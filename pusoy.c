/*
Pusoy Dos program version 1.0

Name:		Paolo Villaflores	
Files:          pusoy.c
                makefile
Code Desc:      This is a UNIX implementation of the card game PUSOY-DOS
                for a single user. The rules as well as the hierarchy of
                plays observed for the traditional PUSOY-DOS are followed.
                Non-standard rules such as hierarchy of suits, number of
                players, number of cards to discard, how control transfers
                can be set by the user. The AI for the computer allows it
                be a competent player/s of the game as well as a checker for
                the correctness of the plays thrown. This PUSOY-DOS uses
                the curses library of functions.

Copyright ca. 1996
All rights reserved.

*/


/* the __USE_BSD macro is for the bzero function */
#include <string.h>
#include <curses.h>
#include <signal.h>
#include <ctype.h>
#include <assert.h>
#include <unistd.h>
#include <time.h>
#include <sys/time.h>
#include <errno.h>
#include <netdb.h>
#include <stdlib.h>
#include <netinet/in.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>

#ifndef A_UNDERLINE	/* BSD curses */
#define	beep()	write(1,"\007",1);
#define	saveterm savetty
#define	resetterm resetty
#define	nocbreak nocrmode
#define strchr	index
#endif /* !A_UNDERLINE */

#ifdef isxdigit		/* aha, must be an AT&T system... */
#define srand(n)	srand48(n)
#define rand()		lrand48()
extern long lrand48();
extern void srand48();
#define bzero(s, n)	(void)memset((char *)(s), '\0', n)
#endif /* isxdigit */

#ifndef ACS_HLINE
#define ACS_HLINE '-'
#define ACS_VLINE '|'
#endif

/* this macro enables the pusoy.log file */
#define DEBUGGING
/* the following macro enables the displaying of opponents cards--for 
debugging 
#define SHOWCARDS */
#define NUMCARDS 52
#define MAXPLAYERS 4

/* the file descriptor for stdin */
#define STDIN 0

/* the following values define the screen size of a card */
#define CARDY 7
#define CARDX 9
/* this value defines the maximum number of connections that may be made to
the server.  this is larger than the maximum number of clients because 
invalid transient connections may exist until the right number of connections
has been verified */
#define MAXCONNECTS 3
static char name[48];
static char progname[128];
static char dfltname[] = "human on this terminal";
char suits[] = "DCHS\0";	/* DIAMONDS, CLUBS, HEARTS, SPADES */
char ranks[] = "3456789TJQKA2";

typedef struct
{
   int send_setting;
   char mes[80];
}
mesgtype;

mesgtype mesgbuffer;

struct DeckStruct
{
    int deck[NUMCARDS];
    int held;
} hand[MAXPLAYERS + 4],  /* 0-3 for players; 4 for discards; 5 for last */
			 /* play; 6&7 for scratch space */
#ifdef DEBUGGING
handdebug[4]		 /* an image of original deck, used for debugging */
#endif
;

#define BACKLOG 5

int numplayers = 4;	/* the number of players in the game */
int discard = 0;	/* the number of cards to discard */
int thisplayer = 0;	/* which hand does this player hold */
int controlmode = 1;    /* how control transfers */
int dispvar = 1;	/* controls whether number of cards is displayed */
int networkgame = 0;	/* controls whether a network game is to be played */
unsigned short int serv_port = 5678;	/* default server port value */
int socketnum, new_fd[MAXCONNECTS], verified[MAXCONNECTS];
int sin_size;
char hostname[60];	/* server hostname */
int send_setting = 4;	/* identifies the target of send commands */

struct sockaddr_in sa;
struct sockaddr_in their_addr; /* connector's address information */
struct hostent *he;
struct {
    int networkgame, numplayers, discard, thisplayer, controlmode, dispvar;
    char name[48];
    int turn, firstdrop, betterthis, pid;
    struct DeckStruct hand;
} messagebuf, messagerec[4];



#ifdef DEBUGGING
FILE *fdbg;		/* log file */
#endif

/* end the game, either normally or due to signal */
static void uninitgame(int sig)
{
#ifdef DEBUGGING
    int i, j;	
#endif

    clear();
    (void)refresh();
    resetty();
    (void)echo();
    (void)endwin();
#ifdef DEBUGGING
    fprintf(fdbg,"DEBUG RECORDS\n");
    fprintf(fdbg, "%d\n", numplayers);
    fprintf(fdbg, "%s\n", suits);
    fprintf(fdbg, "%d\n", controlmode);
    fprintf(fdbg, "%d\n", discard);
    for (i = 0; i < numplayers; i++)
    {
	fprintf(fdbg, "PLAYER RECORD\n");
	fprintf(fdbg, "%d\n", handdebug[i].held);
	for (j = 0; j < handdebug[i].held; j++) fprintf(fdbg, "%d %c%c\n",
	    handdebug[i].deck[j], ranks[handdebug[i].deck[j]/4], 
	    suits[handdebug[i].deck[j]%4]);
    }
    fclose(fdbg);
#endif
    exit(0);
}

static void fatal(char *s)
{
#ifdef DEBUGGING
    int i, j;	
#endif

    clear();
    (void)refresh();
/*    (void)resetterm(); */
    (void)echo();
    (void)endwin();
    (void)fprintf(stderr, "%s:  fatal error:  %s\n", progname, s);
#ifdef DEBUGGING
    fprintf(fdbg,"DEBUG RECORDS\n");
    fprintf(fdbg, "%d\n", numplayers);
    fprintf(fdbg, "%s\n", suits);
    fprintf(fdbg, "%d\n", controlmode);
    fprintf(fdbg, "%d\n", discard);
    for (i = 0; i < numplayers; i++)
    {
	fprintf(fdbg, "PLAYER RECORD\n");
	fprintf(fdbg, "%d\n", handdebug[i].held);
	for (j = 0; j < handdebug[i].held; j++) fprintf(fdbg, "%d %c%c\n",
	    handdebug[i].deck[j], ranks[handdebug[i].deck[j]/4], 
	    suits[handdebug[i].deck[j]%4]);
    }
    fclose(fdbg);
#endif
    exit(0);
}

static int mycompar(const void *a, const void *b)
{
    if (*((int *)a) < *((int *)b)) return -1;
    return *((int *)a) > *((int *)b);
}

static int tlate(int val)
{
    return (val + 8) % NUMCARDS;
}

static int mystrtcompar(const void *a, const void *b)
{
    if (tlate((*((int *)b) & 63)) > 
	tlate((*((int *)a) & 63))) return -1; 
    return tlate((*((int *)b) & 63)) < 
	tlate((*((int *)a) & 63)); 
}

static void sortcard(int i)
{
    qsort((void *)&hand[i].deck[0], (size_t)hand[i].held, 
	(size_t)sizeof(hand[i].deck[0]), mycompar); 
}

static void mvcaddstr(int y, char *s)
{
    char temp[80];

    memset(temp, ' ', strlen(s));
    temp[strlen(s)] = 0;
    (void)mvaddstr(y, (COLS - strlen(s)) / 2, temp);
    (void)mvaddstr(y, (COLS - strlen(s)) / 2, s);
}

static void messageline(char *m)
{
    static char save[80] = "\0";

    if (strcmp(save, m)) 
    {
	wmove(stdscr, 22, 0); clrtoeol(); mvcaddstr(22, save);
	wmove(stdscr, 23, 0); clrtoeol(); mvcaddstr(23, m);
	strcpy(save, m);
	refresh();
    }
}

static void drawcard(int aty, int atx, int crd)
{
    WINDOW *cardw;

    if (!(cardw = newwin(CARDY, CARDX, aty - (crd >> 6), atx)))
	fatal("newwin for cardw failed in drawcard\n");
    crd &= 63;
    box(cardw,ACS_VLINE,ACS_HLINE);
/*  if ((crd / 4) == 9)
    {
	mvwaddstr(cardw,0,0,"10");
        mvwaddstr(cardw,CARDY - 1,CARDX - 2,"10");
        mvwaddch(cardw,0,2,suits[crd % 4]);
    } 
    else 
    { */
    mvwaddch(cardw,0,0,ranks[crd / 4]);
    mvwaddch(cardw,CARDY - 1,CARDX - 1,ranks[crd / 4]);
    mvwaddch(cardw,0,1,suits[crd % 4]);
    switch (crd / 4) 
    {
        case 11:
	    mvwaddch(cardw, CARDY / 2, CARDX / 2, suits[crd % 4]);
	    break;
	case 12:
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2, suits[crd % 4]);
	    break;
	case 0:
	    mvwaddch(cardw, CARDY / 2 , CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2, suits[crd % 4]);
	    break;
	case 1:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    break;
	case 2:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    break;
	case 3:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    break;
	case 4:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    break;
	case 5:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    break;
	case 6:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2, suits[crd % 4]);
	    break;
	case 7:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2, suits[crd % 4]);
	    break;
	case 8:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 - 2, suits[crd % 4]);
	    break;
	case 9:
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 + 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2,     CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 + 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 + 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, CARDX / 2 - 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2,     CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, CARDX / 2 - 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2 - 1, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX / 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, CARDX - 2, suits[crd % 4]);
	    break;
        case 10:
	    mvwaddch(cardw, CARDY / 2 - 2, 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2    , 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2    , 2, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2    , 3, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 1, 4, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 - 2, 5, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 1, 4, suits[crd % 4]);
	    mvwaddch(cardw, CARDY / 2 + 2, 5, suits[crd % 4]);

    }
    overwrite(cardw, stdscr);
    delwin(cardw);
}

static void shuffle()
{
    int i, dist, curply = 0;
    int crdhold[NUMCARDS];

    for (i = 0; i < MAXPLAYERS + 2; i++) hand[i].held = 0;
    for (i = 0; i < NUMCARDS; i++) crdhold[i] = 0;
    for (dist = 0; dist < NUMCARDS - discard; dist++) 
    {
	i = (i + rand()) % NUMCARDS;
	while (crdhold[i]) i = (i + 1) % NUMCARDS;
	crdhold[i] = 1;
	hand[curply].deck[hand[curply].held++] = i;
        curply = (curply + 1) % numplayers;
    }
    for (i = 0; i < numplayers; i++) sortcard(i);
#ifdef DEBUGGING
    for (i = 0; i < 4; i++) handdebug[i] = hand[i];
#endif
}

static int whosfirst()
{
    int i, j, min;

    i = 0;
    min = hand[0].deck[0];
    for (j = 1; j < numplayers; j++)
    {
	if (min > hand[j].deck[0])
	{
	    min = hand[j].deck[0];
	    i = j;
	}
    }
    return i;
}

/* combination of NUM cards to check */		
#define NUM 	13
/* constant needed to get flush value */
#define FLSHCNV 36	
/******* look for flush starts here *******/
static int lookforflush(int who, int betterthis)
{
    int diamonds[NUM];	/* array to hold indices of cards with */ 
    int hearts[NUM];	/* the specified suit */
    int spades[NUM];
    int clubs[NUM];
    int suit, i=0, diamondc=0, heartc=0, spadec=0, clubc=0, cardval=0;

    sortcard(who);
    for (i=0; i<NUM; i++)
    {
	diamonds[i] = -1;
	hearts[i] = -1;
	spades[i] = -1;
	clubs[i] = -1;
    }
    for (i=0; i<hand[who].held; i++)
    {
	suit = hand[who].deck[i] % 4;
	switch (suit)
	{
    	    case 0: clubs[clubc++] = i; break;
    	    case 1: spades[spadec++] = i; break;
    	    case 2: hearts[heartc++] = i; break;   	    
    	    case 3: diamonds[diamondc++] = i; break;
	}
    }
    for (i=4; i<clubc; i++)
    {
    	cardval = hand[who].deck[clubs[i]]/4;
	if (((cardval+=FLSHCNV) > betterthis) && (clubs[i] > 0))
	{
	    if (who != thisplayer)
	    {
	    	hand[who].deck[clubs[0]] |= 128;
	    	hand[who].deck[clubs[1]] |= 128;
	    	hand[who].deck[clubs[2]] |= 128;
	    	hand[who].deck[clubs[3]] |= 128;
	    	hand[who].deck[clubs[i]] |= 128;
	    }
	    return (cardval);
	}
    }
    for (i=4; i<spadec; i++)
    {
    	cardval = hand[who].deck[spades[i]]/4 + 8;
	if (((cardval+=FLSHCNV) > betterthis) && (spades[i] > 0))
	{
	    if (who != thisplayer)
	    {
	    	hand[who].deck[spades[0]] |= 128;
	    	hand[who].deck[spades[1]] |= 128;
	    	hand[who].deck[spades[2]] |= 128;
	    	hand[who].deck[spades[3]] |= 128;
	    	hand[who].deck[spades[i]] |= 128;
	    }
	    return (cardval);
	}
    }
    for (i=4; i<heartc; i++)
    {
    	cardval = hand[who].deck[hearts[i]]/4 + 16;
	if (((cardval+=FLSHCNV) > betterthis) && (hearts[i] > 0))
	{
	    if (who != thisplayer)
	    {
	    	hand[who].deck[hearts[0]] |= 128;
	    	hand[who].deck[hearts[1]] |= 128;
	    	hand[who].deck[hearts[2]] |= 128;
	    	hand[who].deck[hearts[3]] |= 128;
	    	hand[who].deck[hearts[i]] |= 128;
	    }
	    return (cardval);
	}
    }
    for (i=4; i<diamondc; i++)
    {
    	cardval = hand[who].deck[diamonds[i]]/4 + 24;
	if (((cardval+=FLSHCNV) > betterthis) && (diamonds[i] > 0))
	{
	    if (who != thisplayer)
	    {
	    	hand[who].deck[diamonds[0]] |= 128;
	    	hand[who].deck[diamonds[1]] |= 128;
	    	hand[who].deck[diamonds[2]] |= 128;
	    	hand[who].deck[diamonds[3]] |= 128;
	    	hand[who].deck[diamonds[i]] |= 128;
	    }
	    return (cardval);
	}
    }
    return 0;
}
#undef NUM
#undef FLSHCNV

#define NUM	13	/* number of cards to check */
#define STRFLSH	97	/* constant needed to get straight flush value */
#define MARK 	128	/* ORed with card value to mark flush */
static int lookforstraightflush(int who, int betterthis)
{
    int i=0, j=0, k=0, l=0;
    int max=0, index=0;
    int club=0, spade=0, heart=0, diamond=0, min=0;	
    int diffclub=0, diffspade=0, diffheart=0, diffdiamond=0;
    int diamonds[NUM];		/* array to hold cards with */ 
    int hearts[NUM];		/* the specified suit */
    int spades[NUM];
    int clubs[NUM];
    int clubc=0, spadec=0, heartc=0, diamondc=0;	

    qsort((void *)&hand[who].deck[0], (size_t)hand[who].held, 
	(size_t)sizeof(hand[who].deck[0]), mystrtcompar);

    for (i=0; i<hand[who].held; i++)
    {
	switch (hand[who].deck[i]%4)
	{
	    case 0:
		clubs[clubc++]=hand[who].deck[i];
		break; 
	    case 1:
		spades[spadec++]=hand[who].deck[i];
		break;
	    case 2:
		hearts[heartc++]=hand[who].deck[i];
		break;
	    case 3:
		diamonds[diamondc++]=hand[who].deck[i];
		break;
	}
    }
    
    min = tlate(clubs[0])/4;
    for (i=1; i<clubc; i++)
    {
	if ((tlate(clubs[i])/4 - tlate(clubs[i-1])/4) == 1)
	{ 
	    club = clubs[i];
   	    max = tlate(clubs[i])/4;
	    diffclub = max - min; 
	    if ((diffclub >= 4) && ((club/4 + club%4*9 + STRFLSH) 
		> betterthis)) 
	    {    
		if (who == thisplayer)
	    	    return (club/4 + club%4*9 + STRFLSH);
		for (j=0; j<NUM; j++) 
		{		
		    if (club == clubs[j]) 
			index = j;
		}
	        for (k=index; k>=(index-4); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == clubs[k])
		   	hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (club/4 + club%4*9 + STRFLSH);
            }
	}
	else min = tlate(clubs[i])/4;
    }
  
    min = tlate(spades[0])/4;
    for (i=1; i<spadec; i++)
    {
	if ((tlate(spades[i])/4 - tlate(spades[i-1])/4) == 1)
	{ 
	    spade = spades[i]; 
   	    max = tlate(spades[i])/4;
	    diffspade = max - min;		
	    if ((diffspade >= 4) && ((spade/4 + spade%4*9 + STRFLSH) 
		> betterthis)) 
	    {    
		if (who == thisplayer) 
	    	    return (spade/4 + spade%4*9 + STRFLSH);
		for (j=0; j<NUM; j++) 
		{
		    if (spade == spades[j]) 
			index = j;
		}
	        for (k=index; k>=(index-4); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == spades[k])
		   	hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (spade/4 + spade%4*9 + STRFLSH);
            }
	}
	else min = tlate(spades[i])/4;
    }
    
    min = tlate(hearts[0])/4;
    for (i=1; i<heartc; i++)
    {
	if ((tlate(hearts[i])/4 - tlate(hearts[i-1])/4) == 1)
	{ 		
	    heart = hearts[i]; 
   	    max = tlate(hearts[i])/4;
	    diffheart = max - min;		
	    if ((diffheart >= 4) && ((heart/4 + heart%4*9 + STRFLSH) 
		> betterthis))
	    {    
		if (who == thisplayer) 
	    	    return (heart/4 + heart%4*9 + STRFLSH);
		for (j=0; j<NUM; j++) 
		{
		    if (heart == hearts[j]) 
			index = j;
		}
	        for (k=index; k>=(index-4); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == hearts[k])
		   	hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (heart/4 + heart%4*9 + STRFLSH);
            }
	}
	else min = tlate(hearts[i])/4;
    }
    
    min = tlate(diamonds[0])/4;
    for (i=1; i<diamondc; i++)
    {
	if ((tlate(diamonds[i])/4 - tlate(diamonds[i-1])/4) == 1)
	{ 	
	    diamond = diamonds[i]; 
   	    max = tlate(diamonds[i])/4;
	    diffdiamond = max - min;
	    if ((diffdiamond >= 4) && ((diamond/4 + diamond%4*9 + STRFLSH) 
		> betterthis)) 
	    {    
		if (who == thisplayer)
	    	    return (diamond/4 + diamond%4*9 + STRFLSH);
		for (j=0; j<NUM; j++) 
		{
		    if (club == clubs[j]) 
			index = j;
		}
	        for (k=index; k>=(index-4); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == diamonds[k])
		   	hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (diamond/4 + diamond%4*9 + STRFLSH);
            }
	}
	else min = tlate(diamonds[i])/4;
    }
    return 0;
}
#undef NUM
#undef STRFLSH	
#undef MARK 
/******* look for straight flush ends here *******/ 

/******* look for royal flush starts here *******/
#define NUM	13	/* number of cards to check */
#define MARK 	128	/* ORed with card value to mark flush */
static int lookforroyalflush(int who, int betterthis)
{
    int i=0, j=0, k=0, l=0;
    int max=0, index=0;
    int club=0, spade=0, heart=0, diamond=0, min=0;	
    int diffclub=0, diffspade=0, diffheart=0, diffdiamond=0;
    int diamonds[NUM];		/* array to hold cards with */ 
    int hearts[NUM];		/* the specified suit */
    int spades[NUM];
    int clubs[NUM];
    int clubc=0, spadec=0, heartc=0, diamondc=0;	  

    qsort((void *)&hand[who].deck[0], (size_t)hand[who].held, 
	(size_t)sizeof(hand[who].deck[0]), mystrtcompar);

    for (i=0; i<hand[who].held; i++)
    {
	switch (hand[who].deck[i]%4)
	{
	    case 0:
		clubs[clubc++]=hand[who].deck[i];
		break; 
	    case 1:
		spades[spadec++]=hand[who].deck[i];
		break;
	    case 2:
		hearts[heartc++]=hand[who].deck[i];
		break;
	    case 3:
		diamonds[diamondc++]=hand[who].deck[i];
		break;
	}
    }
    
    min = tlate(clubs[0])/4;
    for (i=1; i<clubc; i++)
    {
	if ((tlate(clubs[i])/4 - tlate(clubs[i-1])/4) == 1)
	{ 
	    club = clubs[i];
   	    max = tlate(clubs[i])/4;
	    diffclub = max - min; 
	    if ((diffclub == 3) && (135 > betterthis) && 
		(min == 9) && (tlate(clubs[0])/4 == 0)) 
	    {    
		if (who == thisplayer)
	    	    return (135);
		for (j=0; j<NUM; j++) 
		{		
		    if (club == clubs[j]) 
			index = j;
		}
	        for (k=index; k>=(index-3); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == clubs[k])
		   	    hand[who].deck[l] |= MARK;
			if (hand[who].deck[l] == clubs[0])
			    hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (135);
            }
	}
	else min = tlate(clubs[i])/4;
    }
  
    min = tlate(spades[0])/4;
    for (i=1; i<spadec; i++)
    {
	if ((tlate(spades[i])/4 - tlate(spades[i-1])/4) == 1)
	{ 
	    spade = spades[i]; 
   	    max = tlate(spades[i])/4;
	    diffspade = max - min;		
	    if ((diffspade == 3) && (136 > betterthis) && 
		(min == 9) && (tlate(spades[0])/4 == 0)) 
	    {    
		if (who == thisplayer)
	    	    return (136);
		for (j=0; j<NUM; j++) 
		{		
		    if (spade == spades[j]) 
			index = j;
		}
	        for (k=index; k>=(index-3); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == spades[k])
		   	    hand[who].deck[l] |= MARK;
			if (hand[who].deck[l] == spades[0])
			    hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (136);
            }
	}
	else min = tlate(spades[i])/4;
    }
    
    min = tlate(hearts[0])/4;
    for (i=1; i<heartc; i++)
    {
	if ((tlate(hearts[i])/4 - tlate(hearts[i-1])/4) == 1)
	{ 		
	    heart = hearts[i]; 
   	    max = tlate(hearts[i])/4;
	    diffheart = max - min;		
	    if ((diffheart == 3) && (137 > betterthis) && 
		(min == 9) && (tlate(hearts[0])/4 == 0)) 
	    {    
		if (who == thisplayer)
	    	    return (137);
		for (j=0; j<NUM; j++) 
		{		
		    if (heart == hearts[j]) 
			index = j;
		}
	        for (k=index; k>=(index-3); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == hearts[k])
		   	    hand[who].deck[l] |= MARK;
			if (hand[who].deck[l] == hearts[0])
			    hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (137);
            }
	}
	else min = tlate(hearts[i])/4;
    }
    
    min = tlate(diamonds[0])/4;
    for (i=1; i<diamondc; i++)
    {
	if ((tlate(diamonds[i])/4 - tlate(diamonds[i-1])/4) == 1)
	{ 	
	    diamond = diamonds[i]; 
   	    max = tlate(diamonds[i])/4;
	    diffdiamond = max - min;
	    if ((diffdiamond == 3) && (138 > betterthis) && 
		(min == 9) && (tlate(diamonds[0])/4 == 0)) 
	    {    
		if (who == thisplayer)
	    	    return (138);
		for (j=0; j<NUM; j++) 
		{		
		    if (diamond == diamonds[j]) 
			index = j;
		}
	        for (k=index; k>=(index-3); k--)
	        {
	    	    for (l=0; l<hand[who].held; l++)
	    	    {
		    	if (hand[who].deck[l] == diamonds[k])
		   	    hand[who].deck[l] |= MARK;
			if (hand[who].deck[l] == diamonds[0])
			    hand[who].deck[l] |= MARK;
	    	    }
	    	}
	    	return (138);
            }
	}
	else min = tlate(diamonds[i])/4;
    } 
    return 0;
}
#undef NUM
#undef MARK
/******* look for royal flush ends here *******/ 

#define FOURCNV	86
/******* look for four-of-a-kind starts here *******/
static int lookfor4(int who, int betterthis)
{
    int i, index=0, flag=0, number=0;
    int single=-1, pair=-1, trio=-1, quad=-1;
    int list[13];

    sortcard(who);
    for (i=0; i<13; i++) list[i] = 0;
    for (i=0; i<hand[who].held; i++)
    {
	index = hand[who].deck[i]/4;
	list[index] += 1; 	
    }
    for (i=0; i<13; i++)
    {
	if ((list[i] == 4) && (i > (betterthis-FOURCNV))) 
	{
	    flag = 1;
	    number = i;
	    break;
	}
    }
    if (flag == 1) 
    {
	betterthis = number + FOURCNV;
	if (who != thisplayer)
	{
	    for (i=0; i<hand[who].held; i++)
	    {
	    	if (hand[who].deck[i]/4 == number) 
		    hand[who].deck[i] |= 128;
	    }
	    for (i=0; i<13; i++)
	    {
		switch (list[i])
		{
		    case 1:
			if (single < 0) single = i; 
			break;
		    case 2: 
			if (pair < 0) pair = i; 
			break;
		    case 3: 
			if (trio < 0) trio = i; 
			break;
		    case 4: 
			if (quad < 0) quad = i; 
			break;
		}
  	    }
	    if ((single > 7) && (pair >= 0) && ((single-pair) >= 4))
	    {
	    	for (i=0; i<hand[who].held; i++)
	    	{
	    	    if (hand[who].deck[i]/4 == pair)
		    { 
		    	hand[who].deck[i] |= 128;
		    	return betterthis;
		    }
	    	}
	    }
	    else if (single >= 0)
	    {
	    	for (i=0; i<hand[who].held; i++)
	    	{
	    	    if (hand[who].deck[i]/4 == single) 
		    {
			hand[who].deck[i] |= 128;
		    	return betterthis;
		    }
	    	}
	    }
	    else if (pair >= 0)
	    {
	    	for (i=0; i<hand[who].held; i++)
	    	{
	    	    if (hand[who].deck[i]/4 == pair) 
		    {
			hand[who].deck[i] |= 128;
			return betterthis;
		    }
	    	}
	    }
	    else if (trio >= 0)
	    {
	    	for (i=0; i<hand[who].held; i++)
	    	{
	    	    if (hand[who].deck[i]/4 == trio) 
		    	hand[who].deck[i] |= 128;
		    return betterthis;
	    	}
	    }
	    else if (quad >= 0)
	    {
	    	for (i=0; i<hand[who].held; i++)
	    	{
	    	    if (hand[who].deck[i]/4 == quad) 
		    {
			hand[who].deck[i] |= 128;
		    	return betterthis;
		    }
	    	}
	    }
	}
	return betterthis;
    }
    return 0; 
}
/******* look for four-of-a-kind ends here *******/ 
#undef FOURCNV

#define FULLCNV 73
static int lookforfull(int who, int betterthis)
{
    int LIST[13];
    int trio = -1, duo = -1;
    int i = 0, index = 0, ctr3 = 0, ctr2 = 0;
    int stat3 = 0;
    int stat2 = -1, stat2by3 =-1, stat2by4 = -1;

    sortcard(who);
    for (i = 0; i < 13; i++) LIST[i] = 0;

    for (i=0; i<hand[who].held; i++)
    {
	index = hand[who].deck[i]/4; /* to know card value */
	LIST[index] += 1;
    }
    for (i=0; i<13; i++)
    {
   	if ((LIST[i] == 3) && (i > betterthis-FULLCNV))  
	{
	    trio = i; stat3 = 1; break;
	}
	
    }
    if (stat3==0) 
    {
	for (i=0; i < 13; i++)
	{
	    if ((LIST[i] == 4) && (i > (betterthis-FULLCNV)))
	    {
		trio = i; break;
	    }
	}
    } /* end stat3==0 */
    if (trio < 0) return 0;
    for (i=0; i < 13; i++)
    {
        if ((LIST[i] == 2) && (stat2 < 0)) stat2 = i;
	if ((LIST[i] == 3) && (stat2by3 < 0) && (i != trio)) stat2by3 = i;
	if ((LIST[i] == 4) && (stat2by4 < 0) && (i != trio)) stat2by4 = i;
    }
    if ((stat2 > 7) && (stat2by3 > -1) && (stat2by3 < (stat2-4))) 
	duo = stat2by3;
    else if (stat2 > -1)    duo = stat2;
    else if (stat2by3 > -1) duo = stat2by3;
    else if (stat2by4 > -1) duo = stat2by4;

    if ((trio >= 0) && (duo >= 0)) 
    {
	for (i=0; i < hand[who].held; i++)
	{
    	    if ((trio == (hand[who].deck[i] / 4)) && (ctr3 < 3))
	    {
		hand[who].deck[i] |= 128; ctr3++;
            }
	    if ((duo == (hand[who].deck[i] / 4)) && (ctr2 < 2))
	    {
		hand[who].deck[i] |= 128; ctr2++;
	    }
	}
	return (trio + FULLCNV);	
    }
    return 0;
}
#undef FULLCNV

static int lookforstraight(int who, int betterthis) 
{
    int i, j, k, lowval, prev;
    int marks[5];

    qsort((void *)&hand[who].deck[0], (size_t)hand[who].held, 
	(size_t)sizeof(hand[who].deck[0]), mystrtcompar); 
    for (i = 0; i < 5; i++) marks[i] = 0;
    lowval = prev = hand[who].deck[0];
    i = 1;
    while (i < hand[who].held)
    {
	if ((tlate(hand[who].deck[i])/4 - 1) == (tlate(prev)/4)) 
	{
	    prev = hand[who].deck[i];
	    marks[tlate(prev)/4 - tlate(lowval)/4] = i;
	}
	else if ((tlate(hand[who].deck[i])/4) > (tlate(prev)/4 + 1))
	{
	    lowval = prev = hand[who].deck[i];
	    marks[0] = i;
	}
/*	else
	{
	    wmove(stdscr, 9, 0);
	    printw("%d:%d lowval %d prev %d", tlate(lowval), tlate(prev), lowval, prev);
            for (i = 0; i < hand[who].held; i++) printw("%c%c ",
	        ranks[hand[who].deck[i]/4], suits[hand[who].deck[i]%4]); 
	    refresh(); getch(); fatal("error in lookforstraight");
        }*/
	i++;
        if ((tlate(prev)/4 - tlate(lowval)/4) == 4)
	{
/*	    wmove(stdscr, 7,0);
	    printw("%d %c%c %c%c %d %d", i, ranks[lowval/4], suits[lowval%4], 
	    	ranks[prev/4], suits[prev%4], lowval, prev);
	    refresh();
	    getch();*/
	    if ((tlate(prev) - 15) <= betterthis) 
	    {
		if ((i < hand[who].held) && (tlate(hand[who].deck[i])/4 ==
		    tlate(hand[who].deck[i - 1])/4))
		{
/*	    	    printw("here i %d %d",i,marks[3]);
	    	    refresh();
	    	    getch();*/
		    prev = hand[who].deck[marks[3]];
		}
		else
		{
		    lowval = hand[who].deck[(int)marks[1]];
		    for (j = 0; j < 5; j++) marks[j] = marks[j + 1];
		}
	    }
	    else
	    {
		if (who == thisplayer) return (tlate(prev) - 15);
		for (j = 0; j < 5; j++) hand[who].deck[(int)marks[j]] |= 128;
		return (tlate(prev) - 15);
	    }
	}
    }
    i = 0;
    /* special handler for TJQKA combo */
    while (((prev/4 - lowval/4) == 3) && (hand[who].deck[i]/4 == 11) &&
	(prev / 4 == 10))
    {
        if ((k = (hand[who].deck[i] - 7)) > betterthis)
	{
	    for (j = 0; j < 4; j++) hand[who].deck[(int)marks[j]] |= 128;
	    hand[who].deck[i] |= 128;
	    sortcard(who);
	    return k; 
	}
	i++;
    } 
    return 0;
}

static int isstraightflush(int who)
{
    int i = 0, j = 0, suit = 10;
    int rack[5];

    if (hand[who].held < 5) return 0;
    while ((suit == 10) && (j < hand[who].held))
    {
	if ((who == thisplayer) || (who >= MAXPLAYERS))
	{
	    suit = hand[who].deck[j] % 4;
	    rack[i++] = hand[who].deck[j];
	}
	else if (hand[who].deck[j] & 128)
	{
	    suit = (hand[who].deck[j] & 63) % 4;
	    rack[i++] = hand[who].deck[j] & 63;
	}
	j++;
    }
    if (suit == 10) fatal("isstraightflush called with no card marked");
    while (j < hand[who].held)
    {
	if ((who != thisplayer) && !(hand[who].deck[j] & 128) &&
	    (who < MAXPLAYERS))
	{
	    j++; continue;
	}
	if (((hand[who].deck[j] & 63) % 4) != suit) return 0;
	rack[i++] = hand[who].deck[j] & 63;
	j++;
    }

    qsort((void *)&rack[0], (size_t)5, 
	(size_t)sizeof(rack[0]), mystrtcompar);
    for (j = 0; j < 4; j++)
	if ((tlate(rack[j])/4 + 1) != (tlate(rack[j + 1])/4)) break;

    if (j == 0)	/* handler for TJQKA--royal flush */
    {
	qsort((void *)&rack[0], (size_t)5, 
	    (size_t)sizeof(rack[0]), mycompar);
	for (j = 0; j < 4; j++) if ((rack[j] + 4) != rack[j + 1]) return 0;
	return suit + 135;
    }
    if (j == 4) return (suit * 9) + rack[4]/4 + 97;
    return 0;
}

static int lookfor5(int who, int betterthis)
{
    int i;
    /* better this:
	straight 	1 ... 40
	flush		41 ... 72
	full house 	73 ... 85
	four of a kind	86 ... 98
	straight flush  99 ... 134
	royal flush	135 ... 138 */

    if (hand[who].held < 5) return 0;

    if ((i = lookforstraight(who, betterthis))) return i;
    if ((i = lookforflush(who, betterthis))) return i;
    if ((i = lookforfull(who, betterthis))) return i;
    if ((i = lookfor4(who, betterthis))) return i;
    if ((i = lookforstraightflush(who, betterthis))) return i;
    if ((i = lookforroyalflush(who, betterthis))) return i;
    sortcard(who);
    return 0;
}

static int lookfor3(int who, int betterthis)
{
    int i = 0, rackp = 0, rank = 0;
    int rack[3];

    sortcard(who);
    if (hand[who].held < 3) return 0;
    while (i < hand[who].held)
    {
	if (hand[who].deck[i]/4 == rank)
	{
	    rack[rackp++] = i;
	    if (rackp == 3)
	    {
		if ((rank + 1) > betterthis)
		{
		    for (rackp = 0; rackp < 3; rackp++) 
			hand[who].deck[(int)rack[rackp]] |= 128;
		    return rank + 1;
		}
		else rackp = 0;
	    }
	}
	else 
	{
	    rank = hand[who].deck[i] / 4; rackp = 1; rack[0] = i;
	}
	i++;
    }    
    return 0;
}

static int lookfor2(int who, int betterthis)
{
    int i = 0, rackp = 0, rank = 0;
    int rack[2];

    sortcard(who);
    if (hand[who].held < 2) return 0;
    while (i < hand[who].held)
    {
	if (hand[who].deck[i]/4 == rank)
	{
	    rack[rackp++] = i;
	    if (rackp == 2)
	    {
		/* betterthis val is already that of curr card */
		if (hand[who].deck[i] > betterthis)
		{
		    for (rackp = 0; rackp < 2; rackp++)
			hand[who].deck[(int)rack[rackp]] |= 128;
		    return hand[who].deck[i] & 63;
		}
		else rackp--;
	    }
	}
	else 
	{
	    rank = hand[who].deck[i]/4; rackp = 1; rack[0] = i;
	}
	i++;
    }    
    return 0;
}

static int lookfor1(int who, int betterthis)
{
    int i = 0;

/*  wmove(stdscr, 1,50);
    messageline("debug line in lookfor1");
    getch(); */

    sortcard(who);
    if (hand[who].held == 0) return 0;
    while (i < hand[who].held)
    {
	if (((hand[who].deck[i] & 63) + 1) > betterthis)
	{
	    hand[who].deck[i] |= 128;
	    return (hand[who].deck[i] & 63) + 1;
	}
	i++;
    }    
    return 0;
}

static void dropcard(int *whatcard, int who)
{
    int crd, i;
    
    crd = hand[who].deck[*whatcard] & 63;
    for (i = *whatcard; i < hand[who].held - 1; i++)
    {
	hand[who].deck[i] = hand[who].deck[i + 1];
    }
    if (*whatcard >= --hand[who].held) (*whatcard)--;
    if (!hand[who].held) (*whatcard)++;
    hand[MAXPLAYERS + 1].deck[hand[MAXPLAYERS + 1].held++] = crd;
    hand[MAXPLAYERS].deck[hand[MAXPLAYERS].held++] = crd;    
}

static void dropcard2(int *whatcard, int who)
{
    int crd, i;
    
    crd = hand[who].deck[*whatcard] & 63;
    for (i = *whatcard; i < hand[who].held - 1; i++)
    {
	hand[who].deck[i] = hand[who].deck[i + 1];
    }
    if (*whatcard >= --hand[who].held) (*whatcard)--;
    if (!hand[who].held) (*whatcard)++;
    hand[MAXPLAYERS + 2].deck[hand[MAXPLAYERS + 2].held++] = crd;
}

/* call this when really ready to drop a combo... after validations etc. */
static void dropcombo(int who)
{
    int i;

    hand[MAXPLAYERS + 1].held = 0;
    i = 0;
    while (i < hand[who].held)
    {
	if (hand[who].deck[i] & 128) dropcard(&i, who);
	else i++;
    }
}

static int makechoice(int who, int firstdrop, int betterthis)
{
    int i, stry, sbetter; /* stry and sbetter used when searching for 
	combo that contains the lowest card--for the very first throw */

    if (firstdrop == 2)
    {
	if (betterthis) stry = hand[MAXPLAYERS + 1].held;
	else stry = 5;
	sbetter = betterthis;
	while (stry > 0)
	{
	    do
	    {
		switch (stry)
		{
		    case 5:
			sbetter = lookfor5(who, sbetter);
			break;
		    case 3:
			sbetter = lookfor3(who, sbetter);
			break;
		    case 2:
			sbetter = lookfor2(who, sbetter);
			break;
		    case 1:
			sbetter = lookfor1(who, sbetter);
			break;
		    default:
			fatal("stry set to invalid value in makechoice");
		}
		if (sbetter)
		{
		    for (i = 0; i < hand[who].held; i++) if 
			((unsigned)hand[who].deck[i] == 128) 
			return sbetter;
		    for (i = 0; i < hand[who].held; i++)
			hand[who].deck[i] &= 63;    
		}
	    }
	    while (sbetter > 0);
	    if (--stry == 4) stry--;
	}
	/* the following should only be taken only when makechoice is used
	to validate user's throw and user did not use the lowest three */
	return 0;
    }
    if (firstdrop)
    {
	if (betterthis) stry = hand[MAXPLAYERS + 1].held;
	else stry = 5;
	sbetter = betterthis;
	while (stry > 0)
	{
	    do
	    {
		switch (stry)
		{
		    case 5:
			sbetter = lookfor5(who, sbetter);
			break;
		    case 3:
			sbetter = lookfor3(who, sbetter);
			break;
		    case 2:
			sbetter = lookfor2(who, sbetter);
			break;
		    case 1:
			sbetter = lookfor1(who, sbetter);
			break;
		    default:
			fatal("stry set to invalid value in makechoice");
		}
		if (sbetter) return sbetter;
	    }
	    while (sbetter > 0);
	    if (--stry == 4) stry--;
	}
	fatal("no choice found for first throw.");
    }
    switch (hand[MAXPLAYERS + 1].held)
    {
	case 5:
	    return lookfor5(who, betterthis);
	case 3:
	    return lookfor3(who, betterthis);
	case 2:
	    return lookfor2(who, betterthis);
	case 1:
	    return lookfor1(who, betterthis);
	default:
	    fatal("internal error 2 in makechoice().\n");
    }
    return 0;
}

#ifdef nothing
static void movemark(int who, int from, int to)
{
    int i;
    for (i = 0; i < hand[who].held; i++)
	if ((hand[who].deck[i] & 63) == from) break;
    if (i == hand[who].held) fatal("from not found in movemark");
    if (hand[who].deck[i] & 128) hand[who].deck[i] &= 63;
    else fatal("movemark called on deck entry without mark");

    for (i = 0; i < hand[who].held; i++)
	if ((hand[who].deck[i] & 63) == to) break;
    if (i == hand[who].held) fatal("to not found in movemark");
    if (hand[who].deck[i] & 128) 
	fatal("movemark called for entry with mark");
    else hand[who].deck[i] |= 128;
}

static int checkchoice(int who, int firstdrop, int betterthis)
{
    typedef struct {
	int c
	int crd[4];	/* encodes position in deck */
    } planstruct[13];
    planstruct plan, planbak;
    int i, j, k, l, m, n, choice, heldsave, tryout, conflict, reconcile = 1;
    int straight[13][5], straights; /* essential straights */
    int flush[13][5], flushes; /* essential flushes and strflsh... */
    int savebetter;

    for (i = 0; i < 13; i++)
    {
	plan[i].cnt = 0;
	for (j = 0; j < 4; j++) plan[i].crd[j] = 128;
    }

    for (i = 0; i < hand[who].deck; i++)
    {
	j = hand[who].deck[i];
	plan[j/13].crd[j%4] = i;
    }

    heldsave = hand[MAXPLAYERS + 1].held;
    hand[MAXPLAYERS + 1].held = 5;
    tryout = 0;
    while (tryout = makechoice(who, 0, tryout))	/* inspect 5 card combos */
    {
	/* if (tryout < isstraightflush(who)) continue; */
	/* Do not ignore straight flush/royal flush--treat them as if
	   straight / flush for now */
	conflict = 0; planbak = plan;
	for (i = 0; i < hand[who].held; i++) 
	    if ((hand[who].deck[i] & 128) && (conflict < 8))
	{
	    j = hand[who].deck[i] & 63;
            if (plan[j/13].crd[j%4] & 32)
	    {
		for (k = 0; k < 4; k++) if ((plan[j/13].crd[k] != 128) &&
		    (k != j % 4)) /* look at all cards see if conflict */
		{ 		  /* with a straight may be remedied */
/* remedy by     */ if ((plan[j/13].crd[k] & (32 + 64)) == 0)
/* choosing ano- */ {
/* ther card of  */	plan[j/13].crd[k] |= 32;
/* the same rank */     plan[j/13].crd[j % 4] &= 31;
			movemark(who, j, (j/13)*13 + k);
		    }
		}
		if (k == 4) conflict+=15;
	    }
/* possible improvement:  straight up/down shifting but this may not be
effective since we are scanning for all choices anyway */
		
            if (plan[j/13].crd[j%4] & 64)
	    { /* try to fix conflict with a flush */
		for (k = 0; k < 13; k++) if ((plan[k].crd[j%4] != 128) &&
		(k != (j/13)) && (plan[k].crd[j%4] & (32 + 64)) == 0))
		{
		    plan[k].crd[j % 4] |= 64;
		    plan[k].crd[j % 4] &= 63;
		    movemark(who, j, k*13 + j%4);	
		}
		if (k == 13) conflict+=15;
		else j = k*13 + j % 4;
	    }
	    /*  this way of conflict counting allows us to deduct conflict
		count for claimed areas */
	    for (m = 0; m < 4; m++)
		if ((plan[j/13].crd[m] & 31) && !(plan[j/13].crd[m] & 96))
		    conflict++;
            if (conflict > = 8) plan = planbak;
	}

	if (conflict < 8)	/* if there are few conflicts--only 2 */
	{
	    l = 0;
	    for (i = 0; i < hand[who].held; i++) if (hand[who].deck[i] & 128)
	    {
		j = hand[who].deck[i] & 63;
	        /* is it a striaght */
		if (tryout < 41)
		{
		    straight[straights][l++] = i;
		    plan[j/13].crd[j%4] |= 32;
		    if (l == 5) staaights++;
		}
		else if ((tryout > 40) && (tryout < 73))
		{
		    flush[flushes][l++] = i;
		    plan[j/13].crd[j%4] |= 64;
		    if (l == 5) flushes++;
		}
		else fatal("unhandled 5 card combo passed in checkchoice");
	    }
	}
	for (i = 0; i < hand[who].held; i++) hand[who].deck[i] &= 63;
    }

    if (firstdrop)
    {
	hand[MAXPLAYERS + 1].held = 5; betterthis = 0;
    }
    else hand[MAXPLAYERS + 1].held = heldsave;

    while (betterthis = makechoice(int who, int firstdrop, int betterthis)
    {
	savebetter = betterthis;
	conflict = 1;
	if (betterthis < isstraightflush(who)) continue;
	j = 0;
	for (i = 0; i<hand[who].held; i++) if (hand[who].deck[i] & 128) j++;

/* j */	switch (j)
	{
	    case 5:
		if ((betterthis < 41) || (betterthis > 98))
		{
/* i */		    for (i = 0; i<hand[who].held; i++)
		        if (hand[who].deck[i] & 128)	/* for each card */
		    {
/* m */		    	m = hand[who].deck[i] & 63;
			break;
		    } /* m has first card */
		    for (l = 0; l < straights; l++)
			if (straight[l][0] == (m / 13)) 
		    {
			conflict = 0; break;
		    }
		    if ((!conflict) && (betterthis > 98)) return betterthis;
		    if (!conflict)	/* is the straight essential? */
		    {
		        for (n = 0; n < hand[who].held; n++)
			{
			    if (hand[who].deck[n] & 128) 
				m = hand[who].deck[n] & 63;
			    hand[who].deck[n] &= 63;
			}
			for (n = 0; n < 5; n++)
			{

/* code should now be able to intelligently handle beat condition when
plan dictates otherwise for a straight */
			    i = hand[who].deck[ straight[l][n] ];
			    betterthis = 
				tlate(i) - 15;
			    hand[who].deck[ straight[l][n] ] |= 128;
			
			}
			if (betterthis >= savebetter) return betterthis;
			else
			{
			    if (!(plan[m/13].crd[m%4] & (32 + 64))
				&& (plan[m/13].crd[m%4] == 128))
			    {
				movemark(who, i, m);
				return savebetter;
			    }
			    betterthis = savebetter;
			}
		    }
		} 
		else if (betterthis < 73)
		{
		    conflict = 0; planbak = plan;
		    for (i = 0; i < hand[who].held; i++) 
	    	    if ((hand[who].deck[i] & 128) && (conflict < 8))
		    {
	    j = hand[who].deck[i] & 63;
            if (plan[j/13].crd[j%4] & 32)
	    {
		for (k = 0; k < 4; k++) if ((plan[j/13].crd[k] != 128) &&
		    (k != j % 4)) /* look at all cards see if conflict */
		{ 		  /* with a straight may be remedied */
/* remedy by     */ if ((plan[j/13].crd[k] & (32 + 64)) == 0)
/* choosing ano- */ {
/* ther card of  */	plan[j/13].crd[k] |= 32;
/* the same rank */     plan[j/13].crd[j % 4] &= 31;
			movemark(who, j, (j/13)*13 + k);
		    }
		}
		if (k == 4) conflict+=15;
	    }
/* possible improvement:  straight up/down shifting but this may not be
effective since we are scanning for all choices anyway */
		
            if (plan[j/13].crd[j%4] & 64)
	    { /* try to fix conflict with a flush */
		for (k = 0; k < 13; k++) if ((plan[k].crd[j%4] != 128) &&
		(k != (j/13)) && (plan[k].crd[j%4] & (32 + 64)) == 0))
		{
		    plan[k].crd[j % 4] |= 64;
		    plan[k].crd[j % 4] &= 63;
		    movemark(who, j, k*13 + j%4);	
		}
		if (k == 13) conflict+=15;
		else j = k*13 + j % 4;
	    }
	    /*  this way of conflict counting allows us to deduct conflict
		count for claimed areas */
	    for (m = 0; m < 4; m++)
		if ((plan[j/13].crd[m] & 31) && !(plan[j/13].crd[m] & 96))
		    conflict++;
            if (conflict > = 8) plan = planbak;
	}

	if (conflict < 8)	/* if there are few conflicts--only 2 */
	{
	    l = 0;
	    for (i = 0; i < hand[who].held; i++) if (hand[who].deck[i] & 128)
	    {
		j = hand[who].deck[i] & 63;
	        /* is it a striaght */
		if (tryout < 41)
		{
		    straight[straights][l++] = i;
		    plan[j/13].crd[j%4] |= 32;
		    if (l == 5) staaights++;
		}
		else if ((tryout > 40) && (tryout < 73))
		{
		    flush[flushes][l++] = i;
		    plan[j/13].crd[j%4] |= 64;
		    if (l == 5) flushes++;
		}
		else fatal("unhandled 5 card combo passed in checkchoice");
	    }
	}
	for (i = 0; i < hand[who].held; i++) hand[who].deck[i] &= 63;

		}
	        break;
	    case 4:
		fatal("makechoice returned 4 cards for checkchoice");
	    case 3:
	        break;
	    case 2:
		
	        break;
	    case 1:
	        break;
	}
	for (i = 0; i < hand[who].held; i++) hand[who].deck[i] &= 63;
    }
}
#endif

static int onewon(void)
{
    int i;

    for (i = 0; i < numplayers; i++) if (!hand[i].held) 
    {
	hand[i].held = 60; return i + 1; /* set held to 60 when one wins */
    }
    return 0;
}

static int onehaslost(void)
{
    int i, k = 0;

    for (i = 0; i < numplayers; i++)
	if (hand[i].held != 60) k++;
    return k == 1;
}

static int validate(int firstdrop, int betterthis)
{
    int i, j, k = 0;

    if ((i = makechoice(MAXPLAYERS + 2, firstdrop, betterthis))) 
    {
	if ((j = isstraightflush(MAXPLAYERS + 2))) i = j;
	for (j = 0; j < hand[MAXPLAYERS + 2].held; j++)
	    if (hand[MAXPLAYERS + 2].deck[k] & 128) k++;
	if (k == hand[MAXPLAYERS + 2].held)
	{
	    j = 0;
	    hand[MAXPLAYERS + 1].held = 0;
	    while ((j < hand[MAXPLAYERS + 2].held) && (hand[MAXPLAYERS + 
		2].held)) dropcard(&j, MAXPLAYERS + 2);
	    return i;
	}
    }
    hand[thisplayer] = hand[MAXPLAYERS + 3];
    return 0;
}

static void nextsuitscombi()
{
    int i = 3, j = 3, k; 
    if ((suits[3] < suits[2]) && (suits[2] < suits[1]) && (suits[1] < suits[0]))
    {
	strcpy(suits, "CDHS"); return;
    }
    if (suits[2] < suits[3])
    {
	i = suits[3]; suits[3] = suits[2]; suits[2] = i; return;
    }
    while (suits[i - 1] > suits[i]) i--;
    while (suits[j] < suits[i - 1]) j--;
    k = suits[j]; suits[j] = suits[i - 1]; suits[i - 1] = k;
    qsort(&suits[i], 4 - i, sizeof(suits[0]), mycompar);
}

/* called when a successful combo is found */
static int reportcombo(int j, char *mes, char *whos)
{
    int k;

    switch (hand[MAXPLAYERS + 1].held)
    {
	case 1:
            sprintf(mes, "%s threw a single card (%d).", whos, j);
	    break;
	case 2:
	    sprintf(mes, "%s threw a pair (%d).", whos, j);
	    break;
	case 3:
	    sprintf(mes, "%s threw a trio (%d).", whos, j);
	    break;
	case 5:
	    if (j < 41)
	    {
		if ((k = isstraightflush(MAXPLAYERS + 1)) > 135) sprintf(mes, 
		    "That was just a royal flush (%d)", k);
		else if (k) sprintf(mes, "That was a straight flush (%d)", k);
		else sprintf(mes, "%s threw a straight (%d).", whos, j);
		if (k) j = k;
	    }
	    else if (j < 73)
	    {
		if ((k = isstraightflush(MAXPLAYERS + 1)) > 134) sprintf(mes, 
		    "That was just a royal flush (%d)", k);
		else if (k) sprintf(mes, "That was a straight flush (%d)", k);
		else sprintf(mes, "%s threw a flush (%d).", whos, j);
		if (k) j = k;
	    }
	    else if (j < 86) sprintf(mes, 
		"%s threw a full house (%d).", whos, j);
	    else if (j < 99) sprintf(mes,
		"%s threw a four of a kind (%d).", whos, j);
	    break;
    }
    return j;
}

static void setbit1(int *val, int bit, int set)
{
    if (set) *val |= (1 << bit);
    else *val &= ~(1 << bit);
}

static int askyn(char *s)
{
    int ch;

    messageline(s);
    do
    {
 	beep();
	ch = toupper(getch());
    }
    while ((ch != 'Y') && (ch != 'N'));
    return (ch == 'Y');
}

static void playgame()
{
    int i, j, k, key, choice = 0, cardx = 0, betterthis = 0, lastthrow = 100;
    int redraw = 1, turn, firstdrop = 2, cntrlflag = 0, woncount = 1;
    WINDOW *win;
    char mes[80], mes2[30];
    int wonarray[4];
#ifndef SHOWCARDS
    char *orders[] = {"first", "second", "third", "fourth"};
#endif

    shuffle();

#ifdef DEBUGGING
    fputs("Start of a new game\n", fdbg);
#endif
    turn = whosfirst();

    leaveok(stdscr, FALSE);
    clear();
    for (i = 0; i < hand[thisplayer].held; i++) 
        drawcard(15,i*3,hand[thisplayer].deck[i]);
    do
    {
	
	key = 1;
#ifdef SHOWCARDS
	wmove(stdscr, 9, 0);
	for (j = 1; j < numplayers; j++) if (hand[j].held != 60)
	{
	    printw("%d:",j);
            for (i = 0; i < hand[j].held; i++) printw("%c%c ",
	        ranks[hand[j].deck[i]/4], suits[hand[j].deck[i]%4]); 
            printw("       \n");
        } else printw("         \n");

	wmove(stdscr, 8, 0);printw("lastthrown: ");
            for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) printw("%c%c ",
	        ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
		suits[hand[MAXPLAYERS + 1].deck[i]%4]); 
	refresh();
#else
	wmove(stdscr, 8, 0);
	printw("Keyboard controls:\n");
        printw("  PgUp/PgDn - push a card up/down\n");
	printw("  left/right arrow - move cursor\n");
        printw("  Enter/Spacebar - do chosen action\n");

        /* MARK_1 */

	for (j = 0; j < numplayers; j++)
	{
	    wmove(stdscr, j + 8, 38);
	    if (hand[j].held != 60) 
	    {
		if (dispvar) {
		    if (j == thisplayer) 
		    printw("You have %d card(s)", hand[j].held);
		    else
		    printw("%s has %d card(s)", messagerec[j].name, hand[j].held);

		}
	    }
	    else
	    {
		if (j == thisplayer) 
		printw("You have won %s", orders[wonarray[j] - 1]);
		else
		printw("%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);
	    }
	}
	refresh();

#endif
	if (turn != thisplayer) 
	{
	    if (lastthrow == turn) {
		firstdrop = 1;
		betterthis = 0;
	    }

	    sprintf(mes, "It is now Computer player %d's turn.", turn);
	    messageline(mes);
	    sleep(1);
	    if ((j = makechoice(turn, firstdrop, betterthis)) == 0)
	    {
#ifdef DEBUGGING
		fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    	fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    	fprintf(fdbg, "turn %d\n", turn);
	    	fprintf(fdbg, "betterthis %d\n", betterthis);
	    	fprintf(fdbg, "redraw %d\n", redraw);
	    	fprintf(fdbg, "Computer player %d passed.", turn);
#endif
	    	if (cntrlflag)
	    	{
		    lastthrow = turn;
		    cntrlflag--;
		}
	        sprintf(mes, "Computer player %d will pass.", turn);
 		messageline(mes); sleep(2); 
	    }
	    else
	    {
		dropcombo(turn);
		sprintf(mes2, "Computer player %d", turn);
		betterthis = reportcombo(j, mes, mes2);

#ifdef DEBUGGING
		fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    	fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    	fprintf(fdbg, "turn %d\n", turn);
	    	fprintf(fdbg, "betterthis %d\n", betterthis);
	    	fprintf(fdbg, "redraw %d\n", redraw);
	    	fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    	fprintf(fdbg, "number of thrown cards %d\n", hand[MAXPLAYERS + 1].held);
	    	for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	            fprintf(fdbg, "%d %c%c\n", hand[MAXPLAYERS + 1].deck[i],
	            ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	            suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
	    	if (cntrlflag)
	    	{
		    lastthrow = turn;
		    cntrlflag--;
		}
		lastthrow = turn; firstdrop = 0; messageline(mes);
		redraw = 3;
	    }
    	    while (hand[turn = (turn + 1) % numplayers].held == 60);
	}
	else
	{
	    if (lastthrow == turn) {
		firstdrop = 1; betterthis = 0;
	    }
	    switch(firstdrop)
	    {
		case 0: messageline("It is now your turn."); break;
		case 1: messageline("You are now in control."); break;
		case 2: messageline("You have the first draw."); break;
	    }
            mvaddstr(0, 57, "   throw combo");
            mvaddstr(1, 57, "   throw single");
            mvaddstr(2, 57, "   pass");
            mvaddstr(3, 57, "   quit");
            mvaddstr(4, 57, "   sort by rank");
            wmove(stdscr, 5, 57);
	    printw(	    "   sort by suit (%s)", suits);
    	    mvaddstr(choice, 57, "==>");

            mvaddstr(0, 35, "5 card heirarchy:");
            mvaddstr(1, 35, "  straight");
            mvaddstr(2, 35, "  flush");
            mvaddstr(3, 35, "  full house");
            mvaddstr(4, 35, "  four of a kind");
            mvaddstr(5, 35, "  straight flush");
            mvaddstr(6, 35, "  royal flush");

/*          mvaddstr(0, 35, "5 card heirarchy:");
            mvaddstr(1, 35, "  straight");
            mvaddstr(2, 35, "  flush");
            mvaddstr(3, 35, "  full house");
            mvaddstr(4, 35, "  four of a kind");
            mvaddstr(5, 35, "  straight flush");
            mvaddstr(6, 35, "  royal flush");*/

	    wmove(stdscr, 16, cardx*3);
	    refresh();
            switch (key = getch())
	    {
	    	case ' ':
		case 13:
		    if (choice == 4)
		    {
			for (k = 0; k < hand[turn].held; k++)
			   hand[turn].deck[k] &= 63;
			sortcard(turn); redraw = 1; break;
		    } else if (choice == 5)
		    {
			for (k = 0; k < hand[turn].held; k++)
			{
			    switch ((hand[turn].deck[k] & 63) % 4)
			    {
				case 0:
				    setbit1(&hand[turn].deck[k], 6, 0);
				    setbit1(&hand[turn].deck[k], 7, 0); break;
				case 1:
				    setbit1(&hand[turn].deck[k], 6, 1);
				    setbit1(&hand[turn].deck[k], 7, 0); break;
				case 2:
				    setbit1(&hand[turn].deck[k], 6, 0);
				    setbit1(&hand[turn].deck[k], 7, 1); break;
				case 3:
				    setbit1(&hand[turn].deck[k], 6, 1);
				    setbit1(&hand[turn].deck[k], 7, 1); break;
			    }
			}
			sortcard(turn); redraw = 1; break;
		    } else if (choice == 1)
		    {
			if (firstdrop || (hand[MAXPLAYERS + 1].held == 1)) 
			{
			    if ((((hand[turn].deck[cardx] & 63) + 1) 
				> betterthis) || firstdrop)
			    {
				betterthis = (hand[turn].deck[cardx] & 63)
				    + 1;
			        hand[MAXPLAYERS + 1].held = 0;
		    	    	dropcard(&cardx, thisplayer);

#ifdef DEBUGGING
				fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    			fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    			fprintf(fdbg, "turn %d\n", turn);
	    			fprintf(fdbg, "betterthis %d\n", betterthis);
	    			fprintf(fdbg, "redraw %d\n", redraw);
	    			fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    			fprintf(fdbg, "number of thrown cards %d\n",
				    hand[MAXPLAYERS + 1].held);
	    			for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	        		    fprintf(fdbg, "%d %c%c\n", 
				    hand[MAXPLAYERS + 1].deck[i],
	        		    ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	        		    suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
			    	if (cntrlflag)
			    	{
				    lastthrow = turn;
				    cntrlflag--;
				}
		    	    	messageline("you have dropped a single card");
	             		lastthrow = turn;
			    	firstdrop = 0;
		   		while (hand[turn = (turn + 1) % 
				    numplayers].held == 60);
			    }
			    else messageline("your card is too low");
			}
			else messageline("you may not drop a single card!!!");
		    } 
		    else if (choice == 2) 
		    {
			if (askyn("are you sure you wish to pass (y/n)?"))
			{

#ifdef DEBUGGING
			    fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    		    fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    		    fprintf(fdbg, "turn %d\n", turn);
	    		    fprintf(fdbg, "betterthis %d\n", betterthis);
	    		    fprintf(fdbg, "redraw %d\n", redraw);
	    		    fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    		    fprintf(fdbg, "user has passed.");
#endif
			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
	   		    while (hand[turn = (turn + 1) % 
			       numplayers].held == 60);
			    if (firstdrop == 2) firstdrop--;
		        }
		    }
		    else if (choice == 0)
		    { 
			k = cardx;
			hand[MAXPLAYERS + 2].held = 0;
			hand[MAXPLAYERS + 3] = hand[thisplayer];
		    	i = hand[thisplayer].deck[cardx] >> 6;
		    	j = 0;
		    	while ((j < hand[thisplayer].held) && 
			    (hand[thisplayer].held))
		        {
			    if (i == (hand[thisplayer].deck[j] >> 6))
			    {
		            	dropcard2(&j, thisplayer);
			    	cardx = j;
			    }
			    else j++;
		    	} /* this transfers selected cards to 
			hand[MAXPLAYERS + 2] */
			if ((j = validate(firstdrop, betterthis)))
			{
			    betterthis = reportcombo(j, mes, name);

#ifdef DEBUGGING
			    fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
			    fprintf(fdbg, "lastthrow %d\n", lastthrow);
			    fprintf(fdbg, "turn %d\n", turn);
			    fprintf(fdbg, "betterthis %d\n", betterthis);
			    fprintf(fdbg, "redraw %d\n", redraw);
			    fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    		    fprintf(fdbg, "number of thrown cards %d\n",
				hand[MAXPLAYERS + 1].held);
	    		    for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	        	    fprintf(fdbg, "%d %c%c\n",
				hand[MAXPLAYERS + 1].deck[i],
	        		ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	        		suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
			    messageline(mes);
             		    lastthrow = turn;
			    firstdrop = 0;
			    while (hand[turn = (turn + 1) % 
				numplayers].held == 60);
		        }
			else 
			{
			    cardx = k;
			    messageline("the throw you made is illegal");
			}
		    } 
		    else if (choice == 3)
		    {
			if (askyn("are you sure you wish to quit (y/n)?"))
			{
			    key = 0;
	    messageline("That ends this game.  Press a key to continue.");
			    getch(); messageline("\0"); return;
			}
		    }
		    redraw = 2; sleep(1);
		    break;
	    	case '8':
            	    if (choice > 0) choice--; break;
	    	case '2':
            	    if (choice < 5) choice++; break;
	    	case '4': 
            	    if (cardx > 0) cardx--; break;
	    	case '6':
            	    if (cardx < hand[thisplayer].held - 1) cardx++; break;
		case 27:
	            if ((key = getch()) != 91)
		    {
	    	        ungetc(key, stdin); continue;
		    }                 
        	    switch (key = getch())
		    {
		    	case 53:
                        case 54:
                            if (getch() == 126)
			    {
			    	if (key == 53)
			    	{
				    if (hand[thisplayer].deck[cardx] & 64) 
				    {
				        if (!(hand[thisplayer].deck[cardx] & 128))
 				    	{
					    hand[thisplayer].deck[cardx] |= 128;
					    hand[thisplayer].deck[cardx] &= 191;
					    redraw = 1;
				        }
				    }
				    else 
				    {
				    	hand[thisplayer].deck[cardx] |= 64;
				        redraw = 1;
				    }
			    	}
			        else
			    	{
				    if (hand[thisplayer].deck[cardx] & 64) 
				    {
				    	redraw = 1;
				    	hand[thisplayer].deck[cardx] &= 191;
				    }
				    else 
				    if (hand[thisplayer].deck[cardx] & 128) 
				    {
				    	redraw = 1;
				    	hand[thisplayer].deck[cardx] |= 64;
				    	hand[thisplayer].deck[cardx] &= 127;
				    }
			    	}
			    }
			    else ungetc(key, stdin);

			    break;
	    	    	case 65: 
            	    	    if (choice > 0) choice--; break;
		    	case 66:	
	                    if (choice < 5) choice++; break;
		    	case 68: 
        	    	    if (cardx > 0) cardx--; break;
		    	case 67:
            		    if (cardx < hand[thisplayer].held - 1) cardx++; break;
		    	default:
			    beep(); continue;
		    }
		    break;
		default:
		    beep();
	    }
	}

	if ((redraw == 2) || (redraw == 3))
	{
	    win = newwin(7,25,0,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) 
                drawcard(0,i*3,hand[MAXPLAYERS + 1].deck[i]);
	    if (redraw == 3) 
	    {
		refresh();
		redraw = 0;
		sleep(2); 
	    }
	    else redraw--;
	}
	if (redraw)
	{
	    sortcard(thisplayer);
	    win = newwin(10,80,12,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[thisplayer].held; i++) 
                drawcard(15,i*3,hand[thisplayer].deck[i]);
	    redraw--;
	}

	if ((i = onewon()))
	{
	    wonarray[i-1] = woncount++;

            /* MARK_2 */

	    if ((i - 1) == thisplayer) sprintf(mes, 
		"You have won.  Press any key to continue");
	    else sprintf(mes, 
		"%s has won.  Press a key to continue.", messagerec[j].name);
	    messageline(mes);
	    firstdrop = 1;
	    getch();
	    if (!onehaslost() && controlmode)
	    {
		firstdrop = 0; cntrlflag = 1;
	    } else betterthis = 0;
	}

    } while ((key != 0) && (!onehaslost()));

#ifndef SHOWCARDS
    wmove(stdscr, 8, 0);
    printw("Keyboard controls:\n");
    printw("  PgUp/PgDn - push a card up/down\n");
    printw("  left/right arrow - move cursor\n");
    printw("  Enter/Spacebar - do chosen action\n");
    for (j = 0; j < numplayers; j++)
    {
        wmove(stdscr, j + 8, 38);
	if (hand[j].held != 60) 
	{
	    if (j == thisplayer) 
	    printw("You have lost holding %d card(s)", hand[j].held);
	    else
	    printw("%s has lost with %d card(s)", messagerec[j].name, hand[j].held);
	}
	else
	{
            /* MARK_3 */

	    if (j == thisplayer) 
	    printw("You have won %s", orders[wonarray[j] - 1]);
	    else
	    printw("%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);
	}
    }
    refresh();

#endif
    messageline("That ends this game.");
    getch();
    messageline("\0");
}

static void prerror(char *mes)
{
    char message[200];

    sprintf(message, "%s %s", mes, strerror(errno));
    messageline(message);
}

static void client_send_message()
{

    leaveok(stdscr, FALSE);
    messageline("Message: ");
    messageline("");
    refresh();
    resetterm(); 
    (void)echo(); 
    endwin();
    fgets(mesgbuffer.mes, 60, stdin); 
    if (strlen(mesgbuffer.mes) > 0)
	mesgbuffer.mes[strlen(mesgbuffer.mes) - 1] = 0; 

    initscr();

#ifdef KEY_MIN 
    keypad(stdscr, TRUE);
#endif /* KEY_MIN */
    savetty();
    (void)nonl();
    (void)cbreak();
    (void)noecho();
    mesgbuffer.send_setting = send_setting;

    if (send_setting == 4)
    {
	while (send(socketnum, (void *)&mesgbuffer, 
	    sizeof(mesgbuffer), 0) == -1) prerror("send() failed:");
    } 
    else
    {
	if ((send_setting != thisplayer) && 
	    (send_setting < messagerec[0].networkgame))
        while (send(socketnum, (void *)&mesgbuffer, 
	    sizeof(mesgbuffer), 0) == -1) prerror("send() failed:");
	else
	  messageline("you can't send to yourself or to a non-existent client");
    }

}

static void serv_send_message()
{
    int l;

    leaveok(stdscr, FALSE);
    messageline("Message: ");
    messageline("");
    refresh();
    resetterm(); 
    (void)echo(); 
    endwin();
    fgets((char *) &messagebuf, 60, stdin); 
    if (strlen((char *) &messagebuf) > 0)
	((char *) &messagebuf)[strlen((char *) &messagebuf) - 1] = 0; 

    initscr();

#ifdef KEY_MIN 
    keypad(stdscr, TRUE);
#endif /* KEY_MIN */
    savetty();
    (void)nonl();
    (void)cbreak();
    (void)noecho();

    sprintf(mesgbuffer.mes, "%s: %s", name, (char *)&messagebuf);

    if (send_setting == 4)
    {
	for (l = 0; l < networkgame - 1; l++)
	    while (send(new_fd[l], (void *)&mesgbuffer.mes, 
	    sizeof(mesgbuffer.mes), 0) == -1) prerror("send() failed:");
    } 
    else
    {
	if ((send_setting > 0) && (send_setting < networkgame))
        while (send(new_fd[send_setting - 1], (void *)&mesgbuffer.mes, 
	    sizeof(mesgbuffer.mes), 0) == -1) prerror("send() failed:");
	else
	  messageline("you can't send to yourself or to a non-existent client");
    }
}

static void playgameclient()
{
    int i, j, k, l, key, choice = 0, cardx = 0, betterthis = 0, lastthrow = 
100;
    int redraw = 1, turn, firstdrop = 2, cntrlflag = 0, woncount = 1;
    WINDOW *win;
    char mes[80];
    int wonarray[4];
#ifndef SHOWCARDS
    char *orders[] = {"first", "second", "third", "fourth"};
#endif
    int loopcnt = 0, registers, received;
    int highestfd, numbytes;
    struct timeval tv;
    fd_set readfds;

    hand[MAXPLAYERS].held = 0;
    hand[MAXPLAYERS + 1].held = 0;
    hand[MAXPLAYERS + 2].held = 0;
    hand[MAXPLAYERS + 3].held = 0;

    registers = 0;
    do
    {
	tv.tv_sec = 2;
	tv.tv_usec = 500000;

	highestfd = socketnum;
	FD_ZERO(&readfds);
        FD_SET(socketnum, &readfds);
        FD_SET(STDIN, &readfds);

	/* don't care about writefds and exceptfds: */
        if ((i = select(highestfd + 1, &readfds, NULL, NULL, &tv))  == -1) 
	{
            prerror("select() failed:");
	    FD_ZERO(&readfds);
	} 

	if (FD_ISSET(socketnum, &readfds))
	{
	    if ((numbytes=recv(socketnum, (void *)&messagebuf,
		sizeof(messagebuf), 0)) == -1) 
	    {
        	prerror("recv() failed:");
	    } 
	    else if (numbytes == sizeof(messagebuf)) {
		messagerec[registers] = messagebuf; 
		if (messagebuf.pid == getpid()) 
		    thisplayer = messagebuf.thisplayer;
		hand[registers] = messagebuf.hand;
		sprintf(mes, "Player number %d is %s", registers + 1,
		    messagebuf.name);
		messageline(mes);
		sleep(1);
		registers++;
	    }
	    else if (numbytes)
	    {
		sprintf(mes, "%s", (char *)&messagebuf);
		messageline(mes);
		sleep(2);
	    }
	    else 
	    {
	        sprintf(mes, "The server has rudely closed our connection");
		messageline(mes);
		messageline("That ends this game.");
    		messageline("\0"); close(socketnum); getch(); return;
	    }
	}

	if (FD_ISSET(STDIN, &readfds))
	{
	    getch();
	    messageline("Why are you pressing a key?");
	}

	if (i == 0)
	{
	    switch (rand() % 4 )
	    {
		case 0:
		    messageline("waiting for player info from server"); break;
		case 1:
		    messageline("that server is sure taking long"); break;
		case 2:
		    messageline("i just love waiting don't you?"); break;
		case 3:
		    messageline(
			"that server will come through... i know it."); break;
	    }
	}
    }
    while (registers < numplayers);

    turn = whosfirst();
    send_setting = 4;
    clear();
    for (i = 0; i < hand[thisplayer].held; i++) 
        drawcard(15,i*3,hand[thisplayer].deck[i]);
    refresh();
    messageline("We are now ready to start the game at last.");
    do
    {
	key = 1;
	
#ifdef SHOWCARDS
	wmove(stdscr, 0, 40); printw("bet %d", betterthis);
	wmove(stdscr, 1, 40); printw("turn %d", turn);
	wmove(stdscr, 2, 40); printw("firstdrop %d", firstdrop);
	wmove(stdscr, 3, 40); printw("lastthrow %d", lastthrow);
	
	wmove(stdscr, 9, 0);
	for (j = 0; j < numplayers; j++) if (hand[j].held != 60)
	{
	    printw("%d:",j);
            for (i = 0; i < hand[j].held; i++) printw("%c%c ",
	        ranks[hand[j].deck[i]/4], suits[hand[j].deck[i]%4]); 
            printw("       \n");
        } else printw("         \n");

	wmove(stdscr, 8, 0);printw("lastthrown: ");
            for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) printw("%c%c ",
	        ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
		suits[hand[MAXPLAYERS + 1].deck[i]%4]); 
	refresh();
#else
	wmove(stdscr, 8, 0);
	printw("Keyboard controls:\n");
        printw("  PgUp/PgDn - push a card up/down\n");
	printw("  left/right arrow - move cursor\n");
        printw("  Enter/Spacebar - do chosen action\n");
	for (j = 0; j < numplayers; j++)
	{
	    wmove(stdscr, j + 8, 38);
	    if (hand[j].held != 60) 
	    {
		if (dispvar) {
		    if (j == thisplayer) 
		    printw("You have %d card(s)", hand[j].held);
		    else
		    printw("%s has %d card(s)", 
		        messagerec[j].name, hand[j].held);
		}
	    }
	    else
	    {
		sprintf(mes, "%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);
	    	mvaddstr(j + 8, 38, mes);
		refresh();
	    }
	}
        mvaddstr(0, 35, "5 card heirarchy:");
        mvaddstr(1, 35, "  straight");
        mvaddstr(2, 35, "  flush");
        mvaddstr(3, 35, "  full house");
        mvaddstr(4, 35, "  four of a kind");
        mvaddstr(5, 35, "  straight flush");
        mvaddstr(6, 35, "  royal flush");

	refresh();
#endif
	/*clientpart*/
	if (lastthrow == turn) {
	    firstdrop = 1; betterthis = 0;
	}

	switch(firstdrop)
	{
	    case 0: 
		if (turn == thisplayer) messageline("It is now your turn."); 
		else 
		{
		    sprintf(mes, "It is now %s's turn", messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    case 1: 
		if (turn == thisplayer) messageline("You are now in control.");
		else 
		{
		    sprintf(mes, "%s now has control", messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    case 2: 
		if (turn == thisplayer) 
		    messageline("Your throw will start the game.");
		else 
		{
		    sprintf(mes, "%s will make the first throw",
			messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    default:
		fatal("internal error:  firstdrop set to invalid value");
	}
	if (networkgame == 1) sprintf(mes, "   Client %s", 
		messagerec[thisplayer].name);
	else sprintf(mes, "   Server %s", messagerec[thisplayer].name);
	mvaddstr(8, 57, mes);
	
	mvaddstr(0, 57, "   throw combo");
        mvaddstr(1, 57, "   throw single");
        mvaddstr(2, 57, "   pass");
        mvaddstr(3, 57, "   quit");
        mvaddstr(4, 57, "   sort by rank");
	wmove(stdscr, 6, 57);
	if (send_setting == 4)
	    printw("   broadcast mode");
	else
	    printw("   send to %-10s", messagerec[send_setting].name);
        mvaddstr(7, 57, "   send a message");
        wmove(stdscr, 5, 57);
	printw(	    "   sort by suit (%s)", suits);
    	mvaddstr(choice, 57, "==>");

	leaveok(stdscr, FALSE);
	wmove(stdscr, 16, cardx*3);
	refresh();

	received = 0;
	tv.tv_sec = 1;
	tv.tv_usec = 0;

	highestfd = socketnum;
	FD_ZERO(&readfds);
	FD_SET(STDIN, &readfds);
	FD_SET(socketnum, &readfds);
	if ((i = select(highestfd + 1, &readfds, NULL, NULL, &tv))  == -1)
	{
	    prerror("select() failed:"); FD_ZERO(&readfds);
	}

	if (FD_ISSET(socketnum, &readfds)) {
       	    if ((numbytes=recv(socketnum, (void *)&messagebuf,
		sizeof(messagebuf), 0)) == -1) 
	    {
       	        prerror("recv() failed:");
    	    } 
	    else if (numbytes == sizeof(messagebuf)) 
	    {
		if (messagebuf.thisplayer == turn)
		{
		    hand[turn] = messagebuf.hand;
		    if (messagebuf.betterthis == betterthis)
		    {
		        if (cntrlflag)
    			{
	    		    lastthrow = turn; cntrlflag--;
			}
			if (firstdrop == 2) firstdrop--;
        		sprintf(mes, "%s will pass.", messagebuf.name);
			messageline(mes); sleep(2); 
    		    }
		    else
		    {
			dropcombo(turn);
			betterthis = reportcombo(messagebuf.betterthis,
			    mes, messagebuf.name);

    			if (cntrlflag)
    			{
	    		    lastthrow = turn;
	    		    cntrlflag--;
			}
			lastthrow = turn; firstdrop = 0;
			messageline(mes);
			redraw = 3;
    		    }
    		    while (hand[turn = (turn + 1) % 
			numplayers].held == 60);
		    received = 1;
		}
		else
		{
		    sprintf(mes, "%s", (char *)&messagebuf);
		    messageline(mes);
		}
	    }
	    else if (!numbytes)
	    {
		messageline("the server has closed our connection");
		messageline("That ends this game.");
		getch(); messageline("\0"); close(socketnum); return;
	    }
	    else
	    {
	        sprintf(mes, "%s", (char *)&messagebuf);
		messageline(mes);
	    }
	    loopcnt = 0;
	}

	loopcnt=(loopcnt+1) % 100; 
	if (i == 0)
	{
	    if (turn != thisplayer) switch (rand() % 4)
	    {
		case 0:
		    sprintf(mes, "Why is %s taking so long.", 
			messagerec[turn].name);
		    messageline(mes); break;
		case 1:
		    sprintf(mes, "it must be %s's turn since an eon ago.",
			messagerec[turn].name);
		    messageline(mes); break;
		case 2:
	sprintf(mes, "Just hang on.  %s will make a throw in any minute.",
			messagerec[turn].name);
		    messageline(mes); break;
		case 3:
	sprintf(mes, "Please be patient.  %s is still learning this game.",
			messagerec[turn].name);
		    messageline(mes); break;
	    }
	}

	leaveok(stdscr, FALSE);
	wmove(stdscr, 16, cardx*3);
	refresh();
	if (FD_ISSET(STDIN, &readfds)) switch (key = getch())
	{
	    case ' ':
	    case 13:
		if (choice == 4)
		{
		    for (k = 0; k < hand[thisplayer].held; k++)
			hand[thisplayer].deck[k] &= 63;
		    sortcard(thisplayer); redraw = 1; break;
		} 
		else if (choice == 5)
		{
		    for (k = 0; k < hand[thisplayer].held; k++)
		    {
		        switch ((hand[thisplayer].deck[k] & 63) % 4)
			{
			    case 0:
				setbit1(&hand[thisplayer].deck[k], 6, 0);
				setbit1(&hand[thisplayer].deck[k], 7, 0); break;
			    case 1:
				setbit1(&hand[thisplayer].deck[k], 6, 1);
				setbit1(&hand[thisplayer].deck[k], 7, 0); break;
			    case 2:
				setbit1(&hand[thisplayer].deck[k], 6, 0);
				setbit1(&hand[thisplayer].deck[k], 7, 1); break;
			    case 3:
				setbit1(&hand[thisplayer].deck[k], 6, 1);
				setbit1(&hand[thisplayer].deck[k], 7, 1); break;
			}
		    }
		    sortcard(thisplayer); redraw = 1; break;
		}
		else if (choice == 1)
		{
		    if (turn == thisplayer)
		    {
		    	if (firstdrop || (hand[MAXPLAYERS + 1].held == 1)) 
			{
			    if ((((hand[turn].deck[cardx] & 63) + 1) 
			    > betterthis) || firstdrop)
			    {
				betterthis = (hand[turn].deck[cardx] & 63)
				    + 1;
			        hand[MAXPLAYERS + 1].held = 0;
				messagebuf = messagerec[thisplayer];
				messagebuf.hand = hand[turn];
			        for (l = 0; l < hand[turn].held; l++)
				    messagebuf.hand.deck[l] &= 63;
				messagebuf.hand.deck[cardx] |= 128;
		    	    	dropcard(&cardx, thisplayer);

			        messagebuf.turn = turn;
			        messagebuf.pid = getpid();
			        messagebuf.firstdrop = firstdrop;
				messagebuf.betterthis = betterthis;
				if (send(socketnum, (void *)&messagebuf, 
		    		   sizeof(messagebuf), 0) == -1)
				   prerror("send");

			    	if (cntrlflag)
			    	{
				    lastthrow = turn;
				    cntrlflag--;
				}
		    	    	messageline("you have dropped a single card");
	             		lastthrow = turn;
			    	firstdrop = 0;
		   		while (hand[turn = (turn + 1) % 
				    numplayers].held == 60);
			    }
			    else messageline("your card is too low");
			}
			else messageline("you may not drop a single card!!!");
		    } 
		    else
		    messageline("Be patient.  It is not yet your turn");
		}
		else if (choice == 6)
		{
		    if (send_setting == 4) send_setting = 0;
		    else do
		    {
			send_setting++;
			if ((send_setting < messagerec[0].networkgame)
			    && (send_setting != thisplayer)) break;
		    }
		    while (send_setting < 4);
		    break;
		}
		else if (choice == 7) 
		{
		    client_send_message();
		    redraw = 3;
		}
		else if (choice == 2) 
		{
		    if (turn == thisplayer)
		    {
			if (askyn("are you sure you wish to pass (y/n)?"))
			{
			    messagebuf = messagerec[thisplayer];
			    strcpy(messagebuf.name, name);
			    messagebuf.thisplayer = thisplayer;
			    messagebuf.pid = getpid();
			    messagebuf.turn = turn;
			    messagebuf.firstdrop = firstdrop;
			    messagebuf.betterthis = betterthis;
			    messagebuf.hand = hand[turn];
			    for (l = 0; l < hand[turn].held; l++)
			        messagebuf.hand.deck[l] &= 63;
			    if (send(socketnum, (void *)&messagebuf, 
		    	    	sizeof(messagebuf), 0) == -1) prerror("send");

			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
	   		    while (hand[turn = (turn + 1) % 
			       numplayers].held == 60);
			    if (firstdrop == 2) firstdrop--;
		        }
		    }
		    else 
		    {
			switch (rand() % 4)
			{
			    case 0:
			messageline("I'll ignore the fact that you did that.");
			        break;
			    case 1:
			messageline("You can't pass when it is not your turn.");
			        break;
			    case 2:
messageline("Its good that I've been designed to be tolearnt of mistakes.");
			        break;
			    case 4:
messageline("I'd appreciate it if you'd pass when its your turn.");
			        break;
			}
		    }
		}
		else if (choice == 0)
		{
		    if (turn == thisplayer)
		    {
			k = cardx;
			hand[MAXPLAYERS + 2].held = 0;
			hand[MAXPLAYERS + 3] = hand[thisplayer];
		    	i = hand[thisplayer].deck[cardx] >> 6;
		    	j = 0;

			messagebuf = messagerec[thisplayer];
			messagebuf.pid = getpid();
			messagebuf.turn = turn;
			messagebuf.thisplayer = thisplayer;
			messagebuf.firstdrop = firstdrop;
			messagebuf.hand = hand[turn];
			for (l = 0; l < hand[turn].held; l++)
			    messagebuf.hand.deck[l] &= 63;

			l = j;
		    	while ((j < hand[thisplayer].held) && 
			    (hand[thisplayer].held))
		        {
			    if (i == (hand[thisplayer].deck[j] >> 6))
			    {
				messagebuf.hand.deck[l] |= 128;
		            	dropcard2(&j, thisplayer);
			    	cardx = j;
			    }
			    else j++;
			    l++;
		    	} 
			/* this transfers selected cards to 
			hand[MAXPLAYERS + 2] */
			if ((j = validate(firstdrop, betterthis)))
			{
			    betterthis = reportcombo(j, mes, name);

			    messagebuf.betterthis = betterthis;
			    while (send(socketnum, (void *)&messagebuf, 
		    		sizeof(messagebuf), 0) == -1)
				prerror("send");

			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
			    messageline(mes);
             		    lastthrow = turn;
			    firstdrop = 0;
			    while (hand[turn = (turn + 1) % 
				numplayers].held == 60);
		        }
			else 
			{
			    cardx = k;
			    messageline("the throw you made is illegal");
			}
		    }
		    else messageline("Make a throw on your own turn!");
		}
		else if (choice == 3)
		{
		    if (askyn("are you sure you wish to quit (y/n)?"))
		    {
			key = 0;
	    messageline("That ends this game.  Press a key to continue.");
			close(socketnum); getch(); messageline("\0"); 
			return;
		    }
		}
		redraw = 2;
		sleep(1);
		break;
	    case '8':
                if (choice > 0) choice--; break;
	    case '2':
                if (choice < 7) choice++; break;
	    case '4': 
                if (cardx > 0) cardx--; break;
	    case '6':
                if (cardx < hand[thisplayer].held - 1) cardx++; break;
	    case 27:
	        if ((key = getch()) != 91)
		{
	    	    ungetc(key, stdin); continue;
		}                 
        	switch (key = getch())
		{
		    case 53:
                    case 54:
                   	if (getch() == 126)
			{
			    if (key == 53)
			    {
				if (hand[thisplayer].deck[cardx] & 64) 
				{
				    if (!(hand[thisplayer].deck[cardx] & 128))
 				    {
					hand[thisplayer].deck[cardx] |= 128;
					hand[thisplayer].deck[cardx] &= 191;
					redraw = 1;
				    }
				}
				else 
				{
				    hand[thisplayer].deck[cardx] |= 64;
				    redraw = 1;
				}
			    }
			    else
			    {
				if (hand[thisplayer].deck[cardx] & 64) 
				{
				    redraw = 1;
				    hand[thisplayer].deck[cardx] &= 191;
				}
				else 
				if (hand[thisplayer].deck[cardx] & 128) 
				{
				    redraw = 1;
				    hand[thisplayer].deck[cardx] |= 64;
				    hand[thisplayer].deck[cardx] &= 127;
				}
			    }
			}
			else ungetc(key, stdin);
			break;
	    	    case 65: 
            	        if (choice > 0) choice--; break;
		    case 66:	
	                if (choice < 7) choice++; break;
		    case 68: 
        	        if (cardx > 0) cardx--; break;
		    case 67:
            		if (cardx < hand[thisplayer].held - 1) cardx++; break;
		    default:
			beep(); continue;
		}
		break;
	    default:
		beep();
	}

	if ((redraw == 2) || (redraw == 3))
	{
	    win = newwin(7,25,0,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) 
                drawcard(0,i*3,hand[MAXPLAYERS + 1].deck[i]);
	    if (redraw == 3) 
	    {
		refresh();
		redraw = 0;
		sleep(2); 
	    }
	    else redraw--;
	    refresh();
	}
	if (redraw)
	{
	    sortcard(thisplayer);
	    win = newwin(10,80,12,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[thisplayer].held; i++) 
                drawcard(15,i*3,hand[thisplayer].deck[i]);
	    redraw--;
	    refresh();
	}

	if ((i = onewon()))
	{
	    wonarray[i-1] = woncount++;
	    sprintf(mes, 
"Lucky win for %s.  Press any key to continue", messagerec[i - 1].name);
	    messageline(mes);
	    firstdrop = 1;
	    getch();
	    if (!onehaslost() && controlmode)
	    {
		firstdrop = 0; cntrlflag = 1;
	    } 
	    else betterthis = 0;
	}

    }
    while ((key != 0) && (!onehaslost()));

#ifndef SHOWCARDS
    wmove(stdscr, 8, 0);
    printw("Keyboard controls:\n");
    printw("  PgUp/PgDn - push a card up/down\n");
    printw("  left/right arrow - move cursor\n");
    printw("  Enter/Spacebar - do chosen action\n");
    for (j = 0; j < numplayers; j++)
    {
        wmove(stdscr, j + 8, 38);
	if (hand[j].held != 60) 
	{
	    if (j == thisplayer) 
	    printw("You have lost holding %d card(s)", hand[j].held);
	    else
	    printw("%s has lost with %d card(s)", messagerec[j].name, hand[j].held);
	}
	else
	{
	    if (j == thisplayer) 
	    printw("You have won %s", orders[wonarray[j] - 1]);
	    else
            printw("%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);

	}
    }
    refresh();
#endif

    messageline("That ends this game.");
    close(socketnum);
    getch();
    messageline("\0");
}

static void playgameserv()
{
    int i, j, k, l, key, choice = 0, cardx = 0, betterthis = 0, lastthrow = 100;
    int redraw = 1, turn, firstdrop = 2, cntrlflag = 0, woncount = 1, received;
    WINDOW *win;
    char mes[80];
    int wonarray[4];
#ifndef SHOWCARDS
    char *orders[] = {"first", "second", "third", "fourth"};
#endif

    int loopcnt = 0;
    int highestfd, numbytes;
    struct timeval tv;
    struct fd_set readfds;

    hand[MAXPLAYERS].held = 0;
    hand[MAXPLAYERS + 1].held = 0;
    hand[MAXPLAYERS + 2].held = 0;
    hand[MAXPLAYERS + 3].held = 0;

    shuffle();

#ifdef DEBUGGING
    fputs("Start of a new game\n", fdbg);
#endif

    messageline("Found all clients at last... now proceeding");
    messageline("We shall now start the game"); sleep(2);
    turn = whosfirst();

    messagerec[0].networkgame = networkgame;
    messagerec[0].numplayers = numplayers;
    messagerec[0].discard = discard;
    messagerec[0].controlmode = controlmode;
    messagerec[0].dispvar = dispvar;
    messagerec[0].pid = getpid();
    strcpy(messagerec[0].name, name);
    thisplayer = 0;
    close(socketnum);

    messagerec[0].thisplayer = 0;
    messagerec[0].hand = hand[0];
    messagebuf = messagerec[0];
    for (l = 0; l < (networkgame - 1); l++)
       while (send(new_fd[l], (void *)&messagebuf, 
       sizeof(messagebuf), 0) == -1) prerror("send");
    sprintf(mes, "The first player is you, %s", messagebuf.name);
    messageline(mes); sleep(2);

    for (i = 1; i < networkgame; i++)
    {
	messagerec[i].numplayers = numplayers;
    	messagerec[i].discard = discard;
    	messagerec[i].controlmode = controlmode;
    	messagerec[i].dispvar = dispvar;
        messagerec[i].thisplayer = i;
	messagerec[i].hand = hand[i];
        messagebuf = messagerec[i];
	for (l = 0; l < (networkgame - 1); l++)
           while (send(new_fd[l], (void *)&messagebuf, 
	   sizeof(messagebuf), 0) == -1) prerror("send");
	sprintf(mes, "Client player %d is %s", i, messagebuf.name);
	messageline(mes);
	sleep(2);
    }
    for (i = 0; i < (numplayers - networkgame); i++)
    {
	messagerec[networkgame + i].numplayers = numplayers;
    	messagerec[networkgame + i].discard = discard;
    	messagerec[networkgame + i].controlmode = controlmode;
    	messagerec[networkgame + i].dispvar = dispvar;
	sprintf(mes, "Computer player %d", i+1);
	strcpy(messagerec[networkgame + i].name, mes);
        messagerec[networkgame + i].pid = getpid();
	messagerec[networkgame + i].thisplayer = networkgame + i;
	messagerec[networkgame + i].hand = hand[i + networkgame];
        messagebuf = messagerec[networkgame + i];

	for (l = 0; l < (networkgame - 1); l++)
        while (send(new_fd[l], (void *)&messagebuf, 
	   sizeof(messagebuf), 0) == -1) prerror("send");
	sprintf(mes, "player %d is %s", i + networkgame + 1, messagebuf.name);
	messageline(mes);
	sleep(2);
    }
/*  sprintf(mes, "There are %d computer players", numplayers - networkgame);
    messageline(mes); sleep(2);*/

    leaveok(stdscr, FALSE);
    clear();
    for (i = 0; i < hand[thisplayer].held; i++) 
        drawcard(15,i*3,hand[thisplayer].deck[i]);
    do
    {
	key = 1;

#ifdef SHOWCARDS
	wmove(stdscr, 0, 40); printw("bet %d", betterthis);
	wmove(stdscr, 1, 40); printw("turn %d", turn);
	wmove(stdscr, 2, 40); printw("firstdrop %d", firstdrop);
	wmove(stdscr, 3, 40); printw("lastthrow %d", lastthrow);
	
	wmove(stdscr, 9, 0);
	for (j = 0; j < numplayers; j++) if (hand[j].held != 60)
	{
	    printw("%d:",j);
            for (i = 0; i < hand[j].held; i++) printw("%c%c ",
	        ranks[hand[j].deck[i]/4], suits[hand[j].deck[i]%4]); 
            printw("       \n");
        } else printw("         \n");

	wmove(stdscr, 8, 0);printw("lastthrown: ");
            for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) printw("%c%c ",
	        ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
		suits[hand[MAXPLAYERS + 1].deck[i]%4]); 
	refresh();
#else

	wmove(stdscr, 8, 0);
	printw("Keyboard controls:\n");
        printw("  PgUp/PgDn - push a card up/down\n");
	printw("  left/right arrow - move cursor\n");
        printw("  Enter/Spacebar - do chosen action\n");
	for (j = 0; j < numplayers; j++)
	{
	    wmove(stdscr, j + 8, 38);
	    if (hand[j].held != 60)
	    {
		if (dispvar) {
		    if (j == thisplayer) 
		    printw("You have %d card(s)", hand[j].held);
		    else
		    printw("%s has %d card(s)", messagerec[j].name, hand[j].held);
		}
	    }
	    else
	    {
		sprintf(mes, "%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);
	    	mvaddstr(j + 8, 38, mes);
		refresh();
	    }
	}
        mvaddstr(0, 35, "5 card heirarchy:");
        mvaddstr(1, 35, "  straight");
        mvaddstr(2, 35, "  flush");
        mvaddstr(3, 35, "  full house");
        mvaddstr(4, 35, "  four of a kind");
        mvaddstr(5, 35, "  straight flush");
        mvaddstr(6, 35, "  royal flush");

	refresh();

#endif

	if (lastthrow == turn) {
	   firstdrop = 1; betterthis = 0;
	}

	switch(firstdrop)
	{
	    case 0: 
		if (turn == thisplayer) messageline("It is now your turn."); 
		else 
		{
		    sprintf(mes, "It is now %s's turn", messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    case 1: 
		if (turn == thisplayer) messageline("You are now in control.");
		else 
		{
		    sprintf(mes, "%s has control", messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    case 2: 
		if (turn == thisplayer) 
		    messageline("Your throw will start the game.");
		else 
		{
		    sprintf(mes, "%s will make the first throw",
			messagerec[turn].name);
		    messageline(mes);
		}
		break;
	    default:
		fatal("internal error:  firstdrop set to invalid value");
	}
	if (networkgame == 1) sprintf(mes, "   Client %s", 
		messagerec[thisplayer].name);
	else sprintf(mes, "   Server %s", messagerec[thisplayer].name);
	mvaddstr(8, 57, mes);

	mvaddstr(0, 57, "   throw combo");
        mvaddstr(1, 57, "   throw single");
        mvaddstr(2, 57, "   pass");
        mvaddstr(3, 57, "   quit");
        mvaddstr(4, 57, "   sort by rank");
	wmove(stdscr, 6, 57);
	if (send_setting == 4)
	    printw("   broadcast mode");
	else
	    printw("   send to %-10s", messagerec[send_setting].name);
        mvaddstr(7, 57, "   send a message");
        wmove(stdscr, 5, 57);
	printw(	    "   sort by suit (%s)", suits);
    	mvaddstr(choice, 57, "==>");

	leaveok(stdscr, FALSE);
	wmove(stdscr, 16, cardx*3);
	refresh();

	tv.tv_sec = 1;
	tv.tv_usec = 0;

	received = 0;
	highestfd = new_fd[turn - 2];
	FD_ZERO(&readfds);
	FD_SET(STDIN, &readfds);
	for (i = 0; i < (networkgame - 1); i++)
	{
	    FD_SET(new_fd[i], &readfds);
	    if (new_fd[i] > highestfd) highestfd = new_fd[i];
	}

	if (turn < networkgame)
	{
	    if ((i = select(highestfd + 1, &readfds, NULL, 
	    	NULL, &tv))  == -1)
	    {
   		prerror("select() failed:");
		sleep(2);
		FD_ZERO(&readfds);
	    }
	} 
	
	if (turn >= networkgame)
	{
	    i = 0;
	    sprintf(mes, "It is now %s's turn", messagerec[turn].name);
	    messageline(mes);
	    sleep(1);
	    if ((j = makechoice(turn, firstdrop, betterthis)) == 0)
	    {
#ifdef DEBUGGING
	    	fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    	fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    	fprintf(fdbg, "turn %d\n", turn);
	    	fprintf(fdbg, "betterthis %d\n", betterthis);
	    	fprintf(fdbg, "redraw %d\n", redraw);
	    	fprintf(fdbg, "Computer player %d passed.", turn);
#endif
		messagebuf = messagerec[turn];
		strcpy(messagebuf.name, messagerec[turn].name);
		messagebuf.turn = turn;
		messagebuf.firstdrop = firstdrop;
		messagebuf.betterthis = betterthis;
		messagebuf.hand = hand[turn];
		for (l = 0; l < hand[turn].held; l++)
		    messagebuf.hand.deck[l] &= 63;
		for (l = 0; l < networkgame - 1; l++)
		    if (new_fd[l])
		    while (send(new_fd[l], (void *)&messagebuf, 
			sizeof(messagebuf), 0) == -1)
			prerror("send");
	    	if (cntrlflag)
	    	{
		    lastthrow = turn;
		    cntrlflag--;
		}
	        sprintf(mes, "%s will pass.", messagerec[turn].name);
 		messageline(mes); sleep(2); 
	    }
	    else
	    {
		messagebuf = messagerec[turn];
		messagebuf.hand = hand[turn];
		dropcombo(turn);
		betterthis = reportcombo(j, mes, messagerec[turn].name);

		messagebuf.turn = turn;
		messagebuf.firstdrop = firstdrop;
		messagebuf.betterthis = betterthis;
		for (l = 0; l < networkgame - 1; l++)
		    if (new_fd[l])
		    while (send(new_fd[l], (void *)&messagebuf, 
			sizeof(messagebuf), 0) == -1)
			prerror("send");

#ifdef DEBUGGING
		fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    	fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    	fprintf(fdbg, "turn %d\n", turn);
	    	fprintf(fdbg, "betterthis %d\n", betterthis);
	    	fprintf(fdbg, "redraw %d\n", redraw);
	    	fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    	fprintf(fdbg, "number of thrown cards %d\n", hand[MAXPLAYERS + 1].held);
	    	for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	            fprintf(fdbg, "%d %c%c\n", hand[MAXPLAYERS + 1].deck[i],
	            ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	            suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
	    	if (cntrlflag)
	    	{
		    lastthrow = turn;
		    cntrlflag--;
		}
		lastthrow = turn; firstdrop = 0; messageline(mes);
		redraw = 3;
	    }
    	    while (hand[turn = (turn + 1) % numplayers].held == 60);
	} else { /* major else */

	for (j = 0; j < (networkgame - 1); j++) 
	if (FD_ISSET(new_fd[j], &readfds)) {
	    if (new_fd[j]) if ((numbytes=recv(new_fd[j], (void *)&messagebuf,
	        sizeof(messagebuf), 0)) == -1) 
	    {
                prerror("recv() failed:");
	    }
	    else if (numbytes == sizeof(messagebuf)) 
	    {
		if (messagebuf.thisplayer == turn)
		{
		    for (l = 0; l < networkgame - 1; l++)
			if ((l != j) && (new_fd[l]))
			while (send(new_fd[l], (void *)&messagebuf, 
	    		   sizeof(messagebuf), 0) == -1)
			   prerror("send");

		    hand[turn] = messagebuf.hand;
		    if (messagebuf.betterthis == betterthis)
		    {
#ifdef DEBUGGING
			fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
    	            	fprintf(fdbg, "lastthrow %d\n", lastthrow);
    	            	fprintf(fdbg, "turn %d\n", turn);
    	           	fprintf(fdbg, "betterthis %d\n", betterthis);
    	            	fprintf(fdbg, "redraw %d\n", redraw);
    	            	fprintf(fdbg, "Computer player %d passed.", turn);
#endif
		        if (cntrlflag)
    			{
	    		    lastthrow = turn; cntrlflag--;
			}
			if (firstdrop == 2) firstdrop--;
        		sprintf(mes, "%s will pass.", messagebuf.name);
			messageline(mes); sleep(2); 
    		    }
    		    else
		    {
			dropcombo(turn);
			betterthis = 
			reportcombo(messagebuf.betterthis, mes,
			    messagebuf.name);
#ifdef DEBUGGING
			fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
    			fprintf(fdbg, "lastthrow %d\n", lastthrow);
    			fprintf(fdbg, "turn %d\n", turn);
    			fprintf(fdbg, "betterthis %d\n", betterthis);
    			fprintf(fdbg, "redraw %d\n", redraw);
    			fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
    			fprintf(fdbg, 
		"number of thrown cards %d\n", hand[MAXPLAYERS + 1].held);
    			for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
            		fprintf(fdbg, "%d %c%c\n", 
			    hand[MAXPLAYERS + 1].deck[i],
            		ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
            		suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
    			if (cntrlflag)
    			{
	    		    lastthrow = turn;
	    		    cntrlflag--;
			}
			lastthrow = turn; firstdrop = 0;
			messageline(mes);
			redraw = 3;
    		    }
    		    while (hand[turn = (turn + 1) % 
			numplayers].held == 60);
		    received = 1;
		}
		else
		{
		    sprintf(mes, "illegal attemp to throw by %s",
			messagebuf.name);
		    messageline(mes);
		}
	    }
	    else if (!numbytes)
	    {
		if (hand[j + 1].held == 60)
		{
		    close(new_fd[j]); new_fd[j] = 0;
		    sprintf(mes,
		        "Server:  %s has quit after winning.", 
			messagerec[j].name);
		    messageline(mes);
		    for (l = 0; l < networkgame - 1; l++) if (l != j) 
			while (send(new_fd[l], (void *)mes, 
			sizeof(mes), 0) == -1) prerror("send");
		}
		else 
		{
		    sprintf(mes,
		        "Server:  %s has quit.  Sorry, but that end the game.", 
		   	messagerec[j].name);
		    messageline(mes);
		    for (l = 0; l < networkgame - 1; l++) if (l != j) 
			while (send(new_fd[l], (void *)mes, 
			sizeof(mes), 0) == -1) prerror("send");
		    for (l = 0; l < networkgame - 1; l++)
		        close(new_fd[l]);
		    getch();
		    return;
		}
	    }
	    else 
	    {
		
		sprintf(mes, "%s: %s", messagerec[j + 1].name, 
		    ((mesgtype *)&messagebuf)->mes);
		switch (((mesgtype *)&messagebuf)->send_setting)
		{
		    case 4:
			beep();
			messageline(mes);
		    	for (l = 0; l < networkgame - 1; l++) 
			if ((l != j) && new_fd[l])
		    	while (send(new_fd[l], (void *)mes, 
	    	            sizeof(mes), 0) == -1)
		            prerror("send");
			sleep(2);
			break;
		    case 0:
			beep();
			messageline(mes);
			sleep(2);
			break;
		    default:
			if (new_fd[((mesgtype *)&messagebuf)->send_setting - 1])
		    	while (send(new_fd[
			((mesgtype *)&messagebuf)->send_setting - 1],
			    (void *)mes, sizeof(mes), 0) == -1)
		            prerror("send");
			break;
		}
	    }
	}

/* servpart*/

	loopcnt=(loopcnt+1) % 100; 
	if ((i == 0) && (turn > 0) && (turn < networkgame))
	{
	    switch (rand() % 4 )
	    {
		case 0:
		    sprintf(mes, "%s is sure taking long.", 
			messagerec[turn].name);
		    messageline(mes); break;
		case 1:
		    sprintf(mes, "%s will make a throw yet.", 
			messagerec[turn].name);
		    messageline(mes); break;
		case 2:
		    sprintf(mes, "%s will be with us soon.", 
			messagerec[turn].name);
		    messageline(mes); break;
		case 3:
		    sprintf(mes, "%s is taking quite a while...", 
			messagerec[turn].name);
		    messageline(mes); break;
	    }
	}

	if (FD_ISSET(STDIN, &readfds)) switch (key = getch())
	{
	    case ' ':
	    case 13:
		if (choice == 4)
		{
		    for (k = 0; k < hand[thisplayer].held; k++)
			hand[thisplayer].deck[k] &= 63;
		    sortcard(thisplayer); redraw = 1; break;
		}
		else if (choice == 5)
		{
		    for (k = 0; k < hand[thisplayer].held; k++)
		    {
			switch ((hand[thisplayer].deck[k] & 63) % 4)
			{
			    case 0:
				setbit1(&hand[thisplayer].deck[k], 6, 0);
				setbit1(&hand[thisplayer].deck[k], 7, 0); break;
			    case 1:
				setbit1(&hand[thisplayer].deck[k], 6, 1);
				setbit1(&hand[thisplayer].deck[k], 7, 0); break;
			    case 2:
				setbit1(&hand[thisplayer].deck[k], 6, 0);
				setbit1(&hand[thisplayer].deck[k], 7, 1); break;
			    case 3:
				setbit1(&hand[thisplayer].deck[k], 6, 1);
				setbit1(&hand[thisplayer].deck[k], 7, 1); break;
			}
		    }
		    sortcard(thisplayer); redraw = 1; break;
		} else if (choice == 1)
		{
		    if (turn == thisplayer)
		    {
			if (firstdrop || (hand[MAXPLAYERS + 1].held == 1)) 
			{
			    if ((((hand[turn].deck[cardx] & 63) + 1) 
				> betterthis) || firstdrop)
			    {
				betterthis = (hand[turn].deck[cardx] & 63)
				    + 1;
			        hand[MAXPLAYERS + 1].held = 0;

				messagebuf = messagerec[thisplayer];
				messagebuf.hand = hand[turn];
			        for (l = 0; l < hand[turn].held; l++)
				    messagebuf.hand.deck[l] &= 63;
				messagebuf.hand.deck[cardx] |= 128;
		    	    	dropcard(&cardx, thisplayer);

			        messagebuf.turn = turn;
			        messagebuf.firstdrop = firstdrop;
				messagebuf.betterthis = betterthis;
			    	for (l = 0; l < networkgame - 1; l++)
				while (send(new_fd[l], (void *)&messagebuf, 
		    		   sizeof(messagebuf), 0) == -1)
				   prerror("send");

#ifdef DEBUGGING
				fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    			fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    			fprintf(fdbg, "turn %d\n", turn);
	    			fprintf(fdbg, "betterthis %d\n", betterthis);
	    			fprintf(fdbg, "redraw %d\n", redraw);
	    			fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    			fprintf(fdbg, "number of thrown cards %d\n",
				    hand[MAXPLAYERS + 1].held);
	    			for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	        		    fprintf(fdbg, "%d %c%c\n", 
				    hand[MAXPLAYERS + 1].deck[i],
	        		    ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	        		    suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
			    	if (cntrlflag)
			    	{
				    lastthrow = turn;
				    cntrlflag--;
				}
		    	    	messageline("you have dropped a single card");
	             		lastthrow = turn;
			    	firstdrop = 0;
		   		while (hand[turn = (turn + 1) % 
				    numplayers].held == 60);
			    }
			    else messageline("your card is too low");
			}
			else messageline("you may not drop a single card!!!");
		    }
		    else
		    {
			messageline("Wait for your turn!");
		    }
		} 
		else if (choice == 6)
		{
		    if (send_setting == 4) send_setting = 1;
		    else 
		    do
		    {
			send_setting++;
			if ((send_setting < networkgame) && 
			    (send_setting != thisplayer)) break;
		    }
		    while (send_setting < 4);
		    break;
		}
		else if (choice == 7) 
		{
		    serv_send_message();
		    redraw = 3;
		}
		else if (choice == 2) 
		{
		    if (turn == thisplayer)
		    {
			if (askyn("are you sure you wish to pass (y/n)?"))
			{

#ifdef DEBUGGING
			    fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
	    		    fprintf(fdbg, "lastthrow %d\n", lastthrow);
	    		    fprintf(fdbg, "turn %d\n", turn);
	    		    fprintf(fdbg, "betterthis %d\n", betterthis);
	    		    fprintf(fdbg, "redraw %d\n", redraw);
	    		    fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    		    fprintf(fdbg, "user has passed.");
#endif

			    messagebuf = messagerec[thisplayer];
			    messagebuf.turn = turn;
			    messagebuf.firstdrop = firstdrop;
			    messagebuf.betterthis = betterthis;
			    messagebuf.hand = hand[turn];
			    for (l = 0; l < hand[turn].held; l++)
			        messagebuf.hand.deck[l] &= 63;
			    for (l = 0; l < networkgame - 1; l++)
			        while (send(new_fd[l], (void *)&messagebuf, 
		    	    	    sizeof(messagebuf), 0) == -1)
				    prerror("send");

			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
	   		    while (hand[turn = (turn + 1) % 
			       numplayers].held == 60);
			    if (firstdrop == 2) firstdrop--;
		        }
		    }
		    else
		    {
			switch (rand() % 4)
			{
			    case 0:
			messageline("I'll ignore the fact that you did that.");
			        break;
			    case 1:
			messageline("You can't pass when it is not your turn.");
			        break;
			    case 2:
messageline("Its good that I've been designed to be tolearnt of mistakes.");
			        break;
			    case 4:
messageline("I'd appreciate it if you'd pass when its your turn.");
			        break;
			}
		    }
		}
		else if (choice == 0)
		{
		    if (turn == thisplayer)
		    { 
			k = cardx;
			hand[MAXPLAYERS + 2].held = 0;
			hand[MAXPLAYERS + 3] = hand[thisplayer];
		    	i = hand[thisplayer].deck[cardx] >> 6;
		    	j = 0;

			messagebuf = messagerec[thisplayer];
			messagebuf.turn = turn;
			messagebuf.firstdrop = firstdrop;
			messagebuf.hand = hand[turn];
			for (l = 0; l < hand[turn].held; l++)
			    messagebuf.hand.deck[l] &= 63;

			l = j;
		    	while ((j < hand[thisplayer].held) && 
			    (hand[thisplayer].held))
		        {
			    if (i == (hand[thisplayer].deck[j] >> 6))
			    {
				messagebuf.hand.deck[l] |= 128;
		            	dropcard2(&j, thisplayer);
			    	cardx = j;
			    }
			    else j++;
			    l++;
		    	} /* this transfers selected cards to 
			hand[MAXPLAYERS + 2] */
			if ((j = validate(firstdrop, betterthis)))
			{
			    betterthis = reportcombo(j, mes, name);

			    messagebuf.betterthis = betterthis;
			    for (l = 0; l < networkgame - 1; l++)
			        while (send(new_fd[l], (void *)&messagebuf, 
		    		    sizeof(messagebuf), 0) == -1)
				    prerror("send");

#ifdef DEBUGGING
			    fprintf(fdbg, "\nfirstdrop %d\n", firstdrop);
			    fprintf(fdbg, "lastthrow %d\n", lastthrow);
			    fprintf(fdbg, "turn %d\n", turn);
			    fprintf(fdbg, "betterthis %d\n", betterthis);
			    fprintf(fdbg, "redraw %d\n", redraw);
			    fprintf(fdbg, "cntrlflag %d\n", cntrlflag);
	    		    fprintf(fdbg, "number of thrown cards %d\n",
				hand[MAXPLAYERS + 1].held);
	    		    for (i = 0; i < hand[MAXPLAYERS + 1].held; i++)
	        	    fprintf(fdbg, "%d %c%c\n",
				hand[MAXPLAYERS + 1].deck[i],
	        		ranks[hand[MAXPLAYERS + 1].deck[i]/4], 
	        		suits[hand[MAXPLAYERS + 1].deck[i]%4]);
#endif
			    if (cntrlflag)
			    {
				lastthrow = turn;
				cntrlflag--;
			    }
			    messageline(mes);
             		    lastthrow = turn;
			    firstdrop = 0;
			    while (hand[turn = (turn + 1) % 
				numplayers].held == 60);
		        }
			else 
			{
			    cardx = k;
			    messageline("the throw you made is illegal");
			}
		    }
		    else messageline(
			"No combo throwing is allowed for you at this time.");
		}
		else if (choice == 3) 
		{
		    if (askyn("are you sure you wish to quit (y/n)?"))
		    {
			key = 0;
			messageline("\n			    That ends this game.  Press a key to continue.");
    			for (l = 0; l < networkgame - 1; l++) close(new_fd[l]);
			getch();
			messageline("\0"); 
			return;
		    }
		}
		redraw = 2; sleep(1);
		break;
	    case '8':
            	if (choice > 0) choice--; break;
	    case '2':
                if (choice < 7) choice++; break;
	    case '4': 
                if (cardx > 0) cardx--; break;
	    case '6':
                if (cardx < hand[thisplayer].held - 1) cardx++; break;
	    case 27:
	        if ((key = getch()) != 91)
		{
	    	    ungetc(key, stdin); continue;
		}                 
        	switch (key = getch())
		{
		    case 53:
                    case 54:
                        if (getch() == 126)
			{
			    if (key == 53)
			    {
				if (hand[thisplayer].deck[cardx] & 64) 
				{
				    if (!(hand[thisplayer].deck[cardx] & 128))
 				    {
					hand[thisplayer].deck[cardx] |= 128;
					hand[thisplayer].deck[cardx] &= 191;
					redraw = 1;
				    }
				}
				else 
				{
				    hand[thisplayer].deck[cardx] |= 64;
				    redraw = 1;
				}
			    }
			    else
			    {
				if (hand[thisplayer].deck[cardx] & 64) 
				{
				    redraw = 1;
				    hand[thisplayer].deck[cardx] &= 191;
				}
				else 
				if (hand[thisplayer].deck[cardx] & 128) 
				{
				    redraw = 1;
				    hand[thisplayer].deck[cardx] |= 64;
				    hand[thisplayer].deck[cardx] &= 127;
				}
			    }
			}
			else ungetc(key, stdin);
			break;
	    	    case 65: 
            	        if (choice > 0) choice--; break;
		    case 66:	
	                if (choice < 7) choice++; break;
		    case 68: 
        	        if (cardx > 0) cardx--; break;
		    case 67:
            		if (cardx < hand[thisplayer].held - 1) cardx++; break;
		    default:
			beep(); continue;
		}
		break;
	    default:
		beep();
	}
    	} /* for major else */

	if ((redraw == 2) || (redraw == 3))
	{
	    win = newwin(7,25,0,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[MAXPLAYERS + 1].held; i++) 
                drawcard(0,i*3,hand[MAXPLAYERS + 1].deck[i]);
	    if (redraw == 3) 
	    {
		refresh();
		redraw = 0;
		sleep(2); 
	    }
	    else redraw--;
	}
	if (redraw)
	{
	    sortcard(thisplayer);
	    win = newwin(10,80,12,0);
	    overwrite(win, stdscr);
            delwin(win);
	    for (i = 0; i < hand[thisplayer].held; i++) 
                drawcard(15,i*3,hand[thisplayer].deck[i]);
	    redraw--;
	}

	if ((i = onewon()))
	{
	    wonarray[i - 1] = woncount++;
	    sprintf(mes,
"Lucky win for %s.  Press any key to continue", messagerec[i - 1].name);
	    messageline(mes);
	    firstdrop = 1;
	    getch();
	    if (!onehaslost() && controlmode)
	    {
		firstdrop = 0; cntrlflag = 1;
	    } else betterthis = 0;
	}

    } while ((key != 0) && (!onehaslost()));

#ifndef SHOWCARDS
    wmove(stdscr, 8, 0);
    printw("Keyboard controls:\n");
    printw("  PgUp/PgDn - push a card up/down\n");
    printw("  left/right arrow - move cursor\n");
    printw("  Enter/Spacebar - do chosen action\n");
    for (j = 0; j < numplayers; j++)
    {
        wmove(stdscr, j + 8, 38);
	if (hand[j].held != 60) 
	{
	    if (j == thisplayer) 
	    printw("You have lost holding %d card(s)", hand[j].held);
	    else
	    printw("%s has lost with %d card(s)", messagerec[j].name, hand[j].held);
	}
	else
	{
	    if (j == thisplayer) 
	    printw("You have won %s", orders[wonarray[j] - 1]);
	    else
            printw("%s has won %s", messagerec[j].name, orders[wonarray[j] - 1]);
	}
    }
    refresh();

#endif
    messageline("That ends this game.");
    for (l = 0; l < networkgame - 1; l++) close(new_fd[l]);
    getch();
    messageline("\0");
}

static int checkifagree(int who) 
{
    char mes[80];
    int conflict = 0;

    if (messagerec[who].numplayers != numplayers)
    {
	if (networkgame == 1)
	    sprintf(mes, "The server wants %d players.", 
	    messagerec[who].numplayers);
	else
	    sprintf(mes, "The client %s wants %d players.", 
	    messagerec[who].name, messagerec[who].numplayers);
	messageline(mes); sleep(1); conflict = 1;
    }

    if (messagerec[who].discard != discard)
    {
	if (networkgame == 1)
	    sprintf(mes, "The server wants to discard %d card(s).", 
	    messagerec[who].discard);
	else
	    sprintf(mes, "The client %s wants to discard %d card(s).", 
	    messagerec[who].name, messagerec[who].discard);
	messageline(mes); sleep(1); conflict = 1;
    }

    if (messagerec[who].controlmode != controlmode)
    {
	if (networkgame == 1)
	{
	    if (!messagerec[who].controlmode)
	    sprintf(mes, 
		"The server wants the immediate mode control transfer");
	    else 
	    sprintf(mes, 
		"The server wants allow beating mode of control transfer");
	}
	else
	{
	    if (!messagerec[who].controlmode)
	    sprintf(mes, 
		"The client %s wants the immediate mode control transfer",
		messagerec[who].name);
	    else 
	    sprintf(mes, 
		"The client %s wants allow beating mode of control transfer",
		messagerec[who].name);
	}
	messageline(mes); sleep(1); conflict = 1;
    }

    if (messagerec[who].dispvar != dispvar)
    {
	if (networkgame == 1)
	{
	    if (messagerec[who].dispvar)
	    sprintf(mes, 
		"The server wants displaying of the number of cards held");
	    else 
	    sprintf(mes, 
	    "The server does not want displaying of the number of cards held");
	}
	else
	{
	    if (messagerec[who].dispvar)
	    sprintf(mes, 
		"The client %s wants displaying of the number of cards held", 
		messagerec[who].name);
	    else 
	    sprintf(mes, 
 	   "The client %s does not want displaying of the number of cards held",
		messagerec[who].name);
	}
	messageline(mes); sleep(1); conflict = 1;
    }

    return !conflict;
}

static void initgame() 
{
    int choice = 0, connects, i, j, k, loopcnt = 0, verifies;
    int key, highestfd, numbytes;
    char mes[80];
    struct timeval tv;
    struct fd_set readfds;

    messageline("");
    clear();
    do {
	leaveok(stdscr, TRUE);
    	mvcaddstr(0, 
"**************************** Pusoy Dos Main Menu ***************************");
    	mvcaddstr(2 + 2*choice, 
	"===>                                                            <===");
    	sprintf(mes, "Change number of players:  %d", numplayers);
    	mvcaddstr(2, mes);
    	sprintf(mes, "Change number of cards to discard:  %d", discard);
    	mvcaddstr(4, mes);

	if (!controlmode) mvcaddstr(6,
	    "         how control transfers:  immediate          ");
 	else mvcaddstr(6, 
	    "how control transfers:  give others a beating chance");

	sprintf(mes, "Suit order (least to highest)  : %s", suits);
	mvcaddstr(8, mes);

        if (dispvar)
    	  mvcaddstr(10,    "   Display how many cards each player has    ");
    	else mvcaddstr(10, "Do not display how many cards each player has");

        if (networkgame == 4)
    	  mvcaddstr(12, "Play a network game as dealer (server) and 3 clients");
        else if (networkgame == 3)
    	  mvcaddstr(12, "Play a network game as dealer (server) and 2 clients");
        else if (networkgame == 2)
    	  mvcaddstr(12, "Play a network game as dealer (server) and 1 client ");
        else if (networkgame == 1)
    	  mvcaddstr(12, "  Play a network game as ordinary player (client)   ");
    	else mvcaddstr(12, "Play a standalone game");

	sprintf(mes, "Port address for network game is %d", serv_port);
	mvcaddstr(14, mes);

	sprintf(mes, "Server address (for network game clients): %s", hostname);
	mvcaddstr(16, mes);

    	mvcaddstr(18, "Play");
    	mvcaddstr(20, "Quit"); 
    	refresh();
    	key = getch();
	mvcaddstr(2 + 2*choice, 
	"                                                                    ");
    	switch (key)
        {
	    case ' ':
	    case 13:
		if (choice == 0)
		{
		    numplayers = numplayers % 4 + 1;
		    if (numplayers == 1) numplayers++;
		    switch (numplayers)
		    {
			case 2:
			case 4:
			    discard = 0; break;
			case 3:
			    discard = 1; break;
			default:
			    fatal("illegal number of players set");
		    }
		    if (networkgame > numplayers) networkgame = numplayers;
		} 
		else if (choice == 1)
		{
		    if (key == 13) discard = (discard + 1) % 27;
		    else 
		    {
			if (discard == 0) discard = 26;
			else --discard;
		    }
		    key = 0;
		} 
		else if (choice == 2)
		{
		    controlmode = (controlmode + 1) % 2;
		    key = 0;
		} 
		else if (choice == 3)
		{
		    nextsuitscombi();
		    key = 0;
		}
		else if (choice == 4)
		{
		    dispvar = 1 - dispvar;
		    key = 0;
		}
		else if (choice == 5)
		{
		    networkgame = (networkgame + 1) % (numplayers + 1);
		    key = 0;
		}
		else if (choice == 6)
		{
		    if (key == 13)
		    {
		    	if ((++serv_port) == 32767) serv_port = 0;
		    	key = 0;
		    }
		    else
		    {
		    	if ((--serv_port) == 1024) serv_port = 32767;
		    	key = 0;
		    }
		}
		else if (choice == 7)
		{
		    messageline("Enter server address:");
		    messageline("");
		    refresh();

		    resetty();
		    (void)echo();
		    (void)endwin();
		    fgets(hostname, 60, stdin);
		    if (strlen(hostname) > 0)
			hostname[strlen(hostname) - 1] = 0; 
		    initscr();

#ifdef KEY_MIN 
		    keypad(stdscr, TRUE);
#endif /* KEY_MIN */
		    savetty();
		    (void)nonl();
		    (void)cbreak();
		    (void)noecho();
		    

		    leaveok(stdscr, TRUE);

		    key = 0;
		}
		else break;
		key = 0; break;
	    case '8': 
                if (choice > 0) choice--; break;
	    case '2':	
                if (choice < 9) choice++; break;
	    case 27:
		if ((key = getch()) != 91)
		{
		    ungetc(key, stdin); continue;
		}                 
                switch (key = getch())
		{
		    case 65: 
                        if (choice > 0) choice--; break;
		    case 66:	
	                if (choice < 9) choice++; break;
		    default:
			beep(); continue;
		}
		break;
	    default:
		beep();
	}

	if ((choice == 8) && ((key == ' ') || (key == 13)) && networkgame)
	{
	    if ((socketnum = socket(AF_INET, SOCK_STREAM, 0)) == -1)
	    {
		prerror("socket() failed:"); key = 0;
	    }
	    sprintf(mes, "got a socket num = %d", socketnum);
	    messageline(mes);

	    bzero((char *) &sa, sizeof(sa));

	    if ((networkgame >= 2) && (key))
	    {
		sa.sin_family = AF_INET;
		sa.sin_addr.s_addr = htonl(INADDR_ANY);
		sa.sin_port = htons(serv_port);
		bzero((char *)&(sa.sin_zero), 8);
		if (bind(socketnum, (struct sockaddr *) &sa, sizeof(struct
		    sockaddr)) == -1)
	    	{
		    prerror("bind() failed:"); close(socketnum); key = 0;
	    	}

	        if (key && (listen(socketnum, BACKLOG) == -1)) {
		    prerror("listen() failed:");
		    close(socketnum); key = 0;
        	}

		if (key)
		{
		    sleep(1);
		    messageline(
		    "bind() and listen() succeded now waiting for connections");
		    sleep(1);
		}

		connects = 0; verifies = 0; loopcnt = 0;
		for (k = 0; k < MAXCONNECTS; k++) verified[k] = 0;

		if (key) do 
		{
		    tv.tv_sec = 1;
		    tv.tv_usec = 0;

		    highestfd = socketnum;
		    FD_ZERO(&readfds);
           	    FD_SET(socketnum, &readfds);
           	    FD_SET(STDIN, &readfds);
		    for (i = 0; i < connects; i++)
		    {
			FD_SET(new_fd[i], &readfds);
			if (new_fd[i] > highestfd) highestfd = new_fd[i];
		    }

		    /* don't care about writefds and exceptfds: */
/*		    sprintf(mes, "bef select %d", loopcnt);*/
           	    if (key && ((i = select(highestfd + 1, &readfds, NULL, 
			NULL, &tv))  == -1)) {
        	    	prerror("select() failed:"); 
			FD_ZERO(&readfds);
		    } 
/*		    sprintf(mes, "aft select i is %d %d", i, loopcnt);*/

		    if (FD_ISSET(STDIN, &readfds))
		    {
			getch();
		        messageline(
			    "A key was pressed!  closing all connections");
			close(socketnum);
			for (k = 0; k < connects; k++)
			    close(new_fd[k]);
			key = 0;
		    }
		    if (FD_ISSET(socketnum, &readfds) && 
			(connects == MAXCONNECTS))
		    {
			messageline(
"Someone is attempting to connect but our connect buffer is already full");
			sleep(1);
		    }
		    else if (FD_ISSET(socketnum, &readfds))
		    {
		        sin_size = sizeof(struct sockaddr_in);
		        if (key && ((new_fd[connects] = accept(socketnum, 
			(struct sockaddr *)&their_addr, &sin_size)) == -1)) 
			{
		            prerror(
				"press a key to continue: accept() failed:"); 
			    getch();
       			} else {
			    connects++;
			    sprintf(mes, "Dealer:  got connection from %s",
		    	        inet_ntoa(their_addr.sin_addr));
			    messageline(mes);
			    loopcnt = 0;
            	        }
		    }
		    for (j = 0; j < connects; j++) 
		    if (FD_ISSET(new_fd[j], &readfds)) {
	       		if ((numbytes=recv(new_fd[j], (void *)&messagebuf,
			    sizeof(messagebuf), 0)) == -1) {
        	    	    prerror("recv() failed:");
	    		}
			else if (numbytes == sizeof(messagebuf)) {
			    messagerec[j + 1] = messagebuf; 
			    sprintf(mes, "%s is on connection %d",
				messagebuf.name, j);
			    messageline(mes);

			    messagebuf.pid = getpid();
			    messagebuf.numplayers = numplayers;
			    messagebuf.discard = discard;
			    messagebuf.thisplayer = thisplayer;
			    messagebuf.controlmode = controlmode;
			    messagebuf.dispvar = dispvar;
			    strcpy(messagebuf.name, name);
			    while (send(new_fd[j], (void *)&messagebuf, 
		    		sizeof(messagebuf), 0) == -1) prerror("send");

			    if (checkifagree(j + 1)) 
			    {
				verified[j] = 1;
				verifies++;
			    	sprintf(mes, 
				    "%s's game settings agree with ours",
				    messagerec[j + 1].name);
				messageline(mes);
				sleep(2);
			    }
			    else
			    {
			    	sprintf(mes, 
"%s's game settings do not agree with ours... closing connection",
				    messagerec[j + 1].name);
				messageline(mes);

			        close(new_fd[j]);
			        for (k = j; k < connects - 1; k++)
			        {
				   new_fd[k] = new_fd[k + 1];
				   messagerec[k + 1] = messagerec[k + 2];
			        }
			        connects--;
			    }
			}
			else if (numbytes)
			{
			    sprintf(mes, "Garbage from connection %d", j);
			    messageline(mes);
			}
			else {
			    sprintf(mes, 
				"Connection number %d has chickened out", j);
			    messageline(mes);
			    if (verified[j]) verifies--;
			    close(new_fd[j]);
			    for (k = j; k < connects - 1; k++)
			    {
				new_fd[k] = new_fd[k + 1];
				messagerec[k + 1] = messagerec[k + 2];
				verified[k] = verified[k + 1];
			    }
			    connects--;
			}
			loopcnt = 0;
		    }

		    loopcnt=(loopcnt+1) % 100; 
		    if ((key) && (i == 0))
		    {
			switch (rand() % 4 )
			{
			    case 0:
				messageline("still going ..."); break;
			    case 1:
				messageline(
				"them clients are sure taking long"); break;
			    case 2:
				messageline(
				"i just love waiting don't you?"); break;
			    case 3:
				messageline(
				"they'll be here... i know it."); break;
			}
		    }
		} while ((verifies < (networkgame - 1)) && key);
	    }
	    else if (key && networkgame)
	    {
		if ((he=gethostbyname(hostname)) == NULL) {
		    prerror("gethostbyname() failed:");
            	    key = 0; close(socketnum);
        	}

		if (key)
		{
		    their_addr.sin_family = AF_INET;
		    their_addr.sin_port = htons(serv_port);
	            their_addr.sin_addr = *((struct in_addr *)he->h_addr);
         	    bzero((char *)&(their_addr.sin_zero), 8);
		}

		if (key && (connect(socketnum, (struct sockaddr *)&their_addr,
                    sizeof(struct sockaddr)) == -1)) {
		    prerror("connect() failed:");
            	    close(socketnum); key = 0;
        	}

		messagebuf.numplayers = numplayers;
		messagebuf.discard = discard;
		messagebuf.controlmode = controlmode;
		messagebuf.dispvar = dispvar;
		messagebuf.pid = getpid();
		strcpy(messagebuf.name, name);
		while (key && (send(socketnum, (void *)&messagebuf, 
		    sizeof(messagebuf), 0) == -1)) prerror("send() failed:");
	
		loopcnt = 0; verifies = 0; i = 0;
		if (key) do
		{
		    tv.tv_sec = 1;
		    tv.tv_usec = 0;

		    highestfd = socketnum;
		    FD_ZERO(&readfds);
           	    FD_SET(socketnum, &readfds);
           	    FD_SET(STDIN, &readfds);

		    /* don't care about writefds and exceptfds: */
           	    if (key && ((i = select(highestfd + 1, &readfds, NULL, 
			NULL, &tv))  == -1)) {
        	    	prerror("select() failed:");
			key = 0;
			close(socketnum);
		    } 

		    if (FD_ISSET(socketnum, &readfds))
		    {
			if ((numbytes=recv(socketnum, (void *)&messagebuf,
			    sizeof(messagebuf), 0)) == -1) 
			{
        	    	    prerror("press a key to continue:  recv() failed:");
            	    	    getch(); close(socketnum); key = 0;
	    		}
			if (numbytes == sizeof(messagebuf)) {
			    messagerec[0] = messagebuf; 
			    sprintf(mes, "The server is run by %s",
				messagebuf.name);
			    messageline(mes);
			    if (checkifagree(0)) 
			    {
			    	sprintf(mes, 
				    "%s's game settings agree with ours",
				    messagebuf.name);
				messageline(mes);
				sleep(2); verifies++;
			    }
			    else
			    {
			    	sprintf(mes, 
"%s's game settings do not agree with ours... closing connection",
				    messagebuf.name);
				messageline(mes);

			        close(socketnum);
				key = 0;
			    }
			}
			else if (numbytes)
			{
			    sprintf(mes, 
"Garbage received from the server.  Must be a fake.  disconnecting...");
			    messageline(mes);
			    close(socketnum);
			    key = 0;
			}
			else {
			    sprintf(mes, 
			    "The server has rudely closed our connection");
			    messageline(mes);
			    close(socketnum);
			    key = 0;
			}
			loopcnt = 0;
		    }
		    if (FD_ISSET(STDIN, &readfds))
		    {
			getch();
		        messageline(
			    "A key was pressed!  closing connection.");
			close(socketnum);
			key = 0;
		    }

		    loopcnt=(loopcnt+1) % 100; 
		    if ((key) && (i == 0))
		    {
			switch (rand() % 4 )
			{
			    case 0:
				messageline("still going ..."); break;
			    case 1:
				messageline(
				"that server is sure taking long"); break;
			    case 2:
				messageline(
				"i just love waiting don't you?"); break;
			    case 3:
				messageline(
			"that server will come through... i know it."); break;
			}
		    }
		} while (key && !verifies);
	    }
	}

    } while ((key != ' ') && (key != 13));
    
    messageline("");
    if ((choice == 8) && !networkgame) playgame();
    else if ((choice == 8) && (networkgame >= 2)) playgameserv();
    else if ((choice == 8) && (networkgame == 1)) playgameclient();
    else uninitgame(0);
}

static void intro()
{
    char *tmpname;
    int i;

    srand(time(0L) + getpid());	/* Kick the random number generator */

    (void) signal(SIGINT,uninitgame);
    (void) signal(SIGINT,uninitgame);
    (void) signal(SIGIOT,uninitgame);		/* for assert(3) */
    if (signal(SIGQUIT,SIG_IGN) != SIG_IGN)
	(void)signal(SIGQUIT,uninitgame);

    if ((tmpname = getlogin()))
    {
	(void)strcpy(name,tmpname);
	name[0] = toupper(name[0]);
    }
    else (void)strcpy(name,dfltname);

    (void)initscr();
#ifdef KEY_MIN 
    keypad(stdscr, TRUE);
#endif /* KEY_MIN */
    savetty();
    (void)nonl();
    (void)cbreak();
    (void)noecho();

    (void)clear();
    for (i = 0; i < 8; i++) drawcard(i + 8, i*10, rand() % NUMCARDS);

    mvcaddstr(4,"Welcome to Pusoy Dos--the Network Version!");
    mvcaddstr(6,"by paolo");
    (void)move(8,0);

    mvcaddstr(22,"Hit any key to continue..."); (void)refresh();
    (void) getch();
}		    

/* handle options on command line */
static void do_options(int c, char *op[])
{
    register int i;

    strcpy(progname, op[0]);
    if (c > 1)
    {
        for (i=1; i<c; i++) 
        {
            switch(op[i][0])
            {
                default:
	        case '?':
	  	    (void) fprintf(stderr, "Usage is simply:  %s\n", op[0]);
	  	    exit(1);
  	  	    break;
/*      	case '-':
	  	    switch(op[i][1])
	  	    {
	    		case 'b': break;
	    		case 's': break;
	    		case 'c': break;
	    		default:
              		    (void) fprintf(stderr,
				"Bad arg: type \"%s ?\" for usage message\n", op[0]);
	      		    exit(1);
          	    } */
      	    }
        }
    }
}

int main(int argc, char *argv[]) {

    if (gethostname(hostname, sizeof(hostname)) == -1)
    {
	fprintf(stderr, "gethostname() failed... using default host");
	strcpy(hostname, "balut.admu.edu.ph");
    }
    do_options(argc, argv);

#ifdef DEBUGGING
    if ((fdbg = fopen("pusoy.log", "wt+")) == NULL) 
    {
        fputs("failed to create log file.\n", stderr);
    	if ((fdbg = fopen("/dev/null", "wt+")) == NULL)
	{
	   fputs("failed to create log file and null device.\n", stderr);
	   exit(1);
	}
    }
    fputs("\n\nStart of new log\n", fdbg);
#endif
    intro();
    do {
	initgame();
    } while (1);
    uninitgame(0);
    exit(0);
}
/* pusoy.c ends here */

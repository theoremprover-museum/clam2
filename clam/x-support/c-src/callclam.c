/*
 * @(#)$Id: callclam.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: callclam.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

/*****************************************************************************
 *
 *  xdbx - X Window System interface to the dbx debugger
 *
 *  Copyright 1989 The University of Texas at Austin
 *  Copyright 1990 Microelectronics and Computer Technology Corporation
 *
 *  Permission to use, copy, modify, and distribute this software and its
 *  documentation for any purpose and without fee is hereby granted,
 *  provided that the above copyright notice appear in all copies and that
 *  both that copyright notice and this permission notice appear in
 *  supporting documentation, and that the name of The University of Texas
 *  and Microelectronics and Computer Technology Corporation (MCC) not be 
 *  used in advertising or publicity pertaining to distribution of
 *  the software without specific, written prior permission.  The
 *  University of Texas and MCC makes no representations about the 
 *  suitability of this software for any purpose.  It is provided "as is" 
 *  without express or implied warranty.
 *
 *  THE UNIVERSITY OF TEXAS AND MCC DISCLAIMS ALL WARRANTIES WITH REGARD TO
 *  THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
 *  FITNESS, IN NO EVENT SHALL THE UNIVERSITY OF TEXAS OR MCC BE LIABLE FOR
 *  ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER
 *  RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF
 *  CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 *  CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *  Author:  	Po Cheung
 *  Created:   	March 10, 1989
 *
 *****************************************************************************/

/*  calldbx.c
 *
 *    Set up communication between dbx and xdbx using pseudo terminal, and
 *    call dbx.
 *
 *    open_master():	Open the master side of pty.
 *    open_slave(): 	Open the slave side of pty.
 *    calldbx(): 	Invoke dbx.
 */

#include	<termio.h>
#include	<fcntl.h>
#include	"global.h"

FILE   	    	*dbxfp = NULL;		/* file pointer to dbx */
int    	    	dbxpid = 0;		/* dbx process id */

static int	dbxInputId;		/* dbx input id */
static char 	pty[11] = "/dev/pty??";	/* master side of pseudo-terminal */
static char 	tty[11] = "/dev/tty??";	/* slave side of pseudo-terminal */
extern char	*dbxprompt;

/*
 *  Xdbx talks to dbx through a pseudo terminal which is a pair of master
 *  and slave devices: /dev/pty?? and /dev/tty??, where ?? goes from p0 to
 *  sf (system dependent).  The pty is opened for both read and write.
 */
static int open_master()
{
    int  i, master; 
    char c;

    for (c='p'; c<='s'; c++) {
	pty[8] = c;
	for (i=0; i<16; i++) {
	    pty[9] = "0123456789abcdef"[i];
	    if ((master = open(pty, O_RDWR)) != -1) 
		return (master); 
	}
    }
    fprintf(stderr, "xdbx: all ptys in use\n");
    exit(1);
}

static int open_slave()
{
    int slave;

    tty[8] = pty[8];
    tty[9] = pty[9];
    if ((slave = open(tty, O_RDWR)) != -1)
	return (slave);
    fprintf(stderr, "open: cannot open slave pty %s", tty);
    exit(1);
}

/* ARGSUSED */
void callclam(argc, argv)
int argc;
char *argv[];
{
    struct termio Termio;
    int  	  master;		/* file descriptor of master pty */
    int  	  slave; 		/* file descriptor of slave pty */
    int		  fd; 			/* file descriptor of controlling tty */
    int		  pid;			/* process id */
    int		  pgrp;			/* process group id */
    char 	  *debugger = NULL; 		/* name of executable debugger */
    char	  errmsg[50];

   debugger = (char *) getenv("XCLAM_EXEC");  /* first looks up env var */
    if (debugger == NULL)
	debugger = XtNewString(PROLOG);
  
    /* construct dbx prompt string based on the name of debugger invoked */
/*    if (dbxprompt == NULL) {
	dbxprompt = XtMalloc((4+strlen(debugger)) * sizeof(char));
	sprintf(dbxprompt, "(%s) ", debugger);
    }
 */
 
    /*
     * Clear controlling tty.  Do this now, so that open_slave and
     * open_master will cause the selected pty to become the
     * controlling tty.
     */
    if ((fd = open("/dev/tty", O_RDWR)) > 0) {
	ioctl(fd, TIOCNOTTY, 0);
	close(fd);
    }

    master = open_master();
    slave = open_slave();

    dbxpid = fork();
    if (dbxpid == -1) {
	perror("xdbx error: cannot fork process");
	exit(1);
    }
    else if (dbxpid) { 
	/* 
	 * Parent : close the slave side of pty
	 *	    close stdin and stdout
	 *	    set the dbx file descriptor to nonblocking mode
	 *	    open file pointer with read/write access to dbx
	 *	    set line buffered mode
	 *	    register dbx input with X
	 */
	close(slave);
	close(0);
	close(1);
	fcntl(master, F_SETFL, FNDELAY);
    	dbxfp = fdopen(master, "r+");
	setlinebuf(dbxfp);
	dbxInputId = XtAppAddInput(app_context, master, XtInputReadMask, read_clam, NULL);
    }
    else { 
	/* 
	 * Child : close master side of pty
	 * 	   redirect stdin, stdout, stderr of dbx to pty
	 *	   unbuffer output data from dbx
	 *	   exec dbx with arguments
	 */
	close(master);

	/*
	 * Modify local and output mode of slave pty
	 */
	ioctl(slave, TCGETA, &Termio);
	Termio.c_lflag &= ~ECHO;	/* No echo */
	Termio.c_oflag &= ~ONLCR;	/* Do not map NL to CR-NL on output */
	ioctl(slave, TCSETA, &Termio);

	dup2(slave, 0);
	dup2(slave, 1);
	dup2(slave, 2);
	if (slave > 2)
	    close(slave);
	fcntl(1, F_SETFL, FAPPEND);
	setbuf(stdout, NULL);

	/*
	 * Set our process group to that of the terminal,
	 * so we can change the group of the terminal.
	 */
	ioctl(0, TIOCGPGRP, &pgrp);
	setpgrp(0, pgrp);

	/*
	 * Now set the process group of the terminal and of us
	 * to our process id.  This clears us from the control
	 * of the other process group.
	 */
	pid = getpid();
	ioctl(0, TIOCSPGRP, &pid);
	setpgrp(0, pid);

	argv[0] = debugger;
	execvp(debugger, argv);
	sprintf(errmsg, "xdbx error: cannot exec %s", debugger);
	perror(errmsg);
	exit(1);
    }
}

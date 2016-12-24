/*
 * @(#)$Id: defs.h,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: defs.h,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include <X11/IntrinsicP.h>
#include <X11/Xaw/AsciiText.h>
#include <X11/Xaw/TextP.h>
#define CLAM "clam"

#define PROLOG "/usr/local/bin/xclam.swi"

#define LINESIZE 20
#define xclamprompt  "Xclam|?- "
#define prologprompt "| ?- "
#define streq(a, b)        ( strcmp((a), (b)) == 0 )
#define DIALOGSIZE 100000



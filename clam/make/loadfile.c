/*
 * @(#)$Id: loadfile.c,v 1.1 1994/09/16 09:44:06 dream Exp $
 *
 * $Log: loadfile.c,v $
 * Revision 1.1  1994/09/16 09:44:06  dream
 * Initial revision
 *
 */

#include <stdio.h>
main(argc, argv)
     int argc;
     char *argv[];
{
  int i;
  for( i = 1 ; i < argc ; ++i ) 
    {
      if( i+1 < argc )
	printf( "'%s',\n", argv[i] );
      else
	printf( "'%s'\n", argv[i] );
    }
  exit(0);
}


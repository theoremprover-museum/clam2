/* Coloured rippling support for XClam
 * @(#)$Id: init_colour.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: init_colour.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include <stdio.h>
#include <X11/Xlib.h>
#include <X11/Intrinsic.h>
#include <X11/Xatom.h>
#include <string.h>


#define X 200
#define Y 200
#define WIDTH 1150
#define HEIGHT 300
#define border 30
#define WF_COLOUR gray
#define BACKGROUND_COLOUR white


#define ESCAPE '$'
#define WF_START '`'
#define WH_START '{'
#define WF_END '\''
#define WH_END '}'
#define EXP_START 'u'
#define EXP_END 'd'
#define MATH_START 'm'
#define MATH_END 'n'

#define INDENT 20

 extern Display *display;

typedef struct _XColourList {
  XColor colour;
  struct _XColourList *next_colour;
} XColourList;

String ParseAndWriteColourString(XColor,String);
void parse_o_paren(String);
void parse_c_paren(String);
void parse_token(String *,String *);

/* Window  window; */
extern Widget rippleWindow;
XFontStruct *fontpoint_large, *fontpoint_small, *fontpoint_math_large, 
  *fontpoint_math_small, *fontpoint;
XSetWindowAttributes attributes;
XGCValues gr_values;
GC gr_context;
Visual *visual;
unsigned long depth_of_font;

int y_pos;
int depth, screen;
XEvent event;
unsigned long myforeground, mybackground;
int x_pos, vertical_shift;

#define RED 1
#define YELLOW 2
#define BLUE 4
#define ORANGE (RED | YELLOW)
#define PURPLE (RED | BLUE)
#define GREEN (YELLOW | BLUE)
#define BROWN (RED | YELLOW | BLUE)
#define BLACK 0
/* the colour system is as follows:
 * there are three primitives, R, Y, B, which give a (paint) mixing as follows:
 * R.. = Red
 * .Y. = Yellow
 * ..B = Blue
 * RY. = Orange
 * R.B = Purple
 * .YB = Green
 * ... = Black
 * RYB = Brown
 */
XColor    red, yellow, blue, orange, purple, green, black, white, brown, gray, dummy;

void
  ClearTextWindow()
{ char e;
  /* Clear the buffer */
  e = XSetForeground(display, gr_context,mybackground );
  e = XFillRectangle(display, XtWindow(rippleWindow), gr_context, 0, 0, 
		     WIDTH, 
		     HEIGHT);
  x_pos = INDENT;
  y_pos = (int) (depth_of_font * 1.6) ;
  vertical_shift = 0;
}

void
WriteColourString(XColor colour,String s)
{ XTextItem items[1];
  int e;
  
  XSetForeground(display, gr_context, colour.pixel);     /* colour of ink */
  /* construct a text item */
  items[0].chars = s;
  items[0].nchars = strlen(s);
  items[0].delta = 0;
  items[0].font = None;
  e = XDrawText(display,XtWindow(rippleWindow),gr_context,x_pos,(y_pos-vertical_shift),items,1);
  
  x_pos= x_pos + XTextWidth(fontpoint,s,strlen(s));
}  
void
  WriteColourChar(XColor colour,char ch)
{ char ca[] = "1";
  
  ca[0] = ch;
  if ((x_pos > (WIDTH * 0.5))) { /* bell is ringing */
    if ((ch == '=') ||
  	(ch == (char) 217 )) {  /* do a new-line and indent a bit more than normal */
      x_pos = (int) (WIDTH / 4);
      y_pos = y_pos + (int) (depth_of_font * 2.0) ;
    }
  }	
  WriteColourString(colour,ca);
}  

void
  initialize_colour_window()
{
  /* display = XOpenDisplay(NULL); */
  screen = DefaultScreen(display);
  visual = DefaultVisual(display,screen);
  depth  = DefaultDepth(display,screen);
  attributes.background_pixel = XBlackPixel(display,screen);
  mybackground = BlackPixel(display,screen);
  myforeground = WhitePixel(display,screen);
  
  fontpoint_large = XLoadQueryFont(display,"10x20");
  fontpoint_small = XLoadQueryFont(display,"9x15bold");
  fontpoint_math_large = XLoadQueryFont(display,"-adobe-symbol-*-*-*-*-20-*-*-*-*-*-*-*");
  fontpoint_math_small = XLoadQueryFont(display,"-adobe-symbol-*-*-*-*-16-*-*-*-*-*-*-*");
  fontpoint = fontpoint_large;
  /* red, yellow, blue, orange, purple, green, black, white, brown */
  
  XAllocNamedColor(display, DefaultColormap(display, screen),"red",
		   &red,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"yellow",
		   &yellow,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"blue",
		   &blue,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"orange",
		   &orange,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"purple",
		   &purple,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"green",
		   &green,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"black",
		   &black,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"white",
		   &white,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"brown",
		   &brown,&dummy);
  XAllocNamedColor(display, DefaultColormap(display, screen),"gray",
		   &gray,&dummy);
  gr_values.font = fontpoint_large->fid;
  gr_values.foreground = myforeground;
  gr_values.background = mybackground;
  gr_values.function = GXcopy;
  gr_context=XCreateGC(display,XtWindow(rippleWindow),
		       GCFont+GCFunction+GCForeground+GCBackground, &gr_values);
  (void) XGetFontProperty(fontpoint_large,XA_X_HEIGHT,&depth_of_font);
}

void
  parse_o_paren(String s)
{
  if (*s++ != '(')
    exit(1);
}    
void
  parse_c_paren(String s)
{
  if (*s++ != ')')
    exit(1);
}    

void
  parse_token(String *pt, String *ps)
{ /* parse but don't write */
  *pt = *ps;
  while (*((*ps)++) != ';')
    /* do nothing */;
}

int
  parse_colour(String *s)
{ /* red, yellow, blue, orange, purple, green, black, brown */
  
  /* colour lookup */
  if (strncmp(*s,"black",5)==0){
    (*s) = (*s) + 5;
    return(BLACK);}
  else
    if (strncmp(*s,"red",3)==0){
      (*s) = (*s) + 3;
      return(RED);}
    else
      if (strncmp(*s,"blue",4)==0){
	(*s) = (*s) + 4;
	return(BLUE);}
      else
	if (strncmp(*s,"green",5)==0){
	  (*s) = (*s) + 5;
	  return(GREEN);}
	else
	  if (strncmp(*s,"brown",5)==0){
	    (*s) = (*s) + 5;
	    return(BROWN);}
	  else
	    if (strncmp(*s,"yellow",6)==0){
	      (*s) = (*s) + 6;
	      return(YELLOW);}
	    else
	      if (strncmp(*s,"purple",6)==0){
		(*s) = (*s) + 6;
		return(PURPLE);}
	      else
		if (strncmp(*s,"orange",6)==0){
		  (*s) = (*s) + 6;
		  return(ORANGE);}
		else {
		  fprintf(stderr,"Unknown colour >> %s <<\n",*s);
		  exit(1);
		}
}

XColor
  parse_colour_list(String *s)
/* the colour list is of the form:
   [[[a,b,c]]];
   where ; is a delimiter (see xutil.pl) and 
   a, b  etc are strings like red green etc.
   */
{ int c = BLACK;
  
  /*  fprintf(stderr,"parse_colour_list: %s\n",*s);
   */
  while (**s != ';'){
    if ((**s == '[') || (**s == ',') || (**s == ']'))
      (*s)++;
    else
      c = c | parse_colour(s); /* OR the colours to mix them */
  }
  (*s)++;
  /* map c:int to an XColor */
  if (c > 8){
    fprintf(stderr,"Internal error\n");
    exit(1);
  }
  switch (c) /* red, yellow, blue, orange, purple, green, black, brown */
    {
    case RED: return(red); break;
    case YELLOW: return(yellow); break;
    case BLUE: return(blue); break;
    case ORANGE: return(orange); break;
    case PURPLE: return(purple); break;
    case GREEN: return(green); break;
    case BLACK: return(black); break;
    case BROWN: return(brown); break;
    }
}


String 
  ParseAndWriteColourString(XColor colour,String s)
/* top-down parses a plain string and writes a coloured version of it to the
 * drawable window.  The parsing is for wave-fronts and holes:
 *  ``<term>'' writes <term> in colour WF_COLOUR
 *  {<term>}   write <term> in colour given by colour
 */
{ char ch;			/* lookahead */
  String t = NULL;
  XColor new_colour;
  
  
  /*  fprintf(stderr,"- %s\n",s);
      fflush(stderr);
      */
  /* find next instance of meta-level construct */
  while (ch = (*s++)){
    if ((ch == ESCAPE) && (*s == WF_START)){
      /* found a wave-front, so switch to WF_COLOUR, skip tokens and recurse */
      s++;
      parse_token(&t,&s);	 	/* skip over the direction flag */
      s = ParseAndWriteColourString(WF_COLOUR,s);
    } else {
      if  ((ch == ESCAPE)&&(*s == WH_START)){
	s++;
	new_colour=parse_colour_list(&s);       /* colour token */
	s = ParseAndWriteColourString(new_colour,s);
      }
      else {
	if ((ch == ESCAPE)&&(*s == EXP_START)){
	  int old_shift = vertical_shift;
	  XFontStruct *old_fontpoint = fontpoint;
	  
	  s++;
	  vertical_shift = vertical_shift + (int) (depth_of_font / 1.5);
	  
	  if (fontpoint == fontpoint_math_small){
	    /* dont change font size */
	  } else
	    if (fontpoint == fontpoint_math_large){
	      fontpoint = fontpoint_math_small;
	    }
	    else
	      fontpoint = fontpoint_small;
	  
	  gr_values.font = fontpoint->fid;
	  gr_context=XCreateGC(display,XtWindow(rippleWindow),
			       GCFont+GCFunction+GCForeground+GCBackground, &gr_values);
	  s = ParseAndWriteColourString(colour,s);
	  gr_values.font = old_fontpoint->fid;
	  gr_context=XCreateGC(display,XtWindow(rippleWindow),
			       GCFont+GCFunction+GCForeground+GCBackground, &gr_values);
	  vertical_shift = old_shift;
	  fontpoint = old_fontpoint;
	}
	else {
	  if ((ch == ESCAPE)&&(*s == MATH_START)){
	    XFontStruct *old_fontpoint = fontpoint;
	    s++;
	    
	    if ((fontpoint == fontpoint_math_small) ||
		(fontpoint == fontpoint_math_large)){
	      /* stay the same */
	    } else
	      if ((fontpoint == fontpoint_small)){
		fontpoint = fontpoint_math_small;
	      } else
		if ((fontpoint == fontpoint_large)){
		  fontpoint = fontpoint_math_large;
		} else
		  {
		    fprintf(stderr,"Internal error in MATH START\n");
		    exit(1);
		  }
	    
	    gr_values.font = fontpoint->fid;
	    gr_context=XCreateGC(display,XtWindow(rippleWindow),
				 GCFont+GCFunction+GCForeground+GCBackground, &gr_values);
	    s = ParseAndWriteColourString(colour,s);
	    
	    gr_values.font = old_fontpoint->fid;
	    gr_context=XCreateGC(display,XtWindow(rippleWindow),
				 GCFont+GCFunction+GCForeground+GCBackground, &gr_values);
	    fontpoint = old_fontpoint;
	  }else {
	    if ((ch == ESCAPE) && (*s == WF_END)){
	      s++;
	      return(s);
	    }
	    else {
	      if ((ch == ESCAPE) && (*s == WH_END)){
		s++;
		return(s);
	      }
	      else {
		if ((ch == ESCAPE) && (*s == EXP_END)){
		  s++;
		  return(s);
		} else {
		  if ((ch == ESCAPE) && (*s == MATH_END)){
		    s++;
		    return(s);
		  }else {
		    /* nothing special, so just echo these */
		    if (ch == '\n'){
		      x_pos = INDENT;
		      y_pos = y_pos + (int) (depth_of_font * 2.0) ;
		    }
		    else {	
		      if ((ch == ESCAPE) && (*s == ESCAPE))
			s++;
		      WriteColourChar(colour,ch);	      
		      /*	            fprintf(stderr,"%c",ch)	      */;
		    }
		  }
		}
	      }
	    }
	  }
	}
      }
    }
  }  
}

static String buffer = NULL;
String concat(String,String);

void
WriteRippleTerm(String s)
{  int len =0;
   String nlpos = NULL;

   len = strlen(s);


   buffer = concat(buffer,s);
   if ((nlpos=strrchr(buffer,'\n'))){
     String tmp_buff;

     tmp_buff = concat(NULL,nlpos+1);
     *(nlpos+1)='\0';
     (void) ParseAndWriteColourString(BACKGROUND_COLOUR,buffer);
     XtFree(buffer);
     buffer=tmp_buff;
   }
   else
     /* wait until \n recieved */;
}

/*
 * @(#)$Id: read_write.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: read_write.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include "global.h"
char    *concat();


struct c_entry {
  String c_name;		/* command string */
  void  (*c_func)(String *);	/* associated function */
};


static String buffer=NULL;
static int buffsize=0;

static void id_func(String *s) {/* do nothing */;}

static void c_w_plan(String *s)
  { fprintf(stderr,"PLAN\n");
    currentOutputWindow = planWindow;}
static void c_w_ripple(String *s)
  { fprintf(stderr,"RIPPLE\n");
    currentOutputWindow = rippleWindow;}
static void c_w_dialog(String *s)
  { fprintf(stderr,"DIALOG\n");
    currentOutputWindow = dialogWindow;}
static void c_w_proof(String *s)
  { fprintf(stderr,"PROOF\n");
    currentOutputWindow = proofWindow;}
static void c_ripple_clear(String *s)
  {ripple_clear();}
static void c_plan_clear(String *s)
  {plan_clear();}
static void c_DeleteLine(String *s)
  {DeleteLine();}
static void c_PreviousLine(String *s)
  {PreviousLine();}
static void
c_replace_line(String *s)
{
  int tmp = strlen(*s);		/* this much to skip over */

  replace_line(*s); 
  (*s) = (*s) + tmp;
}

struct c_entry c_table[] = {
  { "|: ", id_func },
  { "change_windowplan\n", c_w_plan },
  { "change_windowripple\n", c_w_ripple },
  { "change_windowdialog\n", c_w_dialog },
  { "change_windowproof\n", c_w_proof },
  { "clear\n", c_ripple_clear },
  { "clrplan\n", c_plan_clear },
  { "killline\n", c_DeleteLine },
  { "backup\n", c_PreviousLine },
  { "rewrite", c_replace_line },
  { (String) NULL, NULL } };
  

void
send_substring(String start, String end)
{ char tmp = *end;

  *end = '\000';		/* terminate the substring */
  if (currentOutputWindow == dialogWindow)
    AppendDialogText(start);
  else if (currentOutputWindow == rippleWindow)
    WriteRippleTerm(start);
  else
    writeout(start);
  *end = tmp;			/* revert to previous */
}
  
    
Boolean
process_output(String s)
{ int l, i=0;
  String prev_pos = s;
  String endpos = s+strlen(s);
  
  fprintf(stderr,"%s",s);
  while (*s){
    while (c_table[i].c_name){
      if ((s+(l=strlen(c_table[i].c_name)))<=endpos){
	if (strncmp(c_table[i].c_name,s,l)==0){
	  send_substring(prev_pos,s); /* dump what we scanned over */
	  s = s + l;
	  (*(c_table[i].c_func))(&s); /* execute the associated function */
	  i = 0;			/* start at the beginning */
	  prev_pos = s;
	}
	else
	  i++;			/* try the other commands */
      }
      else
	i++;
    }
    i = 0;			/* start of command list */
    if (*s != '\000'){
      s = (String) strchr(s,'\n');
      if (s==NULL){		/* a prompt is terminated by NULL */
	s = endpos;		/* point at the end */
      }
      else
	s++;			/* skip the \n */
    }
  }
  send_substring(prev_pos,s);
}


void
read_clam(XtPointer master, int *source, XtInputId *id)
{
  Boolean     more;
  int len = 0;
  int num = 0;
  int lb =0;

  String last_nl, status;


  more = True;
  while (more) {
    /* keep reading until no more input arrives */
    if (buffer == NULL){ /* buffer empty */
      lb=0;
      buffer= (String)malloc(sizeof(char)*LINESIZE);
      *buffer = '\0';
      buffsize=sizeof(char)*LINESIZE;
    }
    else{
      lb = strlen(buffer);
      if ((buffsize-lb) < LINESIZE){
	buffer=(String)realloc(buffer,sizeof(char)*(lb+LINESIZE)); /* get more space */
	buffsize = sizeof(char)*(lb+LINESIZE);
      }
    }
    status = fgets(buffer+lb, LINESIZE, dbxfp);	/* fill it */
    more = (status != NULL);
    if (more){
      last_nl = (String) strrchr(buffer,'\n');
      if (last_nl == NULL){	/* none found, so buffer entire i/p */
	while (strncmp(prologprompt,buffer,strlen(prologprompt))==0){
	  AppendDialogText(prologprompt);
	  strcpy(buffer,buffer+strlen(prologprompt));
	}
	last_nl = buffer;
      }      
      else{
	last_nl++;
      }
      len=strlen(last_nl);
      if (len){			/* there is some to buffer */
	String tmp_buffer= (String) malloc(sizeof(char)*len+1);	    
	
	strcpy(tmp_buffer,last_nl);
	*last_nl = '\000';
	process_output(buffer);	/* dispense with all these lines */
	free(buffer);
	buffer = tmp_buffer;
	buffsize = sizeof(char)*len+1;
      }
      else{
	/* there is nothing to buffer */
	*last_nl = '\000';
	process_output(buffer);	/* dispense with all these lines */
	free(buffer);
	buffer = NULL;
	buffsize = 0;
      }
    }
  }
}


/* Clean up this and the below */
void writeout(s)
String s;
{
    XawTextPosition lastPos;
    XawTextBlock    textblock;

    textblock.firstPos = 0;
    textblock.length   = strlen(s);
    textblock.ptr      = s;

    lastPos = TextGetLastPos(currentOutputWindow);
    XawTextReplace(currentOutputWindow,lastPos,lastPos, &textblock);

/*      if (currentOutputWindow == dialogWindow)
             StartPos = XawTextGetInsertionPoint(dialogWindow);
             StartPos= TextGetLastPos(dialogWindow);*/
             XawTextSetInsertionPoint(currentOutputWindow, lastPos+textblock.length);

/*LOOK 11 NEXT LINE
                StartPos = lastPos + textblock.length +11;
*/


}

/* Clean up this and the above */
void write_to(w,s)
Widget w;
String s;
{   
    XawTextPosition lastPos;
    XawTextBlock    textblock;

    textblock.firstPos = 0;
    textblock.length   = strlen(s);
    textblock.ptr      = s;

    
/*             lastPos = XawTextGetInsertionPoint(currentOutputWindow); */

          lastPos = TextGetLastPos(w);
             XawTextReplace(w,lastPos,lastPos, &textblock);

/*      if (w == dialogWindow)
             StartPos = XawTextGetInsertionPoint(dialogWindow);
             StartPos= TextGetLastPos(dialogWindow);*/
             XawTextSetInsertionPoint(w, lastPos+textblock.length);

}



void write_clam(string)
char * string;
{
  currentOutputWindow = dialogWindow;
  fputs(string,dbxfp);
  fflush(dbxfp);
}

void ripple_output(s)
char * s;
{

     XawTextBlock    textblock;
     XawTextPosition lastPos;

            lastPos = TextGetLastPos(rippleWindow);
            textblock.firstPos = 6;
            textblock.length   = strlen(s);
            textblock.ptr      = s;
            XawTextReplace(rippleWindow, 0, lastPos, &textblock);
            strcpy(s,"");
}

void ripple_clear()
{
  ClearTextWindow();
}

void plan_clear()
{


         XawTextBlock    textblock;
     	 XawTextPosition lastPos;

            lastPos = TextGetLastPos(planWindow);
            textblock.firstPos = 0;
            textblock.length   = 0;
            textblock.ptr      = "";
            XawTextReplace(planWindow, 0, lastPos, &textblock);
}


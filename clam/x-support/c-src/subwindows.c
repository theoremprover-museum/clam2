/*
 * @(#)$Id: subwindows.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: subwindows.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include "global.h"
/* #include  "utils.c"
#include "callclam.c"
#include "read_write.c" */

/*#include <X11/Xaw/MenuButton.h>
#include <X11/Xaw/SimpleMenu.h>
#include <X11/Xaw/Sme.h>
#include <X11/Xaw/SmeBSB.h>
#include <X11/Xaw/Cardinals.h> */

#include <signal.h>
#define MAXARGS 20


Widget          toplevel;               /* top level widget */
	Widget planWindow;
	Widget proofWindow;
	Widget dialogWindow;
	Widget formWindow;
	Widget formWindow2;
	Widget commandBox;
        Widget rippleWindow;
        Widget otherWindow;
        Widget otherWindow2;
        Widget otherWindow3;
        Widget rippleShell;
        Widget rippleLabel;
	Widget b1;
	Widget b2;
	Widget b3;
	Widget b4;
	Widget b5;
	Widget b6;
	Widget b7;
        Widget b8;

        Widget colour_button;

	Widget entry;
	Widget menu;
	Widget menu2;
	Widget menu3;
	Widget menu4;
	Widget menu5;
        Widget menu6;
	Widget menu7;
	Widget menu8;
	Widget menu9;

        Widget subbox;
	Widget subbox2;
        Widget msubbox;
        Widget m2subbox;
	Widget m5subbox;
	Widget m7subbox;
	Widget optionBox;
	Widget extrabutton;

Widget rememberCurrent;


typedef struct {

	int    firstpos;
	int    lastpos;
} plan_pos, * plan_posptr ;


plan_pos  xidplan, xdplan, dplan, idplan, bplan;

static XawTextPosition newpos;
static XawTextPosition endpos;


static char DialogText[DIALOGSIZE];     /* text buffer for widget */
/*static char PlanText[DIALOGSIZE];      text buffer for widget */
static XawTextPosition  StartPos;       /* starting position of input text */
Boolean FalseSignal=FALSE;
Boolean status[15];
Boolean ripple_status[1];
Boolean colour_status[1];
Pixmap mark;

    static XtActionsRec trial_actions[] = {
        {"checkRightAndPopupSubmenu", CheckRightAndPopupSubmenu},
        {"popdownSubmenu", PopdownSubmenu},
	{"dialogReturn", dialogReturn},
        {"dialogNewline", dialogNewline},
        {"libDialogNewline", libDialogNewline},
	{"planDialogNewline", planDialogNewline},
	{"pickout",pickout},
	{"rippleNewline", rippleNewline},
    };


Syntax(call)
char * call;
{
	fprintf(stderr,"Usage: %s\n",call);
}

void Activate(w,client_data,call_data)
	Widget w;
	caddr_t client_data;
	caddr_t call_data;
{
	printf("button was activated.\n");
	exit(0);
}


/*  Sends an EOF signal to dbx. (ctrl-D) */
/* ARGSUSED */
void
SigEof(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
  fputs("\04",dbxfp);
  fflush(dbxfp);

/*    write_dbx("\04"); */
}

/*  Sends an interrupt signal, SIGINT, to dbx.
 *  Simulates the action of the INTR character (ctrl-C).
 */
/* ARGSUSED */
void
SigInt(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    currentOutputWindow = dialogWindow; 
    FalseSignal = TRUE;
    killpg(dbxpid, SIGINT);
}


void
InsertSpace(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    XawTextBlock    textblock;
    XawTextPosition lastPos;

    if (XawTextGetInsertionPoint(w) <= StartPos) {
        lastPos = TextGetLastPos(w);
        if (lastPos == StartPos) {
            textblock.firstPos = 0;
            textblock.length   = 1;
            textblock.ptr      = " ";
            XawTextReplace(w, lastPos, lastPos, &textblock);
            XawTextSetInsertionPoint(w, lastPos+1);
        }
    }
}


void bell(volume)
int volume;
{
    XBell(XtDisplay(toplevel), volume);
}

void DeleteLine(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    XawTextBlock        textblock;
    XawTextPosition     pos, beginPos;
    Cardinal            i;
    char                *s;

    textblock.firstPos = 0;
    textblock.length   = 0;
    textblock.ptr      = "";

    pos = XawTextGetInsertionPoint(currentOutputWindow);
    if (currentOutputWindow == dialogWindow) {
        s = DialogText;
        beginPos = StartPos;
        if (pos <= beginPos)
            pos = TextGetLastPos(dialogWindow);
    }
    else
      if (currentOutputWindow == planWindow){
            s = PlanText;
            beginPos = 0;
            pos = TextGetLastPos(planWindow);
       }

        else {

             Arg sarg[1];
             XtSetArg(sarg[0], XtNstring, &s);
             XtGetValues(currentOutputWindow, sarg, 1);
             beginPos=0;
        }
    for (i=pos; i > beginPos && s[i-1] != '\n' ; i--);
    XawTextReplace(currentOutputWindow, i, pos, &textblock);
    XawTextSetInsertionPoint(currentOutputWindow, i);
}

void PreviousLine(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    XawTextBlock        textblock;
    XawTextPosition     pos, beginPos;
    Cardinal            i;
    char                *s;

    textblock.firstPos = 0;
    textblock.length   = 0;
    textblock.ptr      = "";

    pos = XawTextGetInsertionPoint(currentOutputWindow);
    if (currentOutputWindow == dialogWindow) {
        s = DialogText;
        beginPos = StartPos;
        if (pos <= beginPos)
            pos = TextGetLastPos(dialogWindow);
    }
    else 
      if (currentOutputWindow == planWindow){
            s = PlanText;
            beginPos = 0;
            pos = TextGetLastPos(planWindow);
       }
       else {

         Arg sarg[1];
         XtSetArg(sarg[0], XtNstring, &s);
         XtGetValues(currentOutputWindow, sarg, 1);
         beginPos=0;

    }
    for (i=pos; i > beginPos && s[i] != '\n' ; i--);
    XawTextReplace(currentOutputWindow, i, pos, &textblock); 
    XawTextSetInsertionPoint(currentOutputWindow, i);

}

void AppendDialogText(s)
    char   *s;
{
    XawTextPosition     i, lastPos;
    XawTextBlock        textblock, nullblock;
    Arg                 args[MAXARGS];
    Cardinal            n;

    if (!s || !strcmp(s, "")) return;

    textblock.firstPos = 0;
    textblock.length   = strlen(s);
    textblock.ptr      = s;

    lastPos = TextGetLastPos(dialogWindow);
    if (textblock.length > DIALOGSIZE) {
        bell(0);
        fprintf(stderr, "xdbx error: cannot display string in dialogue window\n\
            string has %d bytes; dialogue window size limit is %d bytes\n",
            textblock.length, DIALOGSIZE);
        return;
    }
    if (lastPos + textblock.length > DIALOGSIZE) {
        nullblock.firstPos = 0;
        nullblock.length = 0;
        nullblock.ptr = "";

        i = textblock.length - (DIALOGSIZE - lastPos);
        if (i < 0.9*DIALOGSIZE)
            i += 0.1*DIALOGSIZE;
        while (DialogText[i] != '\n') i++;
        XawTextReplace(dialogWindow, 0, i+1, &nullblock);
        lastPos = TextGetLastPos(dialogWindow);
    }
    XawTextReplace(dialogWindow, lastPos, lastPos, &textblock);
    StartPos = TextGetLastPos(dialogWindow);
    XawTextSetInsertionPoint(dialogWindow, StartPos);
}


void
redir_out(w, event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{

  char st[1028];

  strcpy(st, DialogText + StartPos);

  fputs(st,dbxfp);
  fflush(dbxfp);
  StartPos = XawTextGetInsertionPoint(dialogWindow);
}


void CreateSubWindows(parent)
Widget parent;
{

   Arg        args[MAXARGS];
   Cardinal   n;


   n=0;
   XtSetArg(args[n], XtNborderWidth,(XtArgVal) 0); n++;
   XtSetArg(args[n], XtNdefaultDistance,(XtArgVal) 0); n++;
   formWindow = XtCreateManagedWidget("formWindow",formWidgetClass,
                    otherWindow3,args,n);
   formWindow2 = XtCreateManagedWidget("formWindow2",formWidgetClass,
                    parent,args,n);
   CreateCommandBox(formWindow2);
   CreateOptionBox(formWindow2);
   CreateDialogWindow(otherWindow);
   CreatePlanWindow(otherWindow2);
   CreateRippleWindow(formWindow);
   CreateProofWindow(formWindow);
}


void CreateProofWindow(parent)
Widget parent;
{
    Arg         args[MAXARGS];
    Cardinal    n;

    n = 0;
    XtSetArg(args[n], XtNeditType, (XtArgVal) XawtextEdit);          n++;
    XtSetArg(args[n],XtNtextOptions, (XtArgVal) 0x04|0x02 );     /* scrollbar */         n++;
 /*   XtSetArg(args[n], XtNheight,  (XtArgVal)402);              n++;
    XtSetArg(args[n], XtNwidth,   (XtArgVal)400);              n++;
    XtSetArg(args[n], XtNfromVert, (XtArgVal) commandBox);           n++;
    XtSetArg(args[n], XtNfromHoriz, (XtArgVal) planWindow);           n++;
  */  XtSetArg(args[n], XtNhorizDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNvertDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNwrap, XawtextWrapLine);                       n++;
    /* XtSetArg(args[n], XtNbottom, (XtArgVal) XtChainBottom);     n++ ; */
        XtSetArg(args[n], XtNtop, (XtArgVal) XtChainTop);     n++ ;
    proofWindow = XtCreateManagedWidget("proofWindow",asciiTextWidgetClass,                        parent,args,n);
}


void CreatePlanWindow(parent)
Widget parent;
{
    Arg         args[MAXARGS];
    Cardinal    n;

    static XtActionsRec plan_actions[] = {
        {"SigEof",      (XtActionProc) SigEof},
        {"InsertSpace", (XtActionProc) InsertSpace},
        {"DeleteLine",      (XtActionProc) DeleteLine},
        {NULL, NULL}
    };


    
    static String translations = "#override\n\
        Ctrl<Key>D:     SigEof()\n\
        Ctrl<Key>U:     DeleteLine()\n\
        Ctrl<Key>H:     InsertSpace() delete-previous-character()\n\
        <Key>Delete:    InsertSpace() delete-previous-character()\n\
        <Key>BackSpace: InsertSpace() delete-previous-character()\n\
     ";

    n = 0;
    XtSetArg(args[n], XtNeditType, (XtArgVal) XawtextEdit);          n++;
    XtSetArg(args[n],XtNtextOptions, (XtArgVal) 0x04|0x02 );     /* scrollbar */    n++;
    XtSetArg(args[n],XtNtextOptions, (XtArgVal) 0x04|0x02 );              n++;
    XtSetArg(args[n], XtNuseStringInPlace, True);                       n++;
    XtSetArg(args[n], XtNstring, (XtArgVal) PlanText);             n++;
    XtSetArg(args[n], XtNlength, (XtArgVal) DIALOGSIZE);                n++;
/*    XtSetArg(args[n], XtNheight,  (XtArgVal)200);              n++;
    XtSetArg(args[n], XtNwidth,   (XtArgVal)400);              n++;
    XtSetArg(args[n], XtNfromVert, (XtArgVal) dialogWindow);         n++;
 */   XtSetArg(args[n], XtNvertDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNhorizDistance, (XtArgVal)0);                 n++;
    planWindow = XtCreateManagedWidget("planWindow",asciiTextWidgetClass,
                   parent,args,n);
    XtOverrideTranslations(planWindow, XtParseTranslationTable(translations));
    XtAppAddActions(app_context, plan_actions, XtNumber(plan_actions));

}

void CreateDialogWindow(parent)
Widget parent;
{
    Arg         args[MAXARGS];
    Cardinal    n;

    static XtActionsRec dialog_actions[] = {
        {"redir_out",    (XtActionProc) redir_out},
        {"SigInt",       (XtActionProc) SigInt},
        {"SigEof",      (XtActionProc) SigEof},
        {"InsertSpace", (XtActionProc) InsertSpace},
        {"DeleteLine",      (XtActionProc) DeleteLine},
        {NULL, NULL}
    };

    static String translations = "#override\n\
        Ctrl<Key>D:     SigEof()\n\
        Ctrl<Key>C:     SigInt()\n\
        <Key>Return:     newline() redir_out()\n\
        Ctrl<Key>U:     DeleteLine()\n\
        Ctrl<Key>H:     InsertSpace() delete-previous-character()\n\
        <Key>Delete:    InsertSpace() delete-previous-character()\n\
        <Key>BackSpace: InsertSpace() delete-previous-character()\n\
     ";


    n = 0;
    XtSetArg(args[n], XtNeditType, (XtArgVal) XawtextEdit);          n++;
    XtSetArg(args[n], XtNuseStringInPlace, True);                       n++;
    XtSetArg(args[n], XtNstring, (XtArgVal) DialogText);             n++;
    XtSetArg(args[n], XtNlength, (XtArgVal) DIALOGSIZE);                n++;
/*    XtSetArg(args[n], XtNheight,  (XtArgVal)200);              n++;
    XtSetArg(args[n], XtNwidth,   (XtArgVal)400);              n++;
    XtSetArg(args[n], XtNfromVert, (XtArgVal)commandBox);                 n++;
 */   XtSetArg(args[n], XtNvertDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNhorizDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNwrap, XawtextWrapLine);                       n++;
    XtSetArg(args[n], XtNscrollVertical, XawtextScrollAlways);          n++;
    /* XtSetArg(args[n], XtNbottom, (XtArgVal) XtChainBottom);     n++ ; */
       XtSetArg(args[n], XtNtop, (XtArgVal) XtChainTop);     n++ ;
    dialogWindow = XtCreateManagedWidget("dialogWindow", asciiTextWidgetClass,
                   parent,args,n);
    XtOverrideTranslations(dialogWindow, XtParseTranslationTable(translations));
    XtAppAddActions(app_context, dialog_actions, XtNumber(dialog_actions));
}

void CreateRippleWindow(parent)
Widget parent;
{
    Arg         args[MAXARGS];
    Cardinal    n;
    

    n = 0;
    XtSetArg(args[n], XtNeditType, (XtArgVal) XawtextEdit);          n++;
    XtSetArg(args[n], XtNhorizDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNvertDistance, (XtArgVal)0);                 n++;
    /* XtSetArg(args[n], XtNbottom, (XtArgVal) XtChainBottom);     n++ ; */
        XtSetArg(args[n], XtNtop, (XtArgVal) XtChainTop);     n++ ;
    rippleWindow = XtCreateManagedWidget("rippleWindow",asciiTextWidgetClass,
                   parent,args,n);
    rippleLabel = XtCreateManagedWidget("rippleLabel",labelWidgetClass,
		   parent,NULL,0);
}


void CreateCommandBox(parent)
Widget parent;
{
    Arg         args[MAXARGS];
    Cardinal    n;

    n = 0;
    XtSetArg(args[n], XtNheight,  (XtArgVal)50);              n++;
    XtSetArg(args[n], XtNwidth,   (XtArgVal)800);              n++;
    /* XtSetArg(args[n], XtNvertDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNhorizDistance, (XtArgVal)0);                 n++;
    XtSetArg(args[n], XtNfromVert, (XtArgVal) dialogWindow);   n++; */
    XtSetArg(args[n], XtNbottom, (XtArgVal) XtChainTop);     n++ ;
    XtSetArg(args[n], XtNleft, (XtArgVal) XtChainLeft);     n++ ;
    XtSetArg(args[n], XtNright, (XtArgVal) XtChainLeft);     n++ ;
    commandBox = XtCreateManagedWidget("commandBox", boxWidgetClass,
                 parent, args, n);
    CreateButtons(commandBox);
}
 

void CreateOptionBox(parent)
Widget parent;
{
    /* the optional miscellaneous command buttons */
void ExtraButton();
int i;
    if (app_resources.command_button_count > 0) {


	char	name[30];
	if (app_resources.command_button_count > 500)
	    app_resources.command_button_count = 500;
        optionBox = XtCreateManagedWidget("optionBox", boxWidgetClass,
                 parent, NULL, 0);
	for (i=1; i <= app_resources.command_button_count; i++) {
	    sprintf(name, "button%d", i);
/*    BBoxAddButton(scrn->miscbuttons, name, commandWidgetClass, True); */
        extrabutton = XtCreateManagedWidget(name, commandWidgetClass, optionBox,
			 NULL, ZERO); 
         XtAddCallback(extrabutton, XtNcallback, ExtraButton, NULL); 
       }
    }
}
void CreateButtons(parent)
Widget parent;
{

void MenuSelect();
void MenuItem();
void Exec();
void MenuLib();
void unPop();
/* put these in globals.h */

	static XtCallbackRec callbacks[]={
	{MenuSelect,NULL},
	{NULL,NULL},
	};

        static XtCallbackRec trace_callbacks[]={
        {MenuItem,NULL},
        {NULL,NULL},
        };

    static char * menu_item_names[] = {
        "load", "delete", "present", "save", "set",
        };


    static char * menu2_item_names[] = {
	"xdplan","xidplan","xdplan_all",
	};

    static char * menu3_item_names[] = {
	"trace","debug","spy","nodebug"
	};

        static char * menu4_item_names[] = {
           "label", "label2" , "label3", "label4",
        };

    static char * menu5_item_names[] = {
        "thm", "lemma", "wave", "synth", "scheme", "def", "eqn", "red",
        "mthd", "smthd","ind_plan1","ind_plan2","ind_plan3",
    };

    static char * menu6_item_names[] = {
        "tautology/1","sym_eval/1","ripple/1","weak_fertilize/2",
	"normalize/1","ind_strat/1","base_case/1","step_case/1",
	"fertilize/2", "ripple_and_cancel/1",
    };

    static char * menu7_item_names[] = { 
	"current", "new",
    };

    static char * menu8_item_names[] = {
	"run_free",
    };

    static char * menu9_item_names[] = {
	"Display wave-rules", 
    };

    Arg         args[MAXARGS];
    Arg         margs[MAXARGS];
    Cardinal    n,i,m;
char * item;

    n = 0;
    m = 0;
    
   XtSetArg(args[n], XtNcallback, callbacks); n++;
   /* XtSetArg(margs[m], XtNmenuName, "menu2"); m++; */


    b2 = XtCreateManagedWidget("lib",commandWidgetClass, parent, args, n);  
    b3 = XtCreateManagedWidget("plan",commandWidgetClass, parent,NULL,          ZERO);  
/*  b4 = XtCreateManagedWidget("pop",commandWidgetClass, parent,NULL,ZERO); */ 
    b8 = XtCreateManagedWidget("ripple",menuButtonWidgetClass, parent,args,n);
    colour_button = XtCreateManagedWidget("colour",menuButtonWidgetClass, parent,args,n);
/*  b5 = XtCreateManagedWidget("cascade",commandWidgetClass, parent,args,n); */ 
    b6 = XtCreateManagedWidget("formats",menuButtonWidgetClass, parent,args,n);  
    b1 = XtCreateManagedWidget("exec",commandWidgetClass, parent,NULL,ZERO);
        XtAddCallback(b1, XtNcallback, Exec, NULL);

    b7 = XtCreateManagedWidget("quit",commandWidgetClass, parent,args,n);  

    menu    = XtCreatePopupShell("menu", transientShellWidgetClass, parent,
			      NULL, ZERO);
    menu2   = XtCreatePopupShell("menu2", transientShellWidgetClass, parent,
                              NULL, ZERO);
    menu3   = XtCreatePopupShell("menu3", transientShellWidgetClass, parent,
                              NULL, ZERO);
    menu4   = XtCreatePopupShell("menu4", transientShellWidgetClass, parent,
                              NULL, ZERO);
    menu5   = XtCreatePopupShell("menu5", transientShellWidgetClass, parent,
                              NULL, ZERO);
    menu6   =  XtCreatePopupShell("menu6", simpleMenuWidgetClass, parent,
                              NULL, ZERO);
    menu7    = XtCreatePopupShell("menu7", transientShellWidgetClass, parent,
                              NULL, ZERO);
    menu8    = XtCreatePopupShell("menu8", simpleMenuWidgetClass, parent,
                              NULL, ZERO);

    menu9    = XtCreatePopupShell("menu9", simpleMenuWidgetClass, parent,
                              NULL, ZERO);

   

   msubbox = XtCreateManagedWidget(
        "msubbox",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );



    for (i = 0; i < (int) XtNumber(menu_item_names) ; i++) {
        char * item = menu_item_names[i];

        entry = XtCreateManagedWidget(item, commandWidgetClass, msubbox,
			 NULL, ZERO); 
         XtAddCallback(entry, XtNcallback, LibMenuItem, i); 
    }

    m2subbox  = XtCreateManagedWidget(
        "m2subbox",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu2,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );

    for (i = 0; i < (int) XtNumber(menu2_item_names) ; i++) {
       char * item = menu2_item_names[i]; 
       entry = XtCreateManagedWidget(item, commandWidgetClass, m2subbox,
                                      NULL, ZERO);
       XtAddCallback(entry, XtNcallback, planMenuItem, i );

    }
    subbox  = XtCreateManagedWidget(
        "subbox",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu3,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );


    for (i = 0; i < (int) XtNumber(menu3_item_names) ; i++) {
       char * item = menu3_item_names[i];
       entry = XtCreateManagedWidget(item, commandWidgetClass , subbox,
                                      NULL, ZERO);
 
        XtAddCallback(entry, XtNcallback, MainPaneChosen, i);
     /* actions ? added in app-defaults file  via translations*/
     /* OK we are making our own menu */
    }


    subbox2  = XtCreateManagedWidget(
        "subbox2",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu4,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );


    for (i = 0; i < (int) XtNumber(menu4_item_names) ; i++) {
       char * item = menu4_item_names[i];
       entry = XtCreateManagedWidget(item, commandWidgetClass , subbox2,
                                      NULL, ZERO);

        XtAddCallback(entry, XtNcallback, SubPaneChosen, i);
     /* actions ? added in app-defaults file  via translations*/
     /* OK we are making our own menu */
    }

  m5subbox = XtCreateManagedWidget(
        "m5subbox",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu5,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );
    for (i = 0; i < (int) XtNumber(menu5_item_names) ; i++) {
       char * item = menu5_item_names[i];
       entry = XtCreateManagedWidget(item, commandWidgetClass , m5subbox,
                                      NULL, ZERO);
        XtAddCallback(entry, XtNcallback, Lib2MenuItem, i);
    }



    for (i = 0; i < (int) XtNumber(menu6_item_names) ; i++) {
      char * item = menu6_item_names[i];
      entry = XtCreateManagedWidget(item, smeBSBObjectClass, menu6,
                                      NULL, ZERO);
        XtAddCallback(entry, XtNcallback, formatMenuItem, i);

    }

    m7subbox =  XtCreateManagedWidget(
        "m7subbox",               /* widget name   */
        boxWidgetClass,              /* widget class */
        menu7,                         /* parent widget*/
        NULL,                    /* argument list*/
        0           /* arglist size */
        );

    for (i = 0; i < (int) XtNumber(menu7_item_names) ; i++) {
       char * item = menu7_item_names[i];
       entry = XtCreateManagedWidget(item, commandWidgetClass , m7subbox,
                                      NULL, ZERO);
    }

    for (i = 0; i < (int) XtNumber(menu8_item_names) ; i++) {
      char * item = menu8_item_names[i];
      entry = XtCreateManagedWidget(item, smeBSBObjectClass, menu8,
                                      NULL, ZERO);
        XtAddCallback(entry, XtNcallback, rippleMenuItem, i);

    }

    for (i = 0; i < (int) XtNumber(menu9_item_names) ; i++) {
      char * item = menu9_item_names[i];
      entry = XtCreateManagedWidget(item, smeBSBObjectClass, menu9,
                                      NULL, ZERO);
        XtAddCallback(entry, XtNcallback, colourMenuItem, i);

    }


/*
       mark = XCreateBitmapFromData(XtDisplay(toplevel),
            RootWindowOfScreen(XtScreen(toplevel)),
            xlogo16_bits, xlogo16_width, xlogo16_height);
*/

       mark = XCreateBitmapFromData(XtDisplay(toplevel),
            RootWindowOfScreen(XtScreen(toplevel)),
            mybits_bits, mybits_width, mybits_height);

    XtAppAddActions(app_context, trial_actions, XtNumber(trial_actions));
    XtAddCallback(menu3, XtNpopupCallback, PlaceMenu, 0);
    XtAddCallback(menu,  XtNpopupCallback, PlaceMenu, 0);
     XtAddCallback(menu7,XtNpopupCallback, PlaceMenu, 0);
    
     CreatePopup(toplevel);
/*     XtAddCallback(b4, XtNcallback, upPop,NULL);
     XawDialogAddButton(dialogPopup,"ok", dialogReturn, 0);
     XawDialogAddButton(dialogPopup,"cancel",unPop, NULL);
     XawDialogAddButton(dialogPopup,"nomspy",dialogReturn,1);
*/
}


void 
MenuItem(w, junk, garbage)
Widget w;
XtPointer junk, garbage;
{
        String word = XtNewString( XtName(w)); 
        strcat(word,".\n");
     AppendDialogText(word);
     write_clam(word);
}

void
Exec()
{
   AppendDialogText("apply_xdplan.\n");
   write_clam("apply_xdplan.\n");

}

void
MenuLib(w, junk, garbage)
Widget w;
XtPointer junk, garbage;
{
    write_to(dialogWindow,"lib_load(");
    write_to(dialogWindow,XtName(w)); 
    write_to(dialogWindow,"("); 
}

void
MenuSelect(w, junk, garbage)
Widget w;
XtPointer junk, garbage;
{
    printf("Menu item `%s' has been selected.\n", XtName(w));
    if (streq(XtName(w), "quit")) {
        XtDestroyApplicationContext(XtWidgetToApplicationContext(w));
        exit(0);
    }
    if (streq(XtName(w), "thm")) {
        rememberCurrent = currentOutputWindow;
	currentOutputWindow=dialogWindow;
	writeout("lib_load(thm(");
	currentOutputWindow =  rememberCurrent;
    }
    if (streq(XtName(w), "quit")) {
        printf("gotcha");
        XtDestroyApplicationContext(XtWidgetToApplicationContext(w));
        exit(0);
    }
    if (streq(XtName(w), "trace")) {
        write_clam("trace.\n");
    }

    if (streq(XtName(w), "  )   ")) {
        rememberCurrent = currentOutputWindow;
	currentOutputWindow=dialogWindow;
	writeout(")");
	currentOutputWindow =  rememberCurrent;
    }
    if (streq(XtName(w), "  (   ")) {
        rememberCurrent = currentOutputWindow;
	currentOutputWindow=dialogWindow;
	writeout("(");
	currentOutputWindow =  rememberCurrent;
    }
    if (streq(XtName(w), "  .   ")) {
        rememberCurrent = currentOutputWindow;
	currentOutputWindow=dialogWindow;
	writeout(".");
	currentOutputWindow =  rememberCurrent;
    }
    if (streq(XtName(w), "  ,   ")) {
        rememberCurrent = currentOutputWindow;
	currentOutputWindow=dialogWindow;
	writeout(",");
	currentOutputWindow =  rememberCurrent;
    }

/* All the single char strings could be done with another function and a
 case statement */
}


void unPop(w, client_data, call_data)
Widget w;
XtPointer client_data; 
XtPointer call_data;
{
   XtPopdown(dialogShell);
   XtPopdown(libDialogShell);
   XtPopdown(planDialogShell);

}

void upPop(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{

   void placeDialogShell();
   placeDialogShell(w);
   XtPopup(dialogShell, XtGrabExclusive);

}

void libUpPop(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
    libPlaceDialog(w);
    XtPopup(libDialogShell, XtGrabExclusive);

}

void planUpPop(w)
Widget w;
{
    planPlaceDialog(w);
    XtPopup(planDialogShell, XtGrabExclusive);

}


void pickout(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
    
    String *  string;
    char *s;
    char * st;
    char buffer[500];
    char buff[500];
    String planner, position;
    Cardinal linebefore = 0;
    Cardinal spaces = 0;    
    static Cardinal branch[500] = {0};
    XawTextPosition stringpos;
    XawTextBlock    textblock, txtblock, textblck ;
    Widget source;
    Cardinal start, end;
int n = 0 ;
int m = 0;

     textblock.firstPos = 0;
     textblock.length   = 1;
     textblock.ptr      = "\n" ;

     txtblock.firstPos = 0;
     txtblock.length   = 0;
     txtblock.ptr      = "" ;

   endpos = XawTextSearch(planWindow, XawsdRight, &textblock);
   newpos = XawTextSearch(planWindow, XawsdLeft, &textblock);
   if (newpos < 0) newpos = 0;
   if (endpos < 0) endpos = TextGetLastPos(w);

     s = PlanText;
     for (start = newpos+1 ; s[start] == ' ' ; start++);
     if (start != 1 ) newpos  = (XawTextPosition) start;

/* make sure the insertion point is right on the first letter of the string */
/* go find the depth etc */
     start = 0 ;  /* set it to the beginning of the plan */
     n=0;
     while (branch[n] != 0) { branch[n]=0; n++;}

     while  (start < newpos){
            while(s[start++] != '\n');
            linebefore = spaces;
            spaces = 0;
            while(s[start++] == ' ') spaces++ ;
/*            if (spaces < linebefore && linebefore > 0 ){ */
              if (spaces <= linebefore && linebefore > 0 ){ 
                  int num = spaces / 2 ;
                  branch[(spaces / 2)-1] += 1;
                  while (branch[num] != 0 ) branch[num++] =0;
            } 
            else  branch[(spaces / 2)-1] = 1;
     }
    n = 0;
    if (branch[n] == 0)
        sprintf(buffer,"");
    else 
    while (branch[n] != 0){ sprintf(buffer+(n*2),"%d,", branch[n] ); n++; }

  if (n != 0) buffer[n*2-1] = '\0'; 
  sprintf(buff,"toggle_formats_in_plan(xdplan,[%s]).\n",buffer);
  AppendDialogText(buff);
  write_clam(buff);

}



void replace_line(s)
String s;
{       

    XawTextBlock    textblock;

        textblock.firstPos = 0;
        textblock.length = strlen(s)-1 ;
        textblock.ptr =  s;

        XawTextReplace (planWindow, newpos, endpos, &textblock);


}

void ExtraButton(w, call_data, client_data)
Widget w;
XtPointer call_data, client_data;
{
   String   name;
   char  command[100];

   XtVaGetValues(w,
		XtNlabel, &name,
   		NULL);
   sprintf(command,"%s.\n", name);
   AppendDialogText(command);
   write_clam(command);
}

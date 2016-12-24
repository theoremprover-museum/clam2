/*
 * @(#)$Id: mute.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: mute.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include "global.h"
/* #include "subwindows.c"
#include "signals.c" */
#include <X11/Xaw/Cardinals.h>

extern void
intialize_colour_window();


XtAppContext    app_context;
Display         *display;
Widget 	        currentOutputWindow;
XFontStruct     *fontpoint;
struct _resources app_resources;

String   fallback_resources[] = {
    "*input:                  True",
    "*ShapeStyle:	      Oval", 
    NULL,
};

/*
static XrmOptionDescRec options[] = {
    {"-font", "*Font",  XrmoptionSepArg,        NULL},
};
*/

#define offset(field) XtOffset(struct _resources *, field)


static XtResource resources[] = {
    {"commandButtonCount", "CommandButtonCount", XtRInt, sizeof(int),
	 offset(command_button_count), XtRImmediate, (XtPointer)0},
};

#undef offset

void main(argc, argv)
int argc;
char **argv; 
{ 

    trap_signals();

    toplevel = XtAppInitialize(&app_context, "XClam", NULL, 0, &argc, argv, fallback_resources, NULL, 0); 
    display = XtDisplay(toplevel);
    XtGetApplicationResources(toplevel, (XtPointer)&app_resources, resources, XtNumber(resources), NULL, 0);
/*
    printf("%s",app_resources.font);
    fflush(stdout);
      fontpoint = *(app_resources.font);
    printf("%d %d %d\n",fontpoint->ascent, fontpoint->descent, fontpoint->max_bounds.width) ; */  

 otherWindow = XtAppCreateShell("otherWindow", "XClam", topLevelShellWidgetClass, XtDisplay(toplevel),  NULL, ZERO);
 otherWindow2 = XtAppCreateShell("otherWindow2", "XClam", topLevelShellWidgetClass, XtDisplay(toplevel),  NULL, ZERO);

 otherWindow3 = XtAppCreateShell("otherWindow3", "XClam", topLevelShellWidgetClass, XtDisplay(toplevel),  NULL, ZERO);

    CreateSubWindows(toplevel);

    XtRealizeWidget(toplevel);
    XtRealizeWidget(otherWindow);
    XtRealizeWidget(otherWindow2);
    XtRealizeWidget(otherWindow3);

    initialize_colour_window();

    sleep(3);
    currentOutputWindow = dialogWindow;
    callclam(argc,argv);

    XtAppMainLoop(app_context);
}

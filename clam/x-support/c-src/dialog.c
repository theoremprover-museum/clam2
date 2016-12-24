/*
 * @(#)$Id: dialog.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: dialog.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include "global.h"

Widget dialogPopup;
Widget dialogShell;
Widget libDialogPopup;
Widget libDialogShell;
Widget planDialogShell;
Widget planDialogPopup;

String Choice1[80];
String Choice2[80];
String Choice3[80];
String Choice4[80];

void CreatePopup(parent)
Widget parent;
{
   dialogShell = XtCreatePopupShell("dialogPopup",
            transientShellWidgetClass,
            toplevel,
            NULL,
            0
            );

    dialogPopup = XtCreateManagedWidget(
            "dialogPopup",               /* widget name   */
            dialogWidgetClass,              /* widget class */
            dialogShell,                         /* parent widget*/
            NULL,                    /* argument list*/
            0           /* arglist size */
            );

   libDialogShell = XtCreatePopupShell("libDialogPopup",
            transientShellWidgetClass,
            toplevel,
            NULL,
            0
            );

   libDialogPopup = XtCreateManagedWidget(
            "libDialogPopup",               /* widget name   */
            dialogWidgetClass,              /* widget class */
            libDialogShell,                         /* parent widget*/
            NULL,                    /* argument list*/
            0           /* arglist size */
            );

     XawDialogAddButton(libDialogPopup,"ok", dialogReturn, 2);
     XawDialogAddButton(libDialogPopup,"cancel",unPop, 0);

   planDialogShell = XtCreatePopupShell("planDialogPopup",
            transientShellWidgetClass,
            toplevel,
            NULL,
            0
            );

   planDialogPopup = XtCreateManagedWidget(
            "planDialogPopup",               /* widget name   */
            dialogWidgetClass,              /* widget class */
            planDialogShell,                         /* parent widget*/
            NULL,                    /* argument list*/
            0           /* arglist size */
            );

     XawDialogAddButton(planDialogPopup,"ok", dialogReturn, 3);
     XawDialogAddButton(planDialogPopup,"cancel",unPop, 0);



}


void placeDialogShell(w)
Widget w;
{

    Position x, y;
    Dimension height;

    XtTranslateCoords(w,
        (Position) 0,        /* x */
        (Position) 0,       /* y */
        &x, &y);          /* coords on root window */

    XtVaGetValues(w,
            XtNheight, &height,
            NULL);

    XtVaSetValues(dialogShell,
            XtNx, x - 1,
            XtNy, y + height + 2,
            NULL);

    XtVaSetValues(dialogPopup,
	    XtNvalue, "",
	    NULL);
}

void dialogReturn(w, client_data,call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
      int num = (int) client_data;
      String buff[80] ;
     
	
		/* The translations do not allow for my self defined
		 * client data so I don't know what num is so
		 * it defaults to what I know its not 
		 */
           switch(num){
		case 0: sprintf(buff,"mspy(%s).\n",
				XawDialogGetValueString(dialogPopup));
			XtPopdown(dialogShell); break;
		case 1: sprintf(buff,"nomspy(%s).\n",
				XawDialogGetValueString(dialogPopup));
                        XtPopdown(dialogShell); break;


		case 2: if (strcmp((String)Choice1,(String)Choice2) != 0)
			   sprintf(buff,"lib_%s(%s(%s)).\n",Choice1, Choice2,
                               XawDialogGetValueString(libDialogPopup));
			else
                           if (strcmp((String)Choice1,"save") == 0){
			    sprintf(buff,"lib_save(%s).\n",
			     XawDialogGetValueString(libDialogPopup));
			   }
			   else 
			    sprintf(buff,"lib_set(dir('%s')),['%s/needs'].\n",
                             XawDialogGetValueString(libDialogPopup),
                             XawDialogGetValueString(libDialogPopup));
                           XtPopdown(libDialogShell); break;

		case 3: sprintf(buff,"plan_thm(%s,%s).\n" , Choice4, 
				XawDialogGetValueString(planDialogPopup));
			XtPopdown(planDialogShell); break;
	   }

/*           if (num != 1) sprintf(buff,"mspy(%s).\n",string);
             else sprintf(buff,"nomspy(%s).\n",string);
*/

           write_to(dialogWindow,buff);
           write_clam(buff); 
      
      
}


void libPlaceDialog(w)
Widget w;
{

    Position x, y;
 /*   Dimension height; */
    String string[80];
    
     if (strcmp((String)Choice1, (String)Choice2) == 0) {
        if (strcmp("save",(String)Choice1) == 0)
               strcpy((String)string,"lib_save(...).\n");
        else strcpy((String)string,"lib_set(dir('...')).\n");
     }
     else sprintf(string,"lib_%s(%s(...)).\n", Choice1, Choice2);

    XtTranslateCoords(w,
        (Position) 0,        /* x */
        (Position) 0,       /* y */
        &x, &y);          /* coords on root window */

 /*   XtVaGetValues(w,
            XtNheight, &height,
            NULL); */

    XtVaSetValues(libDialogShell,
            XtNx, x - 1,
            XtNy, y + 1,
            NULL);

    XtVaSetValues(libDialogPopup,
	    XtNvalue, "",
            XtNlabel, string,
	    NULL);

}

void dialogNewline(w,  event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    dialogReturn(w, 0 ,0 );

}

void libDialogNewline(w,  event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    dialogReturn(w, 2 ,0 );

}

void planDialogNewline(w,  event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    dialogReturn(w, 3 ,0 );

}

void planPlaceDialog(w)
Widget w;
{

    Position x, y;
    String string[200];

    XtTranslateCoords(w,
        (Position) 0,        /* x */
        (Position) 0,       /* y */
        &x, &y);          /* coords on root window */

    sprintf(string,"plan_thm(%s,...).", XtName(w));

    XtVaSetValues(planDialogShell,
            XtNx, x - 1,
            XtNy, y + 1,
            NULL);

    XtVaSetValues(planDialogPopup,
            XtNvalue, "",
            XtNlabel, string,
            NULL);
    
}

void rippleNewline(w,  event, params, num_params)
    Widget w;
    XEvent *event;
    String *params;
    Cardinal *num_params;
{
    
	write_clam("\n");

}


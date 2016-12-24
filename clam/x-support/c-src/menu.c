/*
 * @(#)$Id: menu.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: menu.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

/* Basic ideas from the O'Reilly book xmenu4.c with some variable name changes */
/* The full set of examples is in ~gordon/cprog/Xper/O.Reilly    */



#include "global.h"

/*ARGSUSED*/
void PlaceMenu(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
    Position x, y;
    Dimension height;

    Widget button ;

    if (w == menu) {
           button = b2 ;
    }
    else if (w == menu3 ){
    	button = b5 ;
         }
	else { button = b3; }

    /*
     * translate coordinates in application top-level window
     * into coordinates from root window origin.
     */
    XtTranslateCoords(button,                /* Widget */
        (Position) 0,        /* x */
        (Position) 0,       /* y */
        &x, &y);          /* coords on root window */

        /* get height of pressme so that menu is positioned below */
    XtVaGetValues(button,
            XtNheight, &height,
            NULL);


    /* move popup shell one pixel left and down to the bottom
     * +2 to allow for borders 
     * (it's not visible yet) */
    if ( button == b5) {
    XtVaSetValues(menu3,
            XtNx, x - 1,
            XtNy, y + height + 2,
            NULL);
    }
    else if ( button == b2 ) XtVaSetValues(menu,
            XtNx, x - 1,
            XtNy, y + height + 2,
            NULL);
	  else XtVaSetValues(menu7,
            XtNx, x - 1,
            XtNy, y + height + 2,
            NULL);


}


/*ARGSUSED*/
void CheckRightAndPopupSubmenu(w, event, params, num_params)
Widget w;
XEvent *event;
String *params;
Cardinal *num_params;
{
    XLeaveWindowEvent *leave_event = (XLeaveWindowEvent *) event;
    Dimension height, width;
    Position  x , y;

    XtVaGetValues(w,
            XtNheight, &height,
	    XtNwidth, &width,
            NULL);

    XtTranslateCoords(w,                /* Widget */
        (Position) 0,        /* x */
        (Position) 0,       /* y */
        &x, &y);          /* coords on root window */


    if ((leave_event->x > 0) && (leave_event->y > 0)
                && (leave_event->y < height)) {
        /* move submenu shell to start just right of pane,
         * using an arbitrary offset to place pointer in
         * first item. */
/*
        XtVaSetValues(menu4,
                XtNx, leave_event->x_root,
                XtNy, leave_event->y_root - 12,
                NULL); */

        if ( strcmp("new",XtName(w)) == 0 || strcmp("current",XtName(w)) == 0){
            XtVaSetValues(menu2,
		XtNx, x + width/2,
		XtNy, y ,
		NULL);
            strcpy((String)Choice3,XtName(w));
            XtPopup(menu2, XtGrabExclusive); 
	}
	else { XtVaSetValues(menu5,
                XtNx, x + width/2,
                XtNy, y ,
                NULL);
            strcpy((String)Choice1, XtName(w));
            XtPopup(menu5, XtGrabExclusive);
        }
        
    }
}



/*ARGSUSED*/
void PopdownSubmenu(w, event, params, num_params)
Widget w;
XEvent *event;
String *params;
Cardinal *num_params;
{
        XtPopdown(menu4);
	XtPopdown(menu5);
}


/*
 * menu pane button callback function
 */
/*ARGSUSED*/
void SubPaneChosen(w, client_data, call_data)
Widget w;
XtPointer client_data;  /* cast to pane_number */
XtPointer call_data;  /* unused */
{
    /* need some function here */
    int pane_number = (int) client_data;
     String buff[50];
     sprintf(buff,"SubPane %d chosen.\n", pane_number);
    writeout(buff);
    XtPopdown(menu4);
    XtPopdown(menu3);
    XtPopdown(menu5);
    XtPopdown(menu);
}

/*
 * menu pane button callback function
 */
/*ARGSUSED*/
void MainPaneChosen(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
    
    /* need some function here */
    writeout("MainPane  chosen.\n");

    XtPopdown(menu3);
    XtPopdown(menu4);
    XtPopdown(menu);
    XtPopdown(menu5);
}

void LibMenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
    int num = (int) client_data;

   switch(num) {
	case 0 :   break;    /* lib_load    -> */
	case 1 :   break;    /* lib_delete  -> */
	case 2 :   break;    /* lib_present -> */
	case 3 :   XtPopdown(menu5); XtPopdown(menu); strcpy((String)Choice1,"save");
                   strcpy((String)Choice2,"save");
		   libPlaceDialog(w);     
		   XtPopup(libDialogShell, XtGrabExclusive); break;
	case 4 :   XtPopdown(menu5); XtPopdown(menu); strcpy((String)Choice1,"set");
                   strcpy((String)Choice2,"set");
                   libPlaceDialog(w);
                   XtPopup(libDialogShell, XtGrabExclusive); break;
   }

}

void Lib2MenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
   int num = (int) client_data;
   String string[80];
   XtPopdown(menu5); 
   XtPopdown(menu);

  sprintf(string,"load_ind_plan(%d).\n", num - 9);
   switch(num){
	case 10 :  
    		  
	case 11 : 
    		 
	case 12 :  write_clam(string);
    		   AppendDialogText(string); break;

	default :  /*   libUpPop(w); */
   		   strcpy((String)Choice2,XtName(w));
    		   libPlaceDialog(w);
		   XtPopup(libDialogShell, XtGrabExclusive); break;
   }
}


void formatMenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
   String string[80];
   int num = (int) client_data ;

   if (status[num])
        XtVaSetValues(w,
                XtNleftBitmap, None,
                NULL);
    else
        XtVaSetValues(w,
                XtNleftBitmap, mark,
                NULL);

    status[num] = !status[num];
    sprintf(string,"toggle_format(%s).\n",XtName(w));
    write_clam(string);
    AppendDialogText(string);
}

void rippleMenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
   String string[80];
   int num = (int) client_data ;

   if (ripple_status[num])
        XtVaSetValues(w,
                XtNleftBitmap, None,
                NULL);
    else
        XtVaSetValues(w,
                XtNleftBitmap, mark,
                NULL);

    ripple_status[num] = !ripple_status[num];
    sprintf(string,"toggle_ripple.\n");
    write_clam(string);
    AppendDialogText(string);
}


void colourMenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{
   String string[80];
   int num = (int) client_data ;

   if (colour_status[num])
        XtVaSetValues(w,
                XtNleftBitmap, None,
                NULL);
    else
        XtVaSetValues(w,
                XtNleftBitmap, mark,
                NULL);

    colour_status[num] = !colour_status[num];
    sprintf(string,"toggle_colour.\n");
    write_clam(string);
    AppendDialogText(string);
}







void planMenuItem(w, client_data, call_data)
Widget w;
XtPointer client_data;
XtPointer call_data;
{    

      String string[80];

 XtPopdown(menu2); XtPopdown(menu7);
       if (strcmp((String)Choice3,"current") == 0){
           sprintf(string,"%s.\n",XtName(w));
	   AppendDialogText(string);
	   write_clam(string);

       }
       else {
	     strcpy((String)Choice4,XtName(w));
	     planUpPop(w); 

       }



}

/*
 * @(#)$Id: screen.c,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: screen.c,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

    if (app_resources.command_button_count > 0) 
	scrn->miscbuttons = BBoxCreate(scrn, "commandBox");

    /* the optional miscellaneous command buttons */

    if (app_resources.command_button_count > 0) {
	char	name[30];
	if (app_resources.command_button_count > 500)
	    app_resources.command_button_count = 500;
	for (i=1; i <= app_resources.command_button_count; i++) {
	    sprintf(name, "button%d", i);
	    BBoxAddButton(scrn->miscbuttons, name, commandWidgetClass, True);
	}
    }

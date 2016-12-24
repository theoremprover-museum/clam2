/*
 * @(#)$Id: global.h,v 1.1 1994/09/16 09:45:20 dream Exp $
 *
 * $Log: global.h,v $
 * Revision 1.1  1994/09/16 09:45:20  dream
 * Initial revision
 *
 */

#include <sys/file.h>
#include <stdio.h>
#include <X11/Intrinsic.h>
#include <X11/StringDefs.h>
#include <X11/Xaw/Form.h>
#include <X11/Shell.h>
#include <X11/Xaw/Command.h>
#include <X11/Xaw/Dialog.h>
#include <X11/Xmu/Xmu.h>
#include <X11/Xaw/Box.h>
#include <X11/Xaw/MenuButton.h>
#include <X11/Xaw/SimpleMenu.h>
#include <X11/Xaw/Sme.h>
#include <X11/Xaw/SmeBSB.h>
#include <X11/Xaw/Cardinals.h>
#include <X11/bitmaps/xlogo16>
#include <X11/Xaw/Text.h>
#include <X11/Xaw/AsciiText.h>
#include <X11/Xaw/AsciiSrc.h>
#include <X11/Xaw/TextSrc.h>
#include "mybits"	


#include "defs.h"

extern void CreateProofWindow();
extern void CreatePlanWindow();
extern void CreateDialogWindow();
extern void CreateDialog2Window();
extern void CreateRippleWindow();
extern void CreateCommandBox();
extern void CreateButtons();
extern void CreateOptionBox();
extern void Activate();
extern void AppendDialogText();
extern void MenuSelect();

extern void callclam();

extern void read_clam();

extern void trap_signals();
extern void redir_out();
extern void writeout();
extern void write_to();
extern void  CheckRightAndPopupSubmenu();
extern void  PlaceMenu();
extern void PopdownSubmenu();
extern void MainPaneChosen();
extern void SubPaneChosen();
extern void dialogReturn();
extern void dialogNewline();
extern void rippleNewline();
extern void libDialogNewline();
extern void  planDialogNewline();
extern  void LibMenuItem();
extern  void Lib2MenuItem();
extern  void planMenuItem();
extern void formatMenuItem();
extern void rippleMenuItem();
extern void colourMenuItem();
extern  void libupPop();
extern  void libPlaceDialog();
extern void upPop();
extern void unPop();
extern void pickout();
extern void ripple_output();
extern void ripple_clear();
extern void plan_clear();

extern Widget toplevel, planWindow, proofWindow, dialogWindow,dialog2Window, formWindow, commandBox,                   b1, b2, b3, b4,b5,b6,b7 ,menu ,menu2, menubox, menubox2, otherWindow, formWindow2 , otherWindow2, otherWindow3, dialogPopup, dialogShell , menu3, menu4, menu5, menu6, libDialogPopup, libDialogShell,
planDialogShell, planDialogPopup, menu7, rippleWindow, menu8, b8, colour_button;


extern FILE    *dbxfp;                 /* file pointer to dbx process */
extern Boolean FalseSignal;            /* real/false signal ? */
extern Display * display;

extern XtAppContext    app_context;
extern Boolean         ready; 
extern Widget          currentOutputWindow;
extern XawTextPosition  StartPos;

extern char * concat();
extern String Choice1[];
extern String Choice2[];
extern String Choice3[];
extern String Choice4[];
extern Boolean status[];
extern Boolean ripple_status[];
extern Boolean colour_status[];
extern Pixmap mark;
extern XFontStruct     *myfont;
extern int     dbxpid;                 /* clam process id */
static char PlanText[DIALOGSIZE];
extern struct _resources {
   int command_button_count;
} app_resources;

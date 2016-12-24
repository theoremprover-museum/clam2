/*
 * @(#)$Id: makeclam.pl,v 1.11 2008/05/21 14:14:13 smaill Exp $
 *
 * $Log: makeclam.pl,v $
 * Revision 1.11  2008/05/21 14:14:13  smaill
 * update for sicstus4
 *
 * Revision 1.10  1997/05/09 15:17:01  img
 * *** empty log message ***
 *
 * Revision 1.9  1997/05/08 12:48:39  img
 * Clam 2.6.2
 *
 * Revision 1.8  1996/06/19 11:24:02  img
 * clam_patchlevel_info/0: removed.
 *
 * Revision 1.7  1995/10/18  13:22:03  img
 * support for SWI prolog
 *
 * Revision 1.6  1995/10/17  19:23:48  img
 * Alter make structure to so that .sourcelist defines a predicate rather
 * than piping filenames into Prolog.  Up to version CLAM_2_4_1.
 *
 * Revision 1.5  1995/10/03  13:35:17  img
 * Clam version 2.4
 *
 * Revision 1.4  1995/07/19  14:24:44  img
 * mode to patchlevel info
 *
 * Revision 1.3  1995/07/18  09:54:53  img
 * clam_patchlevel_info/0 added
 *
 * Revision 1.2  1995/05/18  10:16:03  img
 * 	* New make arrangement that does not require cpp.  SWI is not
 * 	  really supported.
 *
 */

/* This file is a script for creating an executable image of CLaM.  */
:- dynamic compile_and_save_clam/1.

compile_and_save_clam(Type) :-
    dialect(qui),!,
    style_check(all),
    (Type = clamlib -> ['../dialect-support/qui/libs.pl']; true),
    consult('.sourcelist'),
    files_to_load(Files),
    loadc(Files),
    %% Construct banner, construct file name to save in, and save: 
    (Type = clamlib -> 
     (write('Saving core Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clamlib', "CLaM proof planner (core only)", clamlib),
	    halt)));
     (write('Saving Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clam', "Clam proof planner", clam))))).

compile_and_save_clam(Type) :-
    dialect(sic),!,
    prolog_flag(redefine_warnings,_,on),
    prolog_flag(single_var_warnings,_,on),
    (Type = clamlib -> ['../dialect-support/sic/libs.pl']; true),
    consult('.sourcelist'),
    files_to_load(Files),
    loadc(Files),
    %% Construct banner, construct file name to save in, and save: 
    (Type = clamlib -> 
     (write('Saving core Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clamlib', "CLaM proof planner (core only)", clamlib),
	    halt)));
     (write('Saving Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clam', "Clam proof planner", clam))))).

compile_and_save_clam(Type) :-
    dialect(swi),!,
    (Type = clamlib -> ['../dialect-support/swi/libs.pl']; true),
    consult('.sourcelist'),
    files_to_load(Files),
    loadc(Files),
    %% Construct banner, construct file name to save in, and save: 
    (Type = clamlib -> 
     (write('Saving core Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    retractall(files_to_load(_)),
	    save_clam('clamlib', "CLaM proof planner (core only)", clamlib),
	    halt)));
     (write('Saving Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    retractall(files_to_load(_)),
	    save_clam('clam', "Clam proof planner", clam))))).

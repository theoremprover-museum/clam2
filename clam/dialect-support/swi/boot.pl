/*
 * @(#)$Id: boot.pl,v 1.3 1997/05/08 12:52:45 img Exp $
 *
 * $Log: boot.pl,v $
 * Revision 1.3  1997/05/08 12:52:45  img
 * Update to version 2
 *
 * Revision 1.2  1995/04/25 10:08:09  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:21:46  dream
 * Initial revision
 *
 */
:- multifile file_version/1.
file_version('$Id: boot.pl,v 1.3 1997/05/08 12:52:45 img Exp $').

/*
 * This file contains predicates that need to be present before we can
 * run the make-scripts.
 * I guess their usual place would otherwise be in util.pl
 */
dialect(swi).
os(unix).

?- ensure_loaded(library(quintus)).
?- op(0,fx,~).
?- op(900,      fy,     [not]).

/* for SWI 2.x */
multifile_needed :- true.
?- set_feature(character_escapes,false).

if(X):-X,!.

% NOTE very weird form of conditional consulting predicates to suit
% quintus' pecadilloes.
% 
if(_) :- current_stream( _,_, S),!,
         ( retractall( if__ctr(_) ) ; true ),
        asserta( if__ctr( 1 ) ),
        'repeat',
         read(S,X),
         count__0(X),
         !.
if(_):- ( retractall( if__ctr(_) ) ; true ),
        asserta( if__ctr( 1 ) ),
        'repeat',
         read(X),
         count__0(X),
         !.

endif.

lib_include(_).

count__0((?-if(_))):-
    retract( if__ctr(PR) ),
    R is PR+1,
    asserta( if__ctr(R)),!,
    fail.
count__0((?-endif)):-
    retract( if__ctr(SR) ),
    R is SR-1,
    ( R = 0 -> true ; asserta( if__ctr(R) ), !,fail ).
count__0(end_of_file):-
    retract( if__ctr( _ ) ),
    asserta( if__ctr( 0 ) ).

/* the three predicates (load/1, reload/1 and time_stamp/1) are
 * part of the make-package. See util.pl for details.
 * IN SWI THIS IS REDUNDANT as it is built into the system...
 */
	% load/1 and reload/1 are as consult/1 and reconsult/1, except
	% that they store a stime stamp for the file.
	% Similarly, loadc/1 is like compile. 
load([]) :- !.
load([F|Fs]) :- !, load(F), load(Fs).
load(File) :- consult(File).
reload([]) :- !.
reload([F|Fs]) :- !, reload(F), reload(Fs).
reload(File) :- consult(File).
loadc([]) :- !.
loadc([F|Fs]) :- !, loadc(F), loadc(Fs).
loadc(File) :- consult(File).

reconsult(F) :- consult(F).

	% time_stamp(+File): produce a time stamp for File. If
	% necessary, throw away existing time stamp.
time_stamp(F) :-
    datime(D), absolute_file_name(F,File),
    (recorded(time_stamp,(File,_),R)->erase(R);true),
    recorda(time_stamp,(File,D),_).



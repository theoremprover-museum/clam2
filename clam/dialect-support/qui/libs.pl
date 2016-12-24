/* -*- Mode: Prolog -*-
 * @(#)$Id: libs.pl,v 1.14 1998/08/26 12:36:56 img Exp $
 *
 * $Log: libs.pl,v $
 * Revision 1.14  1998/08/26 12:36:56  img
 * use library(random)
 *
 * Revision 1.13  1998/07/27 12:16:41  img
 * Dialect support adjustments
 *
 * Revision 1.12  1997/11/06 15:59:15  img
 * lib_fname/4: treat * as special
 *
 * Revision 1.11  1997/10/09 17:02:33  img
 * lib_fname/2 added
 *
 * Revision 1.10  1997/05/09 09:29:20  img
 * Abstract div/3 to dialect-support.
 *
 * Revision 1.9  1997/05/08 12:53:36  img
 * Update to version 3
 *
 * Revision 1.8  1996/12/11 14:21:46  img
 * gracefull_abort/0 added.
 *
 * Revision 1.7  1996/07/09 15:38:46  img
 * load ordsets (was in so.pl)
 *
 * Revision 1.6  1996/06/19  11:22:38  img
 * clam_patchlevel_info/0: removed.
 *
 * Revision 1.5  1995/10/18  12:15:38  img
 * ocunifiable/2 changed to matches/2;  code moved from libs.pl into
 * util.pl
 *
 * Revision 1.4  1995/10/03  13:38:36  img
 * lib_dir_system/1 rather than lib_dir/1
 *
 * Revision 1.3  1995/07/18  14:17:03  img
 * print helpful message on startup
 *
 * Revision 1.2  1995/04/25  10:08:03  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:21:34  dream
 * Initial revision
 *
 */
:- multifile file_version/1.
file_version('$Id: libs.pl,v 1.14 1998/08/26 12:36:56 img Exp $').

%fix for the absolute path name problem
lib_fname(File, File2) :-
    absolute_file_name(File,File2).
lib_fname( '*', Object, Kind, FN ) :-		% system directory
    lib_dir_system(LibDir),
    absolute_file_name(LibDir,LD),
    concat_atom( [LD, '/', Kind, '/', Object ], FN ).
lib_fname( LibDir, Object, Kind, FN ) :-
    absolute_file_name(LibDir,LD),
    concat_atom( [LD, '/', Kind, '/', Object ], FN ).

ttywrite(X) :- write(user,X).
ask(X) :- get0(X), in_eoln(X).
in_eoln(10) :- !.
in_eoln(_) :- get0(X),in_eoln(X).

:- op(900,      fy,     [not]).
:- op(700,      xfx,    [\=]) ; true.

T1 \= T2 :- \+ T1 = T2.
not Goal :- \+ Goal.
do_subcall :-
    read(X),
    !,
    call(X),
    !,
    fail.    

uniq_id( X ) :-
     recorded( '@id_ctr@',X, Ref ),
     SX is X + 1,
     erase(Ref),
     recorda( '@id_ctr@', SX, _ ),
     !.
uniq_id( 1 ) :-
     recorda( '@id_ctr@', 1, _ ).

	% save_state(+String,+File) saves current program state in File. Next
	% time File is called, String will be printed as a banner,
	% followed by the time when the saved state was created.
        % third argument distinguishes between the differenet behaviours for
        % clam and clamlib, since clamlib does not load the needs file
save_state(String,File,clamlib) :-
    datime(date(Year,Month1,Day,Hour,Min,_)),
    Month is Month1+1,	% Quintus bug: Month is 1 down.
    name(Atom,String),
    (Hour<10->(Hc is Hour+48,H=[48,Hc]);H=Hour),
    (Min <10->(Mc is  Min+48,M=[48,Mc]);M=Min),
    concat_atom([Atom,' (',Day,'/',Month,'/',Year,' ',H,':',M,')'],Banner),
    save_program(File, (nl,write(Banner),nl,nl)).

save_state(String,File,clam) :-
    datime(date(Year,Month1,Day,Hour,Min,_)),
    Month is Month1+1,	% Quintus bug: Month is 1 down.
    name(Atom,String),
    (Hour<10->(Hc is Hour+48,H=[48,Hc]);H=Hour),
    (Min <10->(Mc is  Min+48,M=[48,Mc]);M=Min),
    concat_atom([Atom,' (',Day,'/',Month,'/',Year,' ',H,':',M,')'],Banner),
    save_program(File, (nl,write(Banner),nl,nl,
                        lib_dir_system(Dir),concat_atom([Dir,'/',needs],Needs),
			reconsult(Needs))).

save_clam(Name, Description, Type) :-
    clam_version(V),name(V,Vname), 
    append([Description, ", version ",Vname],Banner),
    dialect(D), concat_atom([Name, '.v', V, '.' ,D],LibFile),
    save_state(Banner,LibFile,Type).

:-       ensure_loaded(library(strings)),
	 ensure_loaded(library(directory)),
	 ensure_loaded(library(lists)),
         ensure_loaded(library(flatten)),
	 ensure_loaded(library(arg)),
	 ensure_loaded(library(occurs)),
	 ensure_loaded(library(findall)),
	 ensure_loaded(library(date)),
	 ensure_loaded(library(call)),
	 ensure_loaded(library(files)),
	 ensure_loaded(library(environ)),
         ensure_loaded(library(ordsets)),
         ensure_loaded(library(random)),        
	 ensure_loaded(library(sets)). % Already loaded by Oyster, but stated
                                       % here as well for completeness sake.

nth(1,[A|_],A).
nth(N,[_|As],A) :- nth(X,As,A), N is X + 1.

gracefull_abort :-
    close_all_streams,
    abort.

        %   between(+Lower, +Upper, ?Number)
        %   is true when Lower, Upper, and Number are integers,
        %   and Lower =< Number =< Upper.  If Lower and Upper are given,
        %   Number can be tested or enumerated.  If either Lower or Upper
        %   is absent, there is not enough information to find it, and an
        %   error will be reported.
        %
        % This predicate is lifted from the Quintus library between,
        % since it contains syntax errors and redefines repeat (sigh...).
between(Lower, Upper, Point) :-
        integer(Lower),
        integer(Upper),
        (   integer(Point), !,          %  These cuts must be cuts;
            Lower =< Point, Point =< Upper
        ;   var(Point), !,              %  they can't be arrows.
            Lower =< Upper,
            between1(Lower, Upper, Point)
        ).
between(Lower, Upper, Point) :-
        Goal = between(Lower,Upper,Point),
        must_be_integer(Lower, 1, Goal),
        must_be_integer(Upper, 2, Goal),
        must_be_integer(Point, 3, Goal).

        %%  between1(Lower, Upper, Point)
        %   enumerates values of Point satisfying Lower =< Point =< Upper,
        %   where it is already known that Lower =< Upper and Point was a
        %   variable.  A purer version of this is left as a comment.
between1(L, L, L) :- !.
between1(L, _, L).              % between1(L, U, L) :- L =< U.
between1(L, U, N) :-            % between1(L, U, N) :- L < U,
        M is L+1,               %       M is L+1,
        between1(M, U, N).      %       between1(M, U, N).


/*
 * The following predicates implement a "make" predicate: when files are
 * (re)consulted used (re)load, the system will store a time-stamp to
 * record the time when the file was loaded. The make/0 predicate will
 * compare the load-time time-stamp of each loaded file with the current
 * modification date of the file, and if the later is newer, reload the
 * file.
 * NOTE: this only works for files that have been loaded using the
 * (re)load/1 predicates (and not for files that have just been
 * (re)consulted.
 *
 * load/1, reload/1 and time_stamp/1 are defined in boot.pl
 */

        % make -Flag: make -i reloads files (interpreted) (the default).
        %             make -c recompiles files
        %             make -n finds out which files are to be reloaded,
        %                     but doesn't actually remake them.
        %             make    is shorthand for make -i.
        % Long live failure driven loops!
'make' :- make -i.
make(-n) :-
    recorded(time_stamp,(File,WhenLoaded),_),
    file_property(File,modify_time,WhenModified),
    WhenModified @> WhenLoaded,
    write(File),nl,
    fail.
make(Flag) :-
    (Flag == -i ; Flag == -c), 
    recorded(time_stamp,(File,WhenLoaded),_),
    file_property(File,modify_time,WhenModified),
    WhenModified @> WhenLoaded,
    (Flag = -i
     -> reload(File)
     ;  (/* Flag = -c, */ loadc(File))
    ),
    fail.
make( _) .


maplist(Pred, Olds, News) :-
        map_list_(Olds, News, Pred).

map_list_([], [], _).
map_list_([Old|Olds], [New|News], Pred) :-
        call(Pred, Old, New),
        map_list_(Olds, News, Pred).

maplist(Pred, Xs, Ys, Zs) :-
        map_list_(Xs, Ys, Zs, Pred).

map_list_([], [], [], _).
map_list_([X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, X, Y, Z),
        map_list_(Xs, Ys, Zs, Pred).

maplist(Pred, Ws, Xs, Ys, Zs) :-
        map_list_(Ws, Xs, Ys, Zs, Pred).

map_list_([], [], [], [], _).
map_list_([W|Ws], [X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, W, X, Y, Z),
        map_list_(Ws, Xs, Ys, Zs, Pred).

div(A,B,C) :- A is B div C.

concatenate_atoms(A,B) :-
    concat_atom(A,B).

abs(A,A):-A>0,!.
abs(A,B):-B is -A.


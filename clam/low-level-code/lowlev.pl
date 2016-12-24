/*
 * @(#)$Id: lowlev.pl,v 1.4 1997/01/14 10:50:02 img Exp $
 *
 * $Log: lowlev.pl,v $
 * Revision 1.4  1997/01/14 10:50:02  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:40  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:28  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: lowlev.pl,v 1.4 1997/01/14 10:50:02 img Exp $').

%*************
%*
%*   lowlev  -  A few useful low level predicates
%*
%*************

%select(A,S,R):-del(S,A,R).

rmember( E, [_|L] ) :-
    \+ L = [],
    rmember( E, L ).
rmember( E, [E|_] ).

filter( (V^P), [H|T], [H|R] ) :-
    \+ ( V=H,call( P )),
    !,
    filter( (V^P), T, R ).

filter( EP, [_|T], R ) :-
    filter( EP, T, R ).

filter( _, [], [] ).    


delete_first( [H|L],H,L ) :- !.
delete_first( [H|L], X, [H|D] ) :-
    delete_first( L,X, D ).
delete_first( [], _, [] ).


bak_abort :- true.
bak_abort :-
    nl,
    write( 'INTERNAL ERROR! SHould not have backtracked here!' ),
    nl,
    ((tactic_debug =: _, stopleap) ;abort),
    !.


stopleap.



   

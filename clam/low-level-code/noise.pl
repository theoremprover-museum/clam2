/*
 * @(#)$Id: noise.pl,v 1.4 1997/01/14 10:50:07 img Exp $
 *
 * $Log: noise.pl,v $
 * Revision 1.4  1997/01/14 10:50:07  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:43  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:31  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: noise.pl,v 1.4 1997/01/14 10:50:07 img Exp $').

%***************
%*
%*	noise - Module for diagnostic output
%*
%**************

noise( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.
noise( _, Mesg ) :-
    write( Mesg ),
    ttyflush,
    !.

noisenl( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.
noisenl( _, Mesg ) :-
    write( Mesg ),
    nl,
    !.

noisenl( L ) :-
    trace_plan(V,V),
    V < L,
    !.
noisenl( _ ) :-
    nl,
    !.
error( Mesg ) :-
    write( 'ERROR: ' ),
    write( Mesg ),
    nl,
    !.


noise_schema( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.

noise_schema( _, S) :- !,schema_list( S ).

schema_list( [ (H=>[Sb|RS]) | T ] ) :-
    write( '  ' ),
    write( H ),
    nl,
    write( ' => ' ),
    write( Sb ),
    nl,
    line_list( RS, 4),
    schema_list( T ).
schema_list( [] ).

noise_list( L, _ ) :-
    noise_level =: V,
    V < L,
    !.

noise_list( _, LL ) :-
    write( '[ ' ),
    line_list( LL, 2 ),
    write( ']' ).

line_list( [H|T], I ) :-
    tab(I),
    write( H ),
    nl,
    line_list(T, I ).
line_list( [], _ ).


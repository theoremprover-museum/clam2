/*
 * @(#)$Id: free_vars.pl,v 1.4 1997/01/14 10:49:56 img Exp $
 *
 * $Log: free_vars.pl,v $
 * Revision 1.4  1997/01/14 10:49:56  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:35  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:22  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: free_vars.pl,v 1.4 1997/01/14 10:49:56 img Exp $').

%***************
%*
%*      free_vars -  Work out the free variables of nurprl term,
%*                extended to allow unary defined terms.
%*
%*  free_vars(+Tm,-Vars) - Vars are the free variables in Tm.
%*  free_var(+Tm,?Var) - Var is free in Tm.
%*  nurprl_var(Tm)     - Tm is a nurprl variable
%*
%***************

/*
free_vars( Tm, Vars ) :-
    setof( Var, free_var(Tm,Var), Vars ),
    !.

free_vars( _, [] ).


free_var( V, _ ) :-
    var(V),
    !,
    fail.

free_var( term_of(_), _ ) :-
    !,
    fail.

free_var( {N}, _ ) :- 
    atom(N),
    !,
    fail.

free_var( atom(_), _ ) :-
    !,
    fail.

free_var( any(_), _ ) :-
    !,
    fail.

free_var( [H|T], Var ) :-               % *** Deal with variable binding terms
    !,                                  % ***  from decision and induction 
    append( BoundVars, [Term], [H|T] ), % *** terms
    free_var( Term, Var ),
    \+ member( Var, BoundVars ).

free_var( (_:T1#_), Var ) :-            % *** Deal with binding types
    free_var(T1,Var ).

free_var( (V:_#T2), Var ) :-
    !,
    free_var(T2,Var),
    \+ Var = V.

free_var( (_:T1=>_), Var ) :-
    free_var(T1,Var ).

free_var( (V:_=>T2), Var ) :-
    !,
    free_var(T2,Var),
    \+ Var = V.

free_var( ({_:T1\ _}), Var ) :-
    free_var(T1,Var ).

free_var( ({V:_\ T2}), Var ) :-
    !,
    free_var(T2,Var),
    \+ Var = V.


free_var( lambda(V,T), Var ) :-         % *** lambda term
    !,
    free_var( T, Var ),
    \+ V = Var.


free_var(Var,Var) :-                    % *** Variables
    nurprl_var(Var),
    !.


free_var( Tm, Var ) :-                  % *** Non-binding connectives etc
    Tm =.. [_|Args],
    member(Arg,Args),
    free_var( Arg, Var ).
*/

nurprl_var(Var) :-
                write( 'nurprl_var called' ),
                ttvar( Var ).

free_var( Tm, Var ) :-
          write( 'free_var called' ),
          freevarinterm( Tm, Var ).

free_vars( Tm, Vars ) :-
           write( 'free_vars called' ), 
           freevarsinterm( Tm, Vars ).

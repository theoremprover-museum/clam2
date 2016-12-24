/*
 * @(#)$Id: guess_type.pl,v 1.4 1997/01/14 10:49:58 img Exp $
 *
 * $Log: guess_type.pl,v $
 * Revision 1.4  1997/01/14 10:49:58  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:36  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:25  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: guess_type.pl,v 1.4 1997/01/14 10:49:58 img Exp $').

%**********************
%*
%*      guess_type - Module to support the guessing of term's types
%*                 under the assumption that they are well-formed,
%*                 and assuming the types of the variables present.
%*
%*  ENTRY POINTS: guess_conc_type, guess_typer
%*
%*
%**********************

:- lib_include( nested_ops ).
:- lib_include( library( types ) ).

%************
%*
%* guess_type( +Pure, ?VT, +Tm, ?Type )
%* - Under the assumption that VT is the pairing of variables and
%* their types in Tm and/or that Type is the type of Tm, VT is a
%* guess at the types of variables in Tm and/or Type is a guess at the
%* type of Tm
%*
%* If Pure is pure, only well-formed terms of the type theory 
%* are handled, otherwise abstract defined terms, and conditionals
%* are permitted.
%*
%************

guess_type( abstract, VT, Tm, Type ) :-
    guess_def_type(  VT, Tm, Type ).

guess_type( Pure, VT, Tm, Type ) :-
    guess_tt_type( Tm, Pure, VT,  Type ).


try_guess_type( Pure, VT, Tm, Type ) :-
    (guess_type( Pure, VT, Tm, Type );
     guess_type( Pure, VT, Tm, _ ); 
     true),
    !.



%*********
%*
%*  guess_conc_type( ?Hyps, +Tm, ?Type )
%*   - Guess a pure concrete type (i.e. no meta-variables may be present
%*   in the type guessed) using guess_type.   If the guess_type does
%*   not produce a concrete type try to make it concrete by unifying it
%*   against known concrete types in the Hypothesis list.  (Passed as
%*   a variable-type pairing).
%*
%*********

guess_conc_type( Hyps, Tm, Type ) :-
    guess_type( pure, Hyps, Tm, Type ),
    (ground(Type);(reverse(Hyps,RH),ground_against( Type,RH))).

ground_against( Hyp,[Hyp|_] ).
ground_against( Tm, [_:Hyp|_] ) :-
    ttsub_term( Hyp, Tm ).
ground_against( Hyp, [_|RestHyps] ) :-
    ground_against( Hyp, RestHyps ).



guess_def_type( _, Tm, _ ) :-
    var( Tm ),
    !.

guess_def_type( VT, (if B then Then else Else), T ) :-
    !,
    guess_type( abstract, VT, Then, T),
    guess_type( abstract, VT, Else, T ),
    try_guess_type( abstract, VT, B, unary\unary ).

guess_def_type( VT, Tm, Type ) :-

    % **** Find the relevant term definition (if present)

    def_appl(Name,SubTms,Tm),
     recorded_obj( Name, 
                  definition( _, _, AArgs, _, Dom ==> Range, _ ),
                  _ ),

    % **** Guess type of arguments and term as a whole taking into
    % **** account binding of type arguments.
    zip( Inst, AArgs, SubTms ),
    guess_def_arg_types( VT, SubTms, Inst, Dom),
    instantiated( Range, Inst, Type ).

guess_def_arg_types( _, [], _, [] ).
guess_def_arg_types( VT, [Arg|RestArgs], Inst, [_:ArgType|RestArgTypes] ) :-
    instantiated(ArgType, Inst, IArgType ),
    guess_type( abstract, VT, Arg, IArgType ),
    guess_def_arg_types( VT, RestArgs, Inst, RestArgTypes ).

    



%****************************
%*
%*      guess_tt_type -         Guess the type of proper terms of type
%*                      theory.
%*
%****************************


% **** Variables
guess_tt_type( V,_, VT,  T ) :- 
    ttvar( V ), 
    member( (V:T), VT ),
    !.


guess_tt_type( V,_, _,  _T ) :- 
    ttvar( V ),!.
guess_tt_type( V,_, _,  _ ) :-
    var( V ),
    !.

% **** Unary
guess_tt_type( unit,_, _,  unary ).
guess_tt_type( unary,_, _,  u(1) ).

guess_tt_type( axiom,_,_,  0 in pnat ).

% **** In the case where because is being used to bluff the system
% **** avoid being picky about the `bluff' extract term.
guess_tt_type( _,_, atom(incomplete), _ ).  

% **** Atom's
guess_tt_type( atom(_),_, _,  atom ).
guess_tt_type( atom_eq(L,R,A,B),Pure, VT,  T ) :-
    guess_type( Pure, VT,A,T1),
    guess_type( Pure, VT,B,T2),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, L, atom),
    try_guess_type( Pure, VT, R, atom).

guess_tt_type( atom,_, _,  u(1) ).

% **** extract terms

guess_tt_type( term_of(Name),_, _,  Type ) :-
    ctheorem(Name) =: problem([]==>Type,_,_,_).

% **** Void
guess_tt_type( void,_, _,  u(1) ).

% **** Pnat's
guess_tt_type( pnat,_, _,  u(1) ).
guess_tt_type( 0,_, _,  pnat ).
guess_tt_type( s(X),Pure, VT,  pnat ) :- guess_type( Pure, VT, X, pnat ).
guess_tt_type( p_ind(N,B,[V,R,S]),Pure, VT,  T ) :-
    guess_type( Pure, VT, B, T1 ),
    guess_type( Pure, [V:pnat,R:T|VT], S, T2 ),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, N, pnat).
guess_tt_type( cv_ind(N,[V,R,S]),Pure, VT,  T ) :-
    guess_type( Pure, [V:pnat,R:T|VT], S, T ),
    try_guess_type( Pure, VT, N, pnat).
guess_tt_type( pnat_eq(L,R,A,B),Pure, VT,  T ) :-
    guess_type( Pure, VT,A,T1),
    guess_type( Pure, VT,B,T2),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, L, pnat),
    try_guess_type( Pure, VT, R, pnat).

% **** Integers's 
guess_tt_type( int,_, _,  u(1) ).
guess_tt_type( N,_, _,  int ) :- number(N).
guess_tt_type( X+Y,Pure, VT,  int ) :-
    guess_type( Pure, VT, X, int ),
    guess_type( Pure, VT, Y, int ).
guess_tt_type( X*Y,Pure, VT,  int ) :-
    guess_type( Pure, VT, X, int ),
    guess_type( Pure, VT, Y, int ).
guess_tt_type( X/Y,Pure, VT,  int ) :-
    guess_type( Pure, VT, X, int ),
    guess_type( Pure, VT, Y, int ).
guess_tt_type( X-Y,Pure, VT,  int ) :-
    guess_type( Pure, VT, X, int ),
    guess_type( Pure, VT, Y, int ).
guess_tt_type( X mod Y,Pure, VT,  int ) :-
    guess_type( Pure, VT, X, int ),
    guess_type( Pure, VT, Y, int ).

guess_tt_type( ind(I,[V1,R1,S1],B,[V2,R2,S2]),Pure, VT,  T ) :-
    guess_type( Pure, VT, B, T1 ),
    guess_type( Pure, [V1:int,R1:T|VT], S1, T2 ),
    guess_type( Pure, [V2:int,R2:T|VT], S2, T3 ),
    unif_type( T1, T2, T4 ),
    unif_type( T3, T4, T ),
    (guess_type( Pure,VT,I,int);true).
guess_tt_type( int_eq(L,R,A,B),Pure, VT,  T ) :-
    guess_type( Pure, VT,A,T1),
    guess_type( Pure, VT,B,T2),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, L, int),
    try_guess_type( Pure, VT, R, int).

% **** Less
guess_tt_type( (L<R),Pure, VT,  u(1) ) :-
    try_guess_type( Pure, VT, L, int),
    try_guess_type( Pure, VT, R, int).

guess_tt_type( (L<*R),Pure, VT,  u(1) ) :-
    try_guess_type( Pure, VT, L, pnat),
    try_guess_type( Pure, VT, R, pnat).
guess_tt_type( axiom,Pure, VT,  (L<R) ) :-
    try_guess_type( Pure, VT, L, int),
    try_guess_type( Pure, VT, R, int).
guess_tt_type( axiom, Pure, VT, (L<*R) ) :-
    try_guess_type( Pure, VT, L, pnat),
    try_guess_type( Pure, VT, R, pnat).
guess_tt_type(  less(L,R,A,B), Pure, VT, T ) :-
    guess_type( Pure, VT,A,T1),
    guess_type( Pure, VT,B,T2),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, L, int),
    try_guess_type( Pure, VT, R, int).
guess_tt_type( pless(L,R,A,B),Pure, VT,  T ) :-
    guess_type( Pure, VT,A,T1),
    guess_type( Pure, VT,B,T2),
    unif_type( T1, T2, T ),
    try_guess_type( Pure, VT, L, pnat),
    try_guess_type( Pure, VT, R, pnat).

% **** List's
guess_tt_type( S list,Pure, VT,  U ) :-
    guess_type( Pure, VT, S, U ).

guess_tt_type( nil,_, _,  _ list).
guess_tt_type( Hd :: Tl,Pure, VT,  T list ) :- 
    guess_type( Pure, VT, Hd, T1 ),
    guess_type( Pure, VT, Tl, T2 list ),
    unif_type( T1, T2, T ).
guess_tt_type( list_ind(L,B,[Hd,Tl,R,S]),Pure, VT,  T ) :-
    try_guess_type( Pure, VT, L, T1 list ),
    guess_type( Pure, VT, B, T ),
    guess_type( Pure, [Hd:T1,Tl:(T1 list),R:T|VT], S, T).

% **** Union
guess_tt_type( (L \ R),Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, VT, R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).
guess_tt_type( inl(L),Pure, VT,  (T \ _) ) :-
    guess_type( Pure, VT, L, T ).
guess_tt_type( inr(R),Pure, VT,  (_ \ T) ) :-
    guess_type( Pure, VT, R, T ).
guess_tt_type( decide(U,[X,L],[Y,R]),Pure, VT,  T ) :-
    guess_type( Pure, VT,U,(LT \ RT) ),
    guess_type( Pure, [X:LT|VT], L, T1),
    guess_type( Pure, [Y:RT|VT], R, T2),
    unif_type( T1, T2, T ).

% **** Dependent Function
guess_tt_type( (V:L => R),Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, [V:L|VT], R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).
guess_tt_type( lambda(V,B),Pure, VT,  (VV:LT => RT) ) :-
    guess_type( Pure, [V:LT|VT], B, RT ),
    ( V = VV ; true ).
guess_tt_type( (F of V),Pure, VT,  T ) :-
    guess_type( Pure, VT, V, LT ),
    guess_type( Pure, VT, F, (X:LT=>RT) ),
    s( RT, [V], [X], T ).

% **** Function
guess_tt_type( (L => R),Pure, VT,  u(SN) ) :-
    guess_type( Pure, VT, L, u(SN) ),
    guess_type( Pure, VT, R, u(SN) ).

guess_tt_type( lambda(V,B), Pure, VT,  (LT => RT) ) :-
    guess_type( Pure, [V:LT|VT], B, RT).
guess_tt_type( (F of V),Pure, VT,  T ) :-
    guess_type( Pure, VT, V, LT ),
    guess_type( Pure, VT, F, (LT => T ) ).


% **** Product Types
guess_tt_type( (L # R),Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, VT, R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).
guess_tt_type( (L & R), Pure, VT, (LT # RT) ) :-
    guess_type( Pure, VT, L, LT ),
    guess_type( Pure, VT, R, RT ).
guess_tt_type( spread(P,[L,R,S]),Pure, VT,  T ) :-
    guess_type( Pure, VT, P, (LT # RT) ),
    guess_type( Pure, [L:LT,R:RT|VT], S, T ).

% **** Dependent Product Types
guess_tt_type( (V:L # R), Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, [V:L|VT], R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).
guess_tt_type( (L & R), Pure, VT,  (V:LT # RT) ) :-
    guess_type( Pure, VT, L, LT ),
    guess_type( Pure, [V:LT|VT], R, RT ).

% **** Quotient Type
guess_tt_type( L//[X,Y,R], Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, [X:L,Y:L|VT], R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).


% **** Subset Type
guess_tt_type( {X:L \ R}, Pure, VT,  u(Rs) ) :-
    guess_type( Pure, VT, L, u(A) ),
    guess_type( Pure, [X:L|VT], R, u(B) ),
    unif_type(u(A),u(B),u(Rs)).

% **** Membership and Equality

guess_tt_type( axiom,_, _,  (_ in _) ).
guess_tt_type( axiom,_, _,  (_=_ in _) ).
guess_tt_type( (L = R in T ), Pure, VT,  u(N) ) :-
    guess_type( Pure, VT,L, T),
    guess_type( Pure, VT,R, T),
    guess_type( Pure, VT, T, u(N) ).

guess_tt_type( (L in T ), Pure, VT,  u(N) ) :-
    guess_type( Pure, VT,L, _),
    guess_type( Pure, VT, T, u(N) ).


guess_tt_type( u(N),_, _,  u(SN) ) :-
    SN is N + 1.


% **** Recursive Types

guess_tt_type( rec(X,R), Pure, VT,  u(SN) ) :-
    guess_type( Pure, [X:u(SN)|VT], R, u(SN) ).
guess_tt_type( rec_ind(N,[R,V,S]), Pure, VT,  T ) :-
    guess_type( Pure, VT, N, RT ),
    guess_type( Pure, [V:RT,R:S|VT], S, T ).

% **** Proper definitions


guess_tt_type( {Name}, Pure, _,  Type ) :-
    !,
    cdef(Name) =: ({Name}<==>Body),
    guess_type( Pure,[],Body,Type).

guess_tt_type( Tm, Pure, VT,  Type ) :-
    !,
    Tm =.. [Name|Args],
    Args \= [],
    cdef(Name) =: (Head<==>Body),
    Head =.. [Name|FArgs],
    s( Body, Args, FArgs, IBody ),
    guess_type( Pure, VT, IBody, Type ).


unif_type( T,T,T).
unif_type( u(N1), u(N2), u(N) ) :-
    nonvar(N1),
    nonvar(N2),
    (N1<N2,N=N2;N=N1),
    !.


%**********************
%*
%*      ground_term/2, ground_term/3,
%*      ground_terms/2, ground_term/3
%*      -  Replate meta-variables (prolog variables)
%*      in a term with atoms (object variables).
%*
%*  NOTE: The /2 version use global unique integer for building names
%*        the /3 versions have one supplied as the second argument
%*
%*  reset_ground_var_num - Set global unique integer to 1.
%*
%***********************


reset_ground_var_num :-
    recorded(unique_num, _, Ref ),
    !,
    erase( Ref ),
    recorda( unique_num, 1, _ ).
reset_ground_var_num :-
    recorda( unique_num, 1, _ ).



ground_term( Nm, Tm ) :-
    (recorded( unique_num, N, R ) ; N=1,recorda( unique_num, N, R ) ),
    !,
    ground_term( Nm, N, NN, Tm ),
    erase( R ),
    recorda( unique_num, NN, _ ).

ground_terms( Nm, Tm ) :-
    (recorded( unique_num, N, R ) ; N=1,recorda( unique_num, N, R ) ),
    !,
    ground_terms( Nm, N, NN, Tm ),
    erase( R ),
    recorda( unique_num, NN, _ ).


ground_term( Nm, N, Tm ) :-
    ground_term( Nm, N, _, Tm ).
ground_terms( Nm, N, Tms ) :-
    ground_terms( Nm, N, _, Tms ).


ground_terms( _, N, N, [] ).
ground_terms( Nm, N, NNN, [H|T] ) :-
    ground_term( Nm, N, NN, H ),
    ground_terms( Nm, NN, NNN, T ).

ground_term( Nm, N, NN, V ) :-
    var(V),
    !,
    NN is N+1,
    name( N, ExpN ),
    name( Nm, ExpNm ),
    append( ExpNm, ExpN, ExpV ),
    name( V, ExpV ).

ground_term( Nm, N, NN, Tm ) :-
    Tm =.. [_|SubTms],
    ground_terms( Nm, N, NN, SubTms ).



%******************
%*
%*      meta_type_list - TList is a type binding list, MList is an
%*                     equivalent list with object variables replaced with
%*                     Prolog (meta) variables.
%*
%*******************

meta_type_list( TList, MList ) :-
    findall( Free, 
           (member(TBind,TList),freevarsinterm( TBind, Free )),
           VarSets ),
    VarSets \= [],
    union( VarSets, FreeVars ),
    zip( MetaInst, FreeVars, _MetaVars ),
    instantiated_list( TList, MetaInst, MList ).



%******************
%*
%*      univ_level - Guess the universe level of a term
%*
%******************

univ_level( Tm, N ) :-
    ttsub_term( Tm, u( L1 ) ),
    \+ ( ttsub_term( Tm, u( L2 ) ),
         L1 < L2
       ),
    !,
    N is L1+1.
univ_level( _, 1 ).

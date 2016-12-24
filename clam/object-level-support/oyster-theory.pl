/*
 * @(#)$Id: oyster-theory.pl,v 1.12 1999/05/19 15:58:15 julianr Exp $
 *
 * $Log: oyster-theory.pl,v $
 * Revision 1.12  1999/05/19 15:58:15  julianr
 * Added binary_function_on_type predicate to determine whether a
 * function is of type T => T => T' or not.
 *
 * Revision 1.11  1998/09/01 14:04:53  img
 * Type instances for u(_); dont randomize term instances
 *
 * Revision 1.10  1998/08/26 12:38:00  img
 * random_instance_of_type added (should be elsewhere?)
 *
 * Revision 1.9  1998/06/10 09:37:36  img
 * Binary relations.  Stuff for formula instantiation.
 *
 * Revision 1.8  1997/09/29 09:49:26  img
 * polarity_compatible/3
 *
 * Revision 1.7  1997/04/29 08:42:59  img
 * type_of/3: moved to oyster-theory from method_pre.
 *
 * Revision 1.6  1997/01/14 10:44:58  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.5  1996/12/06 14:49:24  img
 * no change
 *
 * Revision 1.4  1996/06/12  13:38:53  img
 * Support for <=>.
 *
 * Revision 1.3  1995/09/04  15:34:43  img
 * list_to_oyster_conjunction/2: make a Oyster product type from a list
 * of Oyster types.
 *
 * Revision 1.2  1995/05/17  02:18:51  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.1  1995/05/15  11:00:50  img
 * 	* Destined for theory-related stuff concerning Oyster
 *
 */

/* INCOMPLETE 
:- module(oyster_theory, [
		      ]).
*/

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: oyster-theory.pl,v 1.12 1999/05/19 15:58:15 julianr Exp $').

                      /* Oyster/theory related stuff */

/* type_of(+H,+Exp,?Type) guesses the type of Exp in context H.
   Current implementation relies on black magic from Jane's code to be
   found in tactics_wf.pl.  Jane's guess_type/2 sometimes returns the
   same type more then once on backtracking, so we squeeze out
   multiple same answers here using a setof (bit expensive, since this
   forces us to compute all guesses all the time (even if the first
   one is already correct), and we also rely on guess_type returning a
   finite number of answers, but I cant be bothered doing it any other
   way (is there any other way?)).  */
type_of(H,Exp,Type) :- findset(T,guess_type(Exp,H,T),Ts),member(Type,Ts).

?- dynamic transitive_pred/1.
/* transitive_pred(Exp, Sides, NewSides, NewWhole) succeeds if Exp is
 * a transitive function or connective Sides are the two sides of the
 * function whilst NewWhole is a template for a new instance of the
 * connective with sides NewSides.  NOTE: This is currently written in
 * the obvious hacky way.  It should eventually be based on the
 * recognition of transitivity lemmas.  */
transitive_pred( LR=RL in T, [LR,RL], [LRN,RLN], LRN = RLN in T).
transitive_pred( LR<=>RL, [LR,RL], [LRN,RLN], LRN <=> RLN).
transitive_pred( LR=>RL, [LR,RL], [LRN,RLN], LRN => RLN).
transitive_pred( Exp, [LR,RL], [LRN,RLN], Rebuild ) :-
    transitive_pred(P),
    Exp =.. [P,LR,RL],
    Rebuild =.. [P,LRN,RLN].
/* the following is a cheat
            geq(LR,RL)-geq(LRN,RLN),
            leq(LR,RL)-leq(LRN,RLN),
            greater(LR,RL)-greater(LRN,RLN),
           less(LR,RL)-less(LRN,RLN)  ]).
*/

/* canonical(Exp) checks whether a term Exp is canonical---i.e. built
 * up from the constructor functions of recursive data-types.
 * Implementation is highly hacky for efficiency.  */
canonical(E) :- var(E),!,fail.
canonical(Exp):-
    oyster_type( _, Constrs, Base ),
    (member(Exp,Base),! ;
    (member(Exp,Constrs);
    (functor(Exp,Constr,_),
     member(Constr,Constrs)))).

/* polarity(?O1,?O2,?F,?N,?P): Function F has polarity P in argument
 * number N under orderings O1 and O2.  F is positive in arg nr. N
 * under O1 and O2 if: O1(X1,X2) => O2(F(X1),F(X2)) where:
 * 
 * - X1 and X2 obey: exp_at(F(Xi),N,Xi), and
 * - O1 is a partial ordering on the domain of F (in ints Nt-th arg), 
 * - O2 is a partial ordering on the codomain of F.
 * 
 * A positive polarity means that F is monotonic in its Nth arg., a
 * negative polarity means that F is anti-monotonic in its Nth arg.  A
 * zero polarity means that F is neither monotonic nor anti-monotonic
 * in its Nth arg.
 * 
 * This is written using the auxiliary predicate plrty/5. This is the
 * lookup table for the polarity of all the functions.
 * 
 * The first clause of polarity/5 does straight table-lookup, and the
 * 2nd and 3rd clause apply the following transitivity rules for
 * polarity: + = [+|+] or [-|-] and - = [-|+] or [+|-] (compare rules
 * for multiplication)
 * 
 * Obviously, this table will need to be updated when we are adding
 * new functions, etc.
 * 
 * NOTE: I'm not alltogether sure of the status of the entries in the
 * lookup table. I guess, strictly speaking, CLaM should prove such
 * entries before they can be admitted in the table....  (See Blue
 * Book note 539 for more about this issue, and for a suggestion of
 * how this predicate should have been implemented (Actually, that
 * note suggests that this predicate has been implemented in the
 * appropriate way (namely as a special class of monotonicity
 * theorems), but (as can be seen here), this is not actually the case
 * (although it could have been done without too much trouble)))  */
polarity(X,X,_,[],+) :- !. % empty function is positive (think about it!)
polarity(O1,O2,F,N,S) :-
    plrty(F,O1,O2,N,S).
polarity(O1,O2,Exp,[P,Pos|List],+) :-
    exp_at(Exp,[Pos|List],SubExp),
    plrty(SubExp,O1,O,[P],Sign),
    polarity(O,O2,Exp,[Pos|List],Sign).
polarity(O1,O2,Exp,[P,Pos|List],-) :-
    exp_at(Exp,[Pos|List],SubExp),
    plrty(SubExp,O1,O,[P],OneSign),
    (OneSign = (+) -> OtherSign = (-) ; OtherSign = (+)),
    polarity(O,O2,Exp,[Pos|List],OtherSign).

        % simple arithmetic:
plrty(plus(_,_),leq,leq,[1],+).         plrty(plus(_,_),leq,leq,[2],+). 
plrty(exp(_,_),leq,leq,[1],+).          plrty(exp(_,_),leq,leq,[2],+).  
plrty(times(_,_),leq,leq,[1],+).        plrty(times(_,_),leq,leq,[2],+). 
plrty(minus(_,_),leq,leq,[1],+).        plrty(minus(_,_),leq,leq,[2],-).
plrty(double(_),leq,leq,[1],+).         plrty(half(_),leq,leq,[1],+).
plrty(fib(_),leq,leq,[1],+).            plrty(pred(_),leq,leq,[1],+).
plrty(length(_),_,_,[1],+).
        % max/min stuff:
plrty(max(_,_),leq,leq,[1],+).          plrty(max(_,_),leq,leq,[2],+).
plrty(max(_,_),geq,geq,[1],+).          plrty(max(_,_),geq,geq,[2],+).
plrty(min(_,_),leq,leq,[1],+).          plrty(min(_,_),leq,leq,[2],+).
plrty(min(_,_),geq,geq,[1],+).          plrty(min(_,_),geq,geq,[2],+).
        % propositional polarities:
plrty(_#_,=>,=>,[1],+).                 plrty(_#_,=>,=>,[2],+).
plrty(_:_#_,=>,=>,[2,2],+).             plrty(_:_#_,=>,=>,[1,2],+).
plrty(_\_,=>,=>,[1],+).                 plrty(_\_,=>,=>,[2],+).
plrty(_=>_,=>,=>,[2],+).                plrty(_=>_,=>,=>,[1],-).
plrty(_:_=>_,=>,=>,[2,2],+).            plrty(_:_=>_,=>,=>,[1,2],-).



        % predicates:
% plrty(member(_,_),_,_,_,+).
% plrty(even(_),_,_,_,+).
% plrty(leq(_,_),_,_,_,+).
% plrty(geq(_,_),_,_,_,+).
% plrty(greater(_,_),_,_,_,+).
plrty(_ = _ ,=>,=>,[1],+).
plrty(_ = _ ,=>,=>,[2],+).
plrty(_ = _ in _, =>, =>, [1],+).

        % apply{1,2} is interesting: it inherits its polarity from its
        % argument. 
plrty(apply1(_,_),_,_,[1],0).
plrty(apply1(F,_),O1,O2,[2],Sign) :- plrty(F,O1,O2,[1],Sign).
plrty(apply2(_,_,_),_,_,[1],0).
plrty(apply2(F,_,_),O1,O2,[2],Sign) :- plrty(F,O1,O2,[1],Sign).
plrty(apply2(F,_,_),O1,O2,[3],Sign) :- plrty(F,O1,O2,[2],Sign).

         % polarity_compatible/3 checks that the polarity of the 
         % expression at position Pos within Goal is compatible
         % with the rewrite directionality specified by Dir.
polarity_compatible(_,_,equ(_,_)) :- !.
polarity_compatible(_,_,equiv(_)) :- !.
polarity_compatible(Goal, Pos, Dir):-
    strip_meta_annotations(Goal, UnAnnGoal),
    polarity(=>, =>, UnAnnGoal, Pos, P),
    polarity_compat(Dir, P).

% polarity_compat(equ(_,_), _).  % dealt with by first clause of previous.
polarity_compat(imp(right), +).
polarity_compat(imp(left), -).

/* constant(?Term,?Type) succeeds if Term is an object-level term
 * which is a constant in Type.  Only useful mode is (+,?).  The
 * definition of constants is slightly different from the usual (which
 * are also called canonical constants).  For constants, we require
 * that they consist entirely of type constructors and type
 * base-elements, except for positions which are non-recursive in the
 * type constructors (the so called type parameters).  Example: Not
 * only is s(0)::nil constant (since it is canonical), but so is
 * x::nil (since x occurs in the non-recursive parameter position of
 * ::/2), but s(0)::x is not.  */
constant(0,pnat).
constant(s(X),pnat) :- constant(X,pnat).
constant(N,int) :- integer(N).
constant(N,int) :- var(N), genint(N).
constant(nil, _ list).
constant(_H::T,Type list) :-
    % Notice absence of: constant(_H,Type),
    constant(T,Type list).
constant(nil, _ nestedlist).
constant(inl(_)::T, Type nestedlist) :- constant(T, Type nestedlist).
constant(inr(H)::T, Type nestedlist) :-
    constant(H, Type nestedlist),
    constant(T, Type nestedlist).
constant(leaf(N),Type tree) :- constant(N,Type).
constant(tree(L,R),Type tree) :- constant(L,Type tree), constant(R,Type tree).
constant({true},u(1)).
constant(void,u(1)).
%? constant(T1,Type) :- eval(T1,T2), T1\=T2, constant(T2,Type).



/* build an Oyster product type from a list of meta-level terms.  If
 * ?List is nil then ?Conj is nil.  Otherwise, ?Conj is a product of
 * each element of ?List.  (Product associates to the right.)  */
list_to_oyster_conjunction([],[]).
list_to_oyster_conjunction(A,B) :-
    append(A0,[Last],A),
    foldr(A0,#,Last,B).

/* tidy access to ctheorem =: */
oyster_problem(T,Goal) :-
    ctheorem(T) =: problem(Goal,_,_,_).

current_problem(Thm) :-
    cthm=:Thm.

logic_functors(LF) :- oyster_functors( LF ).

        % oyster_type(?Type,?ConstructorList,?BaseElemList) is a reflection of
        % Oysters types: Type is a type with constructors as 
        % in ConstructorList and base elements as in BaseElemList.
        %
        % This is of course not complete and should be expanded as and
        % when needed.
        %
        % (Maybe we should even allow the use of this inside methods (in
        % which case it should move to method-pred.pl)).
/* 
 * The following clause is required to integrate Clam 
 * with Andrew Stevens shell mechanism.
 *
 * oyster_type( T, Constrs, BaseConstrs ) :-
 *   tuple( shell, [T,GndCnsts|_]),
 *   base_step_constrs( GndCnsts, T, Constrs, BaseConstrs ).
 *
 */
oyster_type(pnat,[s(_)],[0]).
oyster_type(_ list,[(_::_)],[nil]).
oyster_type(_ tree,[tree(_,_)],[leaf(_)]). 

base_step_constrs( [Con|RCons], T, [MCon|RSteps], Bases ) :-
    def_appl(Functor,Args,Con),
    member( _:T, Args ),
    !,
    lengtheq( Args,MArgs,_),
    def_appl(Functor,MArgs,MCon),
    base_step_constrs( RCons, T, RSteps, Bases ).
base_step_constrs( [Con|RCons], T, Steps, [MCon|RBases] ) :-
    cdef_appl(Functor,Args,Con),
    lengtheq( Args,MArgs,_),
    cdef_appl(Functor,MArgs,MCon),
    base_step_constrs( RCons, T, Steps, RBases ).
base_step_constrs( [], _, [], [] ).

/* T is an object-level term consisting of variables from V and constructor
   functions.  (V is a list of (variable or variable declaration).)
   */
constructor_term([],_).
constructor_term([T|Ts],V) :-
    !,
    constructor_term(T,V),
    constructor_term(Ts,V).
constructor_term(V,Vs) :- 
    (member(V,Vs); member(V:_,Vs)),!.
constructor_term(T,V) :-
    oyster_type(_,Step,Base),
    once((member(T,Base);member(T,Step))),
    T =.. [_|Args],
    constructor_term(Args,V).

/* make a disjunction from a list */
list2disj([],[]).
list2disj([C],C) :- !.
list2disj([C|Cs],C\CCs) :- list2disj(Cs,CCs).

instance_of_type(u(_),pnat).
instance_of_type(pnat,0).
instance_of_type(pnat,s(0)).
instance_of_type(int,0).
instance_of_type(int,-3).
instance_of_type(int,3).
instance_of_type(T list,E::nil) :-
    instance_of_type(T,E).
instance_of_type(T list,A::B::C::nil) :- 
    instance_of_type(T,A),
    instance_of_type(T,B),
    instance_of_type(T,C).
instance_of_type(_ list,nil).

/* When a definition and its associcated equations have been loaded,
   check to see if these are for a binary relation.  If so, try to
   demonstrate that the relation is transitive; if this succeeds,
   assert that fact so that weak fertilization (or whatever) can make
   use of it.  */
binary_relation_on_type(def(D),Dom) :-
    lib_present(synth(D)),!,
    recorded(theorem,theorem(D,synth,Type,_),_),
    binary_relation_on_type_(Type,Dom).

binary_relation_on_type(def(D),Dom) :-
    Term =.. [D,A,B],
    definition(Term<==>Cons),
    guess_type(lambda(A,lambda(B,Cons)),[],Type),!,
    binary_relation_on_type_(Type,Dom).

/* Type is of the form D=>D=>Prop (or the dependently typed form) or
   of the form (D#D)=>Prop.  */ 
binary_relation_on_type_(Type,D) :-
    ((Type = ((D#D)=>Prop)) orelse
	 (Type = (D=>D=>Prop)) orelse
	 (Type = (_:D=>_:D=>Prop)) orelse
	 (Type = (_:D=>D=>Prop)) orelse
	 (Type = (D=>_:D=>Prop))),
    Prop = u(_).

% binary_function_on_type(+D, -Type)
%
% Attempts to verify that D defines a binary function of Type T => T > T'.
%
binary_function_on_type(def(D),Type => Type => OType) :-
    lib_present(eqn(X)),
    DXY =.. [D,_XX, _YY],
    ctheorem(X) =: problem([] ==> _X:Type => _Y:Type => DXY = _RHS in OType, _, _, _),
    !.


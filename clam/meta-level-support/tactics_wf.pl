/*
 * @(#)$Id: tactics_wf.pl,v 1.21 1999/02/04 16:38:58 img Exp $
 *
 * $Log: tactics_wf.pl,v $
 * Revision 1.21  1999/02/04 16:38:58  img
 * wfftac1/1: shouldnt touch equality goals (?)
 *
 * Revision 1.20  1999/02/02 09:45:36  img
 * Revised wfftac to prevent application to Acc type membership goals.
 * int_or_pnat/1 -> int_or_pnat/2 to allow context to be used to decide
 * between pnat and int (unfinished).
 *
 * Revision 1.19  1999/01/07 16:33:02  img
 * guess_function_type/3: Guess the type of a function
 *
 * Revision 1.18  1998/06/10 08:08:40  img
 * improved type guessing with decision terms for less
 *
 * Revision 1.17  1998/05/13 13:01:10  img
 * guess_type/3 additions
 *
 * Revision 1.16  1998/03/25 10:26:06  img
 * use unification to do some type guessing
 *
 * Revision 1.15  1997/09/26 15:01:08  img
 * improvements (?) to wfftacs (mostly motivated by translation of McAllester corpus
 *
 * Revision 1.14  1997/06/05 10:35:00  img
 * Extensions to guess_type/3
 *
 * Revision 1.13  1997/01/14 10:44:31  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.12  1996/12/04 12:40:21  img
 * Wfftacs improvements.
 *
 * Revision 1.11  1996/07/10  09:46:57  img
 * guess_type/3: leave 0 case to int_or_pnat/1.
 *
 * Revision 1.10  1996/07/10  08:32:35  img
 * integer support added
 *
 * Revision 1.9  1996/07/09  14:51:01  img
 * guess_type/2 -> guess_type/3: new arguments is context.  This is an
 * improved version of type guessing, based on guess_type/2, but (i)
 * crazy bugs removed, and (ii) additional argument provides context that
 * can also be typed.  Use of meta_try/1 is an attempt to return as much
 * information about the type as possible.  For example, we have
 * guess_type(lambda(u,lambda(v,member(u,v))),[],int=>int list=>u(1)).
 *
 * wfftacs/0 has also been strengthed, exploiting new guess_type/3.
 *
 * non-wfftacs related code removed to tactics.pl from tactics_wf.pl.
 *
 * Revision 1.8  1996/06/18  17:19:41  img
 * Trivial cases for trees in wfftac.
 *
 * Revision 1.7  1996/06/11  16:41:32  img
 * Upgrades for rewriting using <=>.
 *
 * Revision 1.6  1996/06/06  11:17:09  img
 * rewrite_at_pos/4: Entry point for <=> rewriting added.
 *
 * Revision 1.5  1995/10/18  12:12:13  img
 * singleton variables removed
 *
 * Revision 1.4  1995/09/21  11:34:54  img
 * added better alignment of tactic/method for rewriting when fewer
 * variables appear on the right of a rule than on the left.  this arose
 * with weak-fertilization.
 *
 * Revision 1.3  1995/05/17  02:18:00  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:43  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: tactics_wf.pl,v 1.21 1999/02/04 16:38:58 img Exp $').

/*
 * This file contains most of the tactics to deal with wff-stuff (mostly
 * taken from Jane), plus some general tactic utilities (mostly taken
 * from AlanS).
 */

        % wfftacs_status/1 reports the status of wfftacs.
wfftacs_status(Status):-
    wfftacs_status =: Status.
        % wfftacs/1 enables the setting of wfftacs_status.
wfftacs(Status):-
    (Status = on; Status = off),
    wfftacs_status := Status.

/*=======================================================================
 * wrapper around select/1, to reset wfftac-value as appropriate
 * for the theorem to be selected.
 */

slct(Thm) :- select(Thm), set_wfftac.
slct :- select.


% The following is a short cut for debugging purposes (I havent got all day!)
% (We need one of the first two clauses, and always the third clause,
% The second clause obviously takes the shortcut).
wfftacs :- 
    wfftacs_status(on),
    repeat wfftac.
wfftacs :- wfftacs_status(off),
           wff_only, apply(because).
wfftacs.

set_wfftac :- remove_pred(wfftac,0),
              list_type(Type), !,
              assert((wfftac :- wfftac1(Type))).

set_wfftac :- remove_pred(wfftac,0),
              assert((wfftac :- wfftac2)).

wfftac1(Type) :- wff_only, sub_wfftac1(Type).
wfftac2 :- wff_only, sub_wfftac2.

%sub_wfftac1(_) :- wff_lemma.
sub_wfftac1(_) :- term_of_wfftac_applicable(L), !,
                     term_of_wfftac(L).
sub_wfftac1(_) :- compute([[unfold]] in _).
sub_wfftac1(_) :- list_intro.
%sub_wfftac1(_) :- product_intro.
sub_wfftac1(_) :- 
    goal(decide(A,_,_) in _),    hyp_list(H),
    guess_type(A,H,Type),
    intro(using(Type)).
sub_wfftac1(Type) :- intro(using(Type)).
sub_wfftac1(_) :- set_intro.
sub_wfftac1(_) :- intro.
sub_wfftac1(_) :- apply_wfftac.
sub_wfftac1(_) :- subsetlist_wfftac.
sub_wfftac1(_) :- unfold_dec.
sub_wfftac1(_) :- unfold_def_type.

%sub_wfftac2(_) :- wff_lemma.
sub_wfftac2 :- term_of_wfftac_applicable(L), !,
                     term_of_wfftac(L).
sub_wfftac2 :- compute([[unfold]] in _).
sub_wfftac2 :- product_intro.
sub_wfftac2 :- set_intro.
sub_wfftac2 :- 
    goal(decide(A,_,_) in _),    hyp_list(H),
    guess_type(A,H,Type),
    intro(using(Type)).
sub_wfftac2 :- intro.
sub_wfftac2 :- apply_wfftac.
sub_wfftac2 :- subsetlist_wfftac.
sub_wfftac2 :- unfold_dec.
sub_wfftac2 :- unfold_def_type.


wff_only :- goal(G), G= (F in Type), \+ Type = acc(_,_), F \= (_ = _).

eq_wff_subgoal :-
    hyp_list(H),
    goal(F of _=F of _ in _),
    guess_type(F, H,Ftype),
    ground(Ftype),
    intro(using(Ftype)) then [idtac,intro,idtac].


% extra for list_ind types:
%
list_intro :- goal(list_ind(L,_,_) in _),
              hypothesis(L:T list),
              intro(using(T list)).

product_intro :-
    goal(spread(E,_) in _),
    hyp_list(H),
    guess_type(E, H,A#B),
    ground(A#B),
    intro(using(A#B)).


/*=======================================================================
 * special purpose extension to wfftac to deal with wff goals of the
 * form x in T list where we know x in {subset of T} list.
 */
subsetlist_wfftac :-
    goal(Var in _ list),
    hypothesis(Var:{_:_\_} list),
    elim(Var).

set_intro :- 
	goal(_ in {_:_\_}),
        intro then [idtac, simplify then repeat (intro or intro(0)), idtac].


/*
 *  where elt is delared as in defined type:
 */

unfold_dec :- goal(El in _),
              (hypothesis(El:{_:_\_}) -> elim(El)
             ; hypothesis(El:{_}) -> compute(hyp(El),[[unfold]])
             ; hypothesis(El:{_} list) -> compute(hyp(El),[[unfold]] list)
             ; hypothesis(El:_ tree) -> compute(hyp(El),[[unfold]])
	     ; hypothesis(El:term_of(_) list) -> compute(hyp(El),[[1]] list)
             ; hypothesis(El:term_of(_)) -> compute(hyp(El),[[1]])).

unfold_def_type :- goal(_ in {_}),
                   compute(_ in [[unfold]]).
unfold_def_type :- goal(_ in _ tree),
                   compute(_ in [[unfold]]).

/*
  for function types with declaration possibly different from goal
*/

subrange_wfftac:- goal(T in (A=>_)),
                 ( hypothesis(T:A=>C); hypothesis(T:_:A=>C) ),
                   intro(using(A=>C)).


/*
  look out for hidden term_of type information first,
  rather than guessing function type
*/

apply_wfftac :-
    goal(F of _ in _),
    mark_termof_term(F,M),
    compute(M of _ in _).

apply_wfftac :-
    goal(F of X in T),
    hyp_list(H),
    meta_try guess_type(F, H,Domain=>_),
    meta_try guess_type(X, H,Domain),
    ground(Domain),
    /* new[_] required to force the correct Oyster rule to be applied.
       We do not want to apply rule for "F in (A=>B)" for F of the form
       "A of B".  */
    intro(using(Domain=>T),new[_]).

mark_termof_term(F of X,M of X) :- mark_termof_term(F,M).
mark_termof_term(F,[[1]]) :-
    functor(F,G,_),
    cdef(G)=:(_<==>Def),
    termof_term(Def).
termof_term(term_of(_)).
termof_term(F of _) :- termof_term(F).


/*=======================================================================
 * Contribution from AlanS:
 *  term_of_wfftac/0  should prove goals of the form
 *  ((..term_of(t) of a of b ...)of n) in type
 *  (requires theorem t to be loaded)
 */ 


%  first, a free-standing version
term_of_wfftac :- goal(term_of(T) in Type), !, 
                  ctheorem(T) =: problem(_==>ThmType,_,_,_),
                 (convertible(Type,ThmType) -> intro
                  ; intro(using(ThmType)) then [idtac,intro,idtac]).
term_of_wfftac :- goal(Goal),
           term_goal(Goal,Theorem,Arglist),
           ctheorem(Theorem) =: problem(_==>ThmType,_,_,_),
           find_prefix(ThmType,Arglist,PrefixList),
           apply_wfftac(PrefixList).

% now, as used in wfftac
term_of_wfftac_applicable(PrefixList) :- goal(Goal),
           term_goal(Goal,Theorem,Arglist),
           (ctheorem(Theorem) =: problem(_==>ThmType,_,_,_)
               -> find_prefix(ThmType,Arglist,PrefixList)
           ; (write('Theorem '),write(Theorem),
              write(' should be loaded!'),nl,
              PrefixList=missing_thm)).


% first clause to deal with cumulativity of universes
term_of_wfftac([]) :-
                   goal(term_of(Thm) in u(I)),
                   theorem(Thm,u(J),_),
                   J<I,
                   intro(u(J)) then intro.
term_of_wfftac([]) :- goal(term_of(T) in Type), !, 
                   ctheorem(T) =: problem(_==>ThmType,_,_,_),
                 (convertible(Type,ThmType) -> intro
                  ; intro(using(ThmType)) then [idtac,intro,idtac]).
term_of_wfftac(L) :- apply_wfftac(L).

term_goal(Goal,Theorem,Arglist):-
           term_goal4(Goal,Theorem,[],Arglist).
term_goal4(term_of(Theorem) in _,Theorem,Arglist,Arglist).
term_goal4(X of A in Type,Theorem,Acc,Arglist) :-
           term_goal4(X in Type,Theorem,[A|Acc],Arglist).

find_prefix(ThmType,Arglist,PrefixList):-
           find_prefix4(ThmType,Arglist,[],PrefixList).
find_prefix4(_,[],PrefixList,PrefixList).
find_prefix4(A=>B,[_|T],L,PrefixList):-
           find_prefix4(B,T,[A=>B|L],PrefixList).
find_prefix4(X:A=>B,[H|T],L,PrefixList):-
           s(B,[H],[X],BB),
           find_prefix4(BB,T,[X:A=>B|L],PrefixList).


/* The wrinkle here is to deal with cumulativity of universes.  This
   should be done uniformly for dependent and independent function
   types, but the Oyster rules as they stand make this hard.  */

apply_wfftac([]) :- intro.
apply_wfftac([X:T=>Y|R]) :- 
           hyp_list(H), hypfree([V],H),
           s(Y,[V],[X],YY),
           ((YY=u(I),goal(_ in u(J)), I<J) -> intro(u(I)) ; apply(idtac)) then
           intro(using(X:T=>Y),over(V,YY)) then
             [try apply_wfftac(R),
               repeat intro,repeat intro].
apply_wfftac([T=>Y|R]) :- 
           intro(using(T=>Y),new[_]) then
             [try apply_wfftac(R),
               repeat intro, repeat intro].
apply_wfftac(missing_thm).

:- dynamic type_declaration/2.
declared_type(F,Type) :-
    retractall(type_declaration(F,_)),
    assert(type_declaration(F,Type)).

guess_function_type(Fterm,Dom,Rng) :-
    Fterm =.. [F|Args],
    same_length(Args,SkelArgs),
    make_ground(SkelArgs),
    zip(DS,SkelArgs,Dom),
    map_list(DS,(A-B) :=> (A:B),true,DSS),
    Fskel =.. [F|SkelArgs],
    guess_type(Fskel,DSS,Rng).



/* Type guessing.  Used by wfftacs and (for example) by generalise
   methods.  */
guess_type([],_,[]).
guess_type([H|T],Hyps,[Ty|Tys]) :-
    guess_type(H,Hyps,Ty),!,
    guess_type(T,Hyps,Tys).
guess_type(Var,_,_) :-
    var(Var),!.
guess_type( T,_,Type) :-
    type_declaration(T,Type),!.
guess_type(X, H,XType) :-
    member(X:XXType,H),
    unify(XXType,XType),!.
guess_type(X, H,_) :-
    X =.. [F|_],
    memberchk(F:rectype,H).
guess_type(u(N), _Hs, u(_)) :-
    var(N),!,fail.
guess_type(u(N), _Hs, u(M)) :-
    var(M),!,
    M is N + 1.
guess_type(u(N), _Hs, u(M)) :-
    M > N.
guess_type(A = B in Type, Hs, u(N)) :-
    !,
    ((\+ var(Type),Type = u(I)) -> N is I + 1; N = 1),
    meta_try guess_type(A,Hs,Type),
    meta_try guess_type(B,Hs,Type).    
guess_type( unit,_H,unary).
guess_type({F}, H,XType) :-
    definition({F} <==>  RHS),			% overlaps with defn clause below
    \+ (RHS = {undef}),
    rewrite({F}, UnfoldedF),
    guess_type(UnfoldedF, H,XType).
guess_type(s(T),H,pnat) :-
    !,meta_try guess_type(T, H,pnat).
guess_type((H::T),Hyp,Type list) :-
    !,
    meta_try guess_type(H, Hyp,Type),
    meta_try guess_type(T, Hyp, Type list).
guess_type(-U,H, int) :-
    meta_try guess_type(U,H,int).    
guess_type(I,_,int) :-
    \+ I = 0,					% leave to int_or_pnat
    integer(I),!.
guess_type(Int,H, int) :-
    member(Int,[(U+V),(U-V), (U*V), (U/V), (U mod V)]),
    meta_try guess_type(U,H,int),
    meta_try guess_type(V,H,int).

guess_type(X, Hyps,XType) :-
    guess_immediate_type(X,Hyps,XType).
% next by trying obvious values (only for monadic functors)
/* this clause behaves badly on universe terms.i */
%%% guess_type(X, H,XType):-
%%%     X=..[F,A],
%%%     guess_type(A, H,AT),
%%%     guess_immediate_type(I,AT),
%%%     ground(I),
%%%     Y=..[F,I],eval(Y,YY), not YY=X,
%%%     /* and we don't want to loop! */
%%%     \+ functor(YY,F,1),
%%%     guess_type(YY, H,XType),!.

guess_type(if(B,C,D),H,T) :-
    !,
    meta_try guess_type(B, H,u(_)),
    guess_type(C,H,T),
    ((\+ var(T),T=u(_)) -> guess_type(D,H,u(_));	% only want Prop
     guess_type(D,H,T)).

guess_type( lambda(V,Term),H, Vt => TermType) :-
    guess_type(Term, [V:Vt|H],TermType).
guess_type( inl(T),H,L\_) :-
    guess_type(T,  H,L).
guess_type( inr(T),H,_\R) :-
    guess_type(T,  H,R).
guess_type(spread(E,[X,Y,Z]),H,T) :-
    guess_type(E, H,A#B),
    guess_type(Z,[X:A,Y:B|H], T).
guess_type(decide(E,[A,B],_),H,T) :-
    meta_try guess_type(E, H,F\_),
    guess_type(B,[A:F|H], T).
guess_type(decide(E,_,[C,D]),H,T) :-
    meta_try guess_type(E, H,_\G),
    guess_type(D,[C:G|H], T).

guess_type(A&B,H,At#Bt) :-
    meta_try guess_type(A, H,At), meta_try guess_type(B, H,Bt).
guess_type(p_ind(L,B,[X,Y,S]),H,Type) :-
    tryto guess_type(L, H, pnat),
    tryto guess_type(B, H,Type),
    tryto guess_type(S,[X:pnat,Y:RType|H], RType),
    \+ var(RType),
    unify(RType,Type),!.

guess_type(pless(A,B,R,S),H,Type) :-
    tryto guess_type(A, H, pnat),
    tryto guess_type(B, H, pnat),
    tryto guess_type(S,[A:pnat,B:pnat|H], SType),
    tryto guess_type(R,[A:pnat,B:pnat|H], Type),
    \+ var(SType),    \+ var(Type),
    unify(Type,SType),!.

guess_type(less(A,B,R,S),H,Type) :-
    tryto guess_type(A, H, int),
    tryto guess_type(B, H, int),
    tryto guess_type(S,[A:int,B:int|H], SType),
    tryto guess_type(R,[A:int,B:int|H], Type),
    \+ var(SType),    \+ var(Type),
    unify(Type,SType),!.

guess_type(list_ind(L,B,[X,Y,Z,S]),H,Type) :-
    meta_try guess_type(L, H, El list),
    tryto guess_type(B, H, Type),
    tryto guess_type(S,[X:El,Y:El list,Z:RType|H], RType),
    \+ var(RType),
    unify(RType,Type),!.
guess_type(ind(A,[X,Y,S],B,[U,V,T]),H,Type) :-
    meta_try guess_type(A,H,int),
    tryto guess_type(B,H,Type),
    tryto guess_type(S,[X:int,Y:SType|H],SType),
    \+ var(SType),
    meta_try guess_type(T,[U:int,V:TType|H],TType),
    \+ var(TType),
    unify(SType,TType),!.
	       
guess_type(term_of(Thm),_,Type) :-
    ctheorem(Thm) =: problem(_ ==>Type,_,_,_),!.
guess_type( _ in Type,_,XType) :-
    super_type(Type,XType).   
guess_type(lambda(U,F) of G,H,Type) :-
    !,
    s(F,[G],[U],FF),
    guess_type(FF,H,Type).
guess_type(F of Arg,H,DP) :-
    %% Account for dependant and independant types
    /* obviously, this does not do any real type checking here */
    guess_type(F,  H,FType),
    /* polymorphic definitions may have an {undef} type argument (this
    is to simplify the addition of such definitions).  In these
    cases, we proceed with a type variable.   */
    (Arg == {undef} -> RealArg = _; RealArg = Arg),
    once(((unify(FType, (V:Domain=>CoDomain)),	%dep function space
	   replace_all(V,RealArg,CoDomain,DP));
	  unify(FType, (Domain=>DP)))),!,		%fn space
    meta_try guess_type(RealArg, H, Domain).
    
/*guess_type(F of Arg,H,XType) :-
    \+ noprove =: _,
    eval(F of Arg,Y), (F of Arg) \= Y,
    guess_type(Y,  H,XType).
*/
guess_type(pnat_eq(A,B,S,T),H,Type) :-
    meta_try guess_type(A,H,pnat),
    meta_try guess_type(B,H,pnat),
    meta_try guess_type(S,H,Type),
    meta_try guess_type(T,H,Type).   
guess_type(int_eq(A,B,S,T),H,Type) :-
    meta_try guess_type(A,H,int),
    meta_try guess_type(B,H,int),
    meta_try guess_type(S,H,Type),
    meta_try guess_type(T,H,Type).   

guess_type(Ty,  H,u(UU)) :-
    member(Ty,[(A\B), (A#B), (A=>B), (_:A=>B), (_:A#B)]),
    meta_try guess_type(A, H,At),
    meta_try guess_type(B, H,Bt),
    ((At = u(Auu),\+ var(Auu)) -> Au is Auu + 1 ; Au = 0),
    ((Bt = u(Buu),\+ var(Buu)) -> Bu is Buu + 1 ; Bu = 0),
    max([Au,Bu],U),
    U = UU.
guess_type(X, H,XType) :-
    functor(X,F,N),
    definition(F/N <==>  RHS),
    \+ (RHS = {undef}),
    rewrite(X, UnfoldedX),
    guess_type(UnfoldedX, H,XType).

/* try to guess from RHS of equations 
guess_type(Term, _Hs, Ty) :-
    compound(Term),
    Term =.. [F|Args],
    lengtheq(Args,As),
    Skel =.. [F|As],
    rewrite_rule(Skel,_RHS,_Cond,TypeDir,_,_),
    (TypeDir = equ(Ty,_);
     ((TypeDir = equiv(_);TypeDir = imp(_)), Ty=u(1))),
    true.
*/
    /* attempt to guess the types of the arguments */
/*    metavars(Skel,MVs),
    untype(MVTs,MVs),
    make_ground(Skel),
    append(MVTs,Hs,HHs),
    meta_try guess_type(Cond,HHs,u(_)),
    meta_try guess_type(RHS,HHs,Ty),
    zip(Z,As,Args),
    guess_type_map(Z,HHs).*/

/* try to show that pairs have the same type */
guess_type_map([],_).
guess_type_map([A-B|Z],HHs) :-
    meta_try (guess_type(A,HHs,Typ),
	      guess_type(B,HHs,Typ)),
    guess_type_map(Z,HHs).    
guess_immediate_type(0,Hyps,T) :- !,int_or_pnat(Hyps,T).
guess_immediate_type(s(_),_,pnat) :- !.
guess_immediate_type(nil, _,_ list) :- !.
guess_immediate_type(void,_,u(1)).
guess_immediate_type({true},_,u(1)).
guess_immediate_type(int,_,u(1)).
guess_immediate_type(pnat,_,u(1)).
guess_immediate_type(_ list,_,u(1)).


super_type(pnat,u(1)).
super_type(_ list,u(1)).
super_type(int,u(1)).
super_type(pnat,u(1)).
super_type(u(I),u(J)) :- !,J is I + 1.
super_type(_,u(1)).                           % yuk

guess_def_types(LHS,VarTypes):-
    LHS =.. [F|Vs],
    definition(LHS <==> RHS),
    \+ (RHS = {undef}),				% ** HACK **
    guess_def_types(Vs,F,RHS,VarTypes).

guess_def_types([],_,_,[]).
guess_def_types([V|Vs],F,RHS,[type(V,Type)|Types]):-
    guess_def_type(V,F,RHS,Type),
    guess_def_types(Vs,F,RHS,Types).

% New clause added by frankh: if RHS is a list_ind term and we are
% guessing the type of the inductive variable, then try to guess the
% type of the head-variable in the inductive term and stick 'list' at
% the end of it.
guess_def_type(V,_,list_ind(V,_,[H,_,_,Step]),Type list) :-
    		    guess_def_type(H,_,Step,Type).
/*
% New clause added by frankh: temporarily removed since not needed (yet)
% Try to guess type of inductive variable by guessing the type of the
% predecessor in the recursive term. First two conjuncts check if RHS is
% an induction functional with V as the inductive variable. Then find
% the predecessor variable using recursive_arg_with_same_type_as_ind_var/2,
% and guess its type.
guess_def_type(V,_,RHS,Type) :-
    		    analyse_induction_functional(RHS,[_|Steps]),
                    RHS =.. [_,V|_],
		    member(Step,Steps),
		    recursive_arg_with_same_type_as_ind_var(RHS,Arg),
		    guess_def_type(Arg,_,Step,Type).
*/
% rest of clauses from Jane.
guess_def_type(V,_,RHS,Type) :-
                    RHS =.. [IndType,V|_],             % induction variable
                    induction_type_over(IndType,Type), !.
guess_def_type(V,_,RHS,Type) :-                        % explicit value of fn
                    analyse_induction_functional(RHS,Outputs),
		    member(V,Outputs),
		    guess_immediate_type(RHS,Type)/*, !*/.
guess_def_type(V,_,RHS,Type) :-                        % other variables
                    sub_term(RHS,X),
		    (X = ( V = _ in Type)
		    ;X = ( _ = V in Type)
                    ;(X =.. [Functor|Args],
                      nth1(N,Args,V),
		      def_arg_type(Functor,N,Type))).

induction_type_over(p_ind,pnat).
induction_type_over(ind,int).
induction_type_over(list_ind,Type) :- list_type(Type).

analyse_induction_functional(p_ind(_,B,[_,_,S]),[B,S]).
analyse_induction_functional(list_ind(_,B,[_,_,_,S]),[B,S]).
analyse_induction_functional(ind(_,[_,_,S1],B,[_,_,S2]),[B,S1,S2]).

% Added by frankh to support extra clause for guess_def_type.
recursive_arg_with_same_type_as_ind_var(p_ind(_,_,[V,_,_]),V).
recursive_arg_with_same_type_as_ind_var(list_ind(_,_,[_,V,_,_]),V).
recursive_arg_with_same_type_as_ind_var(ind(_,[V,_,_],_,_),V).
recursive_arg_with_same_type_as_ind_var(ind(_,_,_,[V,_,_]),V).

def_arg_type(s,_,pnat):- !.
def_arg_type('::',1,Type):- !, list_type(Type list).
def_arg_type('::',2,Type):- !, list_type(Type).
def_arg_type(F,N,Type):-
    definition(F/A <==> _), functor(X,F,A),
    definition(X <==> Y),
    type_of_nth_arg_of_term(N,X,Y,Type).

type_of_nth_arg_of_term(N,Left,Right,Type):-
    Left =.. [F|Args],
    nth1(N,Args,V),
    guess_def_type(V,F,Right,Type).

% find highest mentioned universe 

top_univ_level(Term,I) :- top_u_level([Term],1,I).
top_u_level([],I,I).
top_u_level([u(J)|R],I,K) :- !, II is max(I,J),
                             top_u_level(R,II,K).
top_u_level([H|T],I,K) :- atom(H), !,top_u_level(T,I,K).
top_u_level([H|T],I,K) :- H=..[_|Args], append(Args,T,TL),
                          top_u_level(TL,I,K).



list_type(Type list) :-
    do_list_type(Type1),
    ((Type1 = {_:Type\_},!)
     ;
     Type1 = Type
    ).
do_list_type(Type) :- goal(G),
                        hyp_list(H),
                        ((appears(Type list,allof(G,H)),!) ;
                         (appears(list_ind,allof(G,H)),
			  sub_term(_:R,G),
			  R =.. [=>,Type,_],
			  !)).
/* this is awful!
int_or_pnat(NumType) :-
             goal(G),
             hyp_list(H),
	     ((appears(pnat,allof(G,H)), NumType = pnat, !)
	       ; (appears(int,allof(G,H)), NumType = int, !)),!.
*/
int_or_pnat(_,int).
int_or_pnat(_,pnat).

get_base_value(p_ind,0).
get_base_value(ind,0).
get_base_value(list_ind,nil).


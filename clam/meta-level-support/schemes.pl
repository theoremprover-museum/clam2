/*
 * @(#)$Id: schemes.pl,v 1.34 1998/07/27 12:12:38 img Exp $
 *
 * $Log: schemes.pl,v $
 * Revision 1.34  1998/07/27 12:12:38  img
 * Conditional tracing messages
 *
 * Revision 1.33  1998/03/25 10:31:49  img
 * revert to v1.31
 *
 * Revision 1.31  1997/11/08 12:20:23  img
 * cosmetic changes
 *
 * Revision 1.30  1997/10/17 17:14:14  rjb
 * Fixed bug and comments.
 *
 * Revision 1.29  1997/10/17 15:02:56  rjb
 * Added source of induction scheme to apply_scheme and scheme predicates.
 *
 * Revision 1.28  1997/09/26 14:52:59  img
 * add_induction_scheme/1 and construct_scheme/3 added
 *
 * Revision 1.27  1997/07/09 15:18:11  img
 * typo
 *
 * Revision 1.26  1997/06/05 10:36:36  img
 * scheme/3: use recorded database
 *
 * Revision 1.25  1996/12/12 12:41:21  img
 * Error message predicates.
 *
 * Revision 1.24  1996/12/04 12:32:25  img
 * Abstract annotation.  Simplify the induction hypothesis markers, and
 * give each its own marker.
 *
 * Revision 1.23  1996/07/09 14:44:37  img
 * well_annotated/1 removed due to inappropriate behaviour: reimplemented
 * in schemes.pl.
 *
 * Revision 1.22  1996/06/18 17:07:29  img
 * use clam_error/2 for error messages
 *
 * Revision 1.21  1996/05/24 09:24:26  img
 * Warnings about singleton variables proved too much
 *
 * Revision 1.20  1996/04/09 14:35:53  img
 * typos
 *
 * Revision 1.19  1995/12/12 17:54:46  img
 * list induction exposing car and cadr of list; typo in {posint}
 * induction removed.
 *
 * Revision 1.18  1995/11/28 20:19:17  img
 * difference matching repaired
 *
 * Revision 1.17  1995/10/18 12:12:02  img
 * singleton variables removed
 *
 * Revision 1.16  1995/10/03 13:25:17  img
 * New scheme representation/manipulation.
 *
 * Revision 1.15  1995/09/25 15:56:43  img
 * incremental commit: induction ind_pre/scheme/tactic not implemented
 * correctly
 *
 * Revision 1.14  1995/09/21 11:36:00  img
 * totally new induction scheme mechanism
 *
 * Revision 1.13  1995/09/04 17:40:04  img
 * Removed sinks from base-cases of inductions (problem arises with nested
 * inductions).
 *
 * Revision 1.12  1995/05/17 02:17:54  img
 * Conditional multifile declaration (for Quintus).
 *
 * Revision 1.11  1995/05/15 17:29:58  img
 * delete_delete -> delete
 *
 * Revision 1.10  1995/05/15 14:17:38  img
 * variable naming problem fixed---need matrix variables to be
 * considered when naming the induction hypothesis since the
 * tactic does this too (not sure why this has not been a
 * problem before see eg. apprev)
 *
 * Revision 1.9  1995/05/12 15:49:14  img
 * datatype shell stuff removed
 *
 * Revision 1.8  1995/05/12 15:48:14  img
 * junk removed;  tidied
 *
 * Revision 1.7  1995/05/10 03:20:34  img
 * remove exisiting sinks prior to inserting new sinks
 *
 * Revision 1.6  1995/03/01 04:14:37  img
 * Added file_version/1 and associated multifile declaration
 *
 * Revision 1.5  1995/02/28 00:25:01  img
 * put initial annotation into normal form
 *
 * Revision 1.4  1995/02/10 10:47:18  img
 * check for presence of induction scheme before using it
 *
 * Revision 1.3  1994/10/04 23:42:26  dream
 * fixed bug in scheme for structural induction over 2-trees
 *
 * Revision 1.2  1994/09/16 10:53:22  dream
 * made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16 09:18:22  dream
 * Initial revision
 *
 */

/* Induction scheme material */

/* (The following comments pertain to the use of scheme/3 in
 * conjuction with apply_scheme/4.)
 *
 * Scheme clauses have the form Sequents ==> Conclusion, where
 * Conclusion is a schematic term of the form phi(...) where ... is a
 * list of arguments.  Each argument has the form V:T, where V is a
 * Prolog variable and T is a possibly non-ground Prolog term.  The
 * set of variables in the Conclusion is called Vs, the set of free
 * variables in the T are called Ts.
 * 
 * The idea is to read the third argument of scheme/3 clauses as
 * induction schemes:
 *
 *    Hyps1==>Goal1  .... HypsN ==> GoalN
 *    -----------------------------------
 *          ==> GoalN
 * 
 * Sequents is a list of sequents of the form Hyps ==> Goal.  When
 * Hyps is empty, the sequent may be written ==> Goal.  Goal is again
 * a term of the form phi(...) (of the same arity as appeared in
 * Conclusion), where each argument is an object-logic term, possibly
 * containing Prolog variables; let the set of Prolog variables be
 * called Gs.
 * 
 * Hyps is a list of the (binding) form B:BT or the (induction
 * hypothesis, or indhyp) form phi(...).  (Again phi must have the
 * same arity as in Conclusion.)
 * 
 * Let the set of binding variables be Bs, and the set of varibles in
 * the indhyp form be IHs.  The we insist that Bs == union(IHs,Gs), so
 * that all variables in this sequent are mentioned in the bindings.
 * 
 * The terms BT may mention Prolog variables in Ts, Prolog unification
 * will instantiate them.
 * 
 * Internally, Bs, (and hence IHs and Gs) are kept in a different name
 * space from Vs (appearing in Conclusion), but it might be confusing
 * to rely on this, and so the user should discipline itself to
 * keeping these sets exlcusive, Bs \cap Vs == \empty.
 * 
 * The second argument to scheme/3 is a list of skeletal induction terms
 * used to (partially) identify the induction scheme.  It is a list of
 * induction terms as they appear in the induction schema: for example
 * in plusind, there is only one constructor; in nat_list_pair there
 * are two [s, ::], as there are in expo, [p,times].  The first
 * argument is the name of a scheme(.) lemma from the Clam library
 * which must, if it is not a var, be present for the induction to be
 * applicable.  */

scheme(A,B,C) :-
    recorded(scheme,scheme(A,B,C),_).

/* apply_scheme(+H==>+AnnGoal,?SchemeSource,?Scheme,?SubGoals).

 * H==>AnnGoal is a well-formed sequent, possibly containing
 * (meta-level) annotations.  Scheme is an induction scheme
 * description: a list of the form V:T-IT (as in induction_pre). V is
 * a variable of type T in the sequent, and IT is an induction term,
 * s(v0) or H::T, for example.  Induction terms may be partially or
 * wholly instantated.  This scheme is applied to H==>AnnGoal giving
 * SubGoals (consisting of both base- and step-cases).  Induction may
 * be on universal variables in the prefix of AnnGoal or on parameters
 * present in H.
 *
 * Induction terms are not necessarily sufficient to accurately
 * identify induction schemes, so there may be backtracking, even when
 * scheme is ground.  (apply_scheme uses the scheme/3 database, and a
 * perusal of that shows that there are different inductions with the
 * same induction terms.)  
 *
 * BASE-CASE: hyps are extended with any parameters, as indicated by
 * the scheme/3 clause for the induction scheme.  The goal is
 * indicated by scheme/3, but from which all annotation has been
 * removed.
 *
 * STEP-CASE: all sinks in step-case goals correspond to the present
 * induction, ie, any sinks present in AnnGoal are first removed.  New
 * sinks are then placed around all universally quantifed variables
 * which are not being induced upon.  A step-case sequent may have
 * multiple hypotheses: this is reflected in the goal by the presence
 * of multi-hole wave-fronts.  All wave-fronts are generated
 * automatically by difference matching each of the hypotheses with
 * the goal.  ONLY THE FIRST OF POTENTIALLY MANY DIFFERENCE MATCHES
 * ARE CONSIDERED... MAYBE ONE DAY THIS RESTRICTION CAN BE DROPPED.
 * Anyway, it would make good sense since the induction_pre code of
 * method_pre knows exactly what difference matches are acceptable.
 * For a general treatment of such matters, see Negrete's thesis.  */

apply_scheme(H==>AnnGoal,lemma(LemmaRequired),
             IndVarAndTypesAndIndices,SubGoals) :-
    no_sinks(AnnGoal,Goal),
    %% find free variables in H
    map_list_filter(H,(Var:Type) :=> (Var:Type),true,HBindings),
 
    %% find a scheme which works over this type
    scheme(LemmaRequired,Indices,SubSequents ==> Phi),
    Phi =.. [phi|IndVarTypes],

    %% we only let the following succeed once since otherwise
    %% behaviour when IndVarAndTypesAndIndices is uninstantiated has
    %% the annoying effect of multiple identical (modulo permuatation)
    %% solutions.  Down side of this is lack of flexibility in finding
    %% types/indices match-up.
    once((lengtheq(IndVarAndTypes,IndVarTypes),
	  zip(IndVarAndTypesAndIndicesPerm,IndVarAndTypes,Indices),
	  permutation(IndVarAndTypesAndIndices,IndVarAndTypesAndIndicesPerm),
	  %% instantiate/check types too
	  unvar(IndVarAndTypes,ITs),
	  unvar(IndVarTypes,ITs))),


    %% When doing a induction, each induction hypotheses must be free
    %% of all annotation.  Base case conclusions are free of all
    %% annotation. Step case conclusions may contain some annotation
    %% inherited from Goal (ie Goal may already be annotated), subject
    %% to the restriction that induction variables (ie IndVarTypes) in
    %% the step case goals are not sinks.  

    %% Dequantify/requantify the universals in the Goal, and account
    %% for possible induction variables in the hypothesis.  We can
    %% induce on universal variables or things already in the context.
    %% Non-induction variables which are not in the context
    %% (NonIndVarTypes) will become sinks
    matrix(Universals,GoalM,Goal),

    %% Here we want to find the induction variables: either universals
    %% or variables in the context.
    append(Universals,HBindings,PossibleIndVars),
    set_subset(IndVarAndTypes,PossibleIndVars),
    no_duplicates(IndVarAndTypes),		% can't do induction
						% on same variable twice
    del_elements(IndVarAndTypes,Universals,NonIndVarTypes),
    
    %% Any type variables in the induction scheme conclusion have a
    %% scope across all of that scheme.  Other variables are taken to
    %% stand for universal variables, and their scope is the sequent
    %% in which they appear.  Type variables are extracted at this
    %% stage.
    unvar(IndVarTypes,TypeTerms), untype(IndVarTypes,IndVars),
    metavars(TypeTerms,TypeVars),
    sub_goals(TypeVars,SubSequents,StepSubs),

    %% GoalTerms are all those occurring in inductive cases
    map_list_filter(StepSubs, (_-Gterm-[_|_]) :=> Gterm,true,GoalTermsNF),
    flatten(GoalTermsNF,GoalTerms),
    %% it is possible that Indices will unify with GoalTerms by
    %% instantiating some variable or other in Indices; this is not
    %% the effect we are looking for.  We simply want to use Indicies
    %% to partially (if at all) instantiate induction parameters
    %% appearing in GoalTerms.  In the case of a two-step induction,
    %% we might have Indices=s(s(v0)) (ie v0 has been supplied) and
    %% GoalTerms might be s(X), if we are trying a single
    %% induction.  These unify, giving an incorrect induciton.
    %% Instead, we need to see that the terms have the same shape, and
    %% only use instantiation to map the variables.  (If Indices is
    %% list of variables, don't do this check, since we are simply
    %% generating, not checking.)
    align_variables(Indices,GoalTerms),

    %% We want two versions of the lifted goal: one with sinks (for
    %% the step cases) and one without.  We need to add the sink
    %% annotations in place before applying the quantifing prefix

    %% Notice that we do not remove annotation from the step-case
    %% goals (other than sinks).  This is a mute point: strictly
    %% speaking, we should remove all new annotation associated with
    %% previous inductions but in the presence of certain proof-plans
    %% (eg. ripple-then-cancel) it is necessary to leave them in
    %% place.  If a user should require (non-sink) annotation to be so
    %% removed, this should be done in the preconditions of the
    %% appropriate method.

    %% For the base case and hypotheses, we need a plain matrix (we
    %% have already removed sinks from Goal)
    wave_fronts(PlainGoalM,_,GoalM),
    matrix(NonIndVarTypes,PlainGoalM,RawGoalBase), 
    mark_sinks(NonIndVarTypes,GoalM,RawGoalStepM),
    matrix(NonIndVarTypes,RawGoalStepM,RawGoalStep),

    %% and we want a schematic version of each of these
    replace_universal_vars(IndVars,IndVarAndTypes,RawGoalBase, BaseGoal),
    replace_universal_vars(IndVars,IndVarAndTypes,RawGoalStep, StepGoal),

    %% We pass the append of H and NonIndVarTypes because Clam doesn't
    %% know about capture avoiding substitution.  Renaming away from
    %% all variables in the prefix and context _usually_ gives a safe
    %% variable name: not always because there may be binding
    %% occurrences that are not in the prefix (we quietly ignore this
    %% problem: the tactic ensures saftey).
    append(H,NonIndVarTypes,Frees),

    make_instances(H,Frees,
		   IndVarAndTypes,StepSubs,IndVarTypes,BaseGoal-StepGoal,
		   SubGoals).


make_instances(_H,_Frees,_IndVarAndTypes,[],_IndVarTypes,_Goal,[]).
make_instances(H,Frees,IndVarAndTypes,[Sub|Subs],IndVarTypes, 
	       Hyp-Goal,[Seq | Seqs]) :-
    %% do a single sequent
    make_instance_(H,Frees,IndVarAndTypes,Sub,IndVarTypes,Hyp-Goal,Seq),
    make_instances(H,Frees,IndVarAndTypes,Subs,IndVarTypes,Hyp-Goal,Seqs).

/* make a single sequent from hyp and goal by applying the
 * substitution SGk-HypSub  */
make_instance_(H,Frees,IndVarAndTypes,Bindings-SGk-HypSub, IndVarTypes,
	       Hyp-Goal, FinalInstHyps==>InstGoal) :-
    map_list(HypSub,
	     SHik :=> (_IN_name:Hki),
	     apply_subst(SHik, IndVarTypes, Hyp, Hki),
	     InstHyps),

    untype(InstHyps,IH_names),
    untype(Bindings,VBs),
    append(VBs,IH_names,BindingsWits),
    %% Hnew  contains induction variables too.  Use union since we may
    %% be doing induction on a parameter already present in H
    union(IndVarAndTypes,H,Hnew),		
    append(IndVarAndTypes,Frees,IVTFrees),
    hfree(BindingsWits,IVTFrees),

    %% the substitution for G is complicated by the need to stick
    %% annotations in place too.  The annotations are found by
    %% difference matching with each of the hypotheses (if there are
    %% any).  
    (HypSub=[] ->
     %% base case so simply instantiate the hypothesis
	 (apply_subst(SGk, IndVarTypes, Hyp, InstGoal),
	  SGkAnn = SGk) ;
     (matrix_transpose(HypSub,HypSubT),
      zip(SGk_HypSubT,SGk,HypSubT),		%align corresponding arguments
      map_list(SGk_HypSubT,
	       (SGkarg-HypSubTarg) :=> TermAnn,
	       (ground_difference_match_multi(HypSubTarg,SGkarg,SGkAnnColoured),
		!,				% Stick with the first one????
		%% not proper colourings, so remove them
		    coloured_term(_,TermAnn,SGkAnnColoured)),
	       SGkAnn)),
     apply_subst(SGkAnn, IndVarTypes, Goal, InstGoal)),
    %% Clam jiggery-pokery: the induction hypotheses are marked specially
    (InstHyps = [] -> 
     ClamInstHyps = InstHyps;
     ClamInstHyps = [step_case:InstHyps]),
    append(Bindings,ClamInstHyps,BindingsInstHyps),
    append(BindingsInstHyps,Hnew,FinalInstHyps).


apply_subst(Ss,Vs,T,TT) :-
    copy(T-Vs,TT-VVs),
    zip(Sub,Ss,VVs),
    map_list(Sub,
	     S-(V:_) :=> S-V,
	     S=V,
	     _SubDone).

make_instance([],[],Hyp-Goal,Hyp==>Goal) :- !.
make_instance([],[],Goal,==>Goal) :- !.
make_instance(_,_,_,_) :- true,true, internall_error1.
  
make_instance([],_IndVarTypes,_Goal,[]).
make_instance([Sub|Subs],IndVarTypes,Goal,[Seq | Seqs]) :-
    make_instance(Sub,IndVarTypes,Goal,Seq),
    make_instance(Subs,IndVarTypes,Goal,Seqs).
    
sub_goals(_TypeVars,[],[]).
sub_goals(TypeVars,[HClist==>GC|Seqs],[Bindings-GTerms-StepSubsts|Steps]) :-
    %% for the moment, we assume that all prolog variables are given
    %% an explicit binding to describe the type.  Later, this could be
    %% partly automated.

    %% Copy to avoid problems if duplicate prolog variables are used
    %% for universal variables;  preserve type variables however.
    copy(TypeVars-HClist==>GC, TypeVars-Hlist==>G),

    sub_goals_(Hlist, StepSubsts, Bindings),

    %% ensure that all prolog variables appearing in this sequent are
    %% bound in Bindings
    untype(Bindings,BindingsNoType),
    metavars(G-StepSubsts,MVs),			% each of these must
    (forall {MV \ MVs} :			% have a binding
	 (member_id(MV, BindingsNoType);
	  member_id(MV,TypeVars)) -> true
      ; clam_internal_error('sub_goals/3.2: incomplete hypothesis (bindings)',[])),

    G =.. [phi|GTerms],
    sub_goals(TypeVars,Seqs,Steps).

sub_goals(TypeVars,[==>GC|Seqs],[[]-GTerms-[]|Steps]) :-
    %% if Hlist is empty, assume that denotes a ground goal (it will
    %% be a base case, eventually.
    (metavars(GC,[]) -> true;
     clam_internal_error('sub_goals/3.3: missing bindings',[])),
    GC =.. [phi|GTerms],
    sub_goals(TypeVars,Seqs,Steps).	
       
sub_goals_([],[],[]).
sub_goals_([H|Hs], [HTerms | StepSubsts], Bindings) :-
    H =.. [phi| HTerms],!,
    sub_goals_(Hs,StepSubsts, Bindings).
sub_goals_([V:T|Hs],  StepSubsts, [V:T|Bindings]) :-
    !,
    sub_goals_(Hs,StepSubsts, Bindings).
sub_goals_([_|_Hs],  _StepSubsts,_Bindings) :-		% junk hyps
    error('unrecognized hypothesis').

sub_goals_(H, [HTerms], []) :-			% singleton abbrev.
    H =.. [phi| HTerms].

/* scheme(?SchemeSource,?Scheme,+H==>+AnnGoal,?BaseSequents,?StepSequents)}. */
scheme(SchemeSource, Scheme, H==>G, BaseCases, StepCases) :-
    apply_scheme(H==>G, SchemeSource, Scheme, Cases),
    base_and_step_cases(H, Cases,BaseCases, StepCases).

base_and_step_cases(_H, [], [], []) :- !.
base_and_step_cases(Hyps, [H==>G | Cases],[H==>G | BaseCases], StepCases) :-
    \+member(step_case:_,H),!,
    base_and_step_cases(Hyps, Cases, BaseCases, StepCases).
base_and_step_cases(Hyps, [H==>G | Cases],BaseCases, [Hih==>G | StepCases]) :-
    member(step_case:_,H),!,
    base_and_step_case_aux(H,Hih),
    base_and_step_cases(Hyps, Cases,BaseCases, StepCases).
base_and_step_cases(_,_,_,_) :-
    clam_error('base_and_step_cases/4: Unknown case.').


/* Map each of the step-case hypotheses into an annotated hypotheses.
   The annotation serves to mark the fact that these hypotheses are
   inductive.   */  
base_and_step_case_aux([step_case:[S|Ss]|H],
		       [ih:[ihmarker(raw,[]),S]|Hihs]) :-
    !,
    base_and_step_case_aux([step_case:Ss|H], Hihs).
base_and_step_case_aux([step_case:[]|H], Hihs) :-
    !,
    base_and_step_case_aux(H, Hihs).
base_and_step_case_aux([],[]).
base_and_step_case_aux([H|Hs],[H|Rest]) :-
    base_and_step_case_aux(Hs,Rest).    

del_elements([],L,L).
del_elements([V|Vs],L,NL) :-
    del_element(V,L,LL),
    del_elements(Vs,LL,NL).

unvar(Bs,BsNoV) :- map_list(Bs,(_V:T):=>T,BsNoV).

set_subset([],_B).
set_subset([A|As],B) :-
    select(A,B,Bs),
    set_subset(As,Bs).


/* I is a variable or I has the same tree-structure as GT.  Since
   Indices and GoalTerms may not be presented in the same order, it is
   necessary to treat GoalTerms as a set.  */
align_variables([],[]).
align_variables([I|Indices],GoalTerms) :-
    var(I),!,
    select(GT,GoalTerms,RestGoalTerms),
    I=GT,!,					%not sure about this cut
    align_variables(Indices,RestGoalTerms).
align_variables([I|Indices],GoalTerms) :-
    select(GT,GoalTerms,RestGoalTerms),
    nodes_equal(I,GT),!,			%nor this one
    I=GT,
    align_variables(Indices,RestGoalTerms).


/* holds if T1 and T2 are the same term trees, modulo differences at
 * the leaves. */
nodes_equal_list([],[]).
nodes_equal_list([T1|Ts],[T2|Qs]) :-
    !,
    nodes_equal(T1,T2),
    nodes_equal_list(Ts,Qs).
nodes_equal(T1,T2) :-
    ((\+ compound(T1) -> !, \+ compound(T2));
     (\+ compound(T2) -> !, \+ compound(T1))).
nodes_equal(T1,T2) :-
    T1 =.. [F|Args1],
    T2 =.. [F|Args2],
    nodes_equal_list(Args1,Args2).

%is_list([_|_]).

/* transpose(+M,?N) N is the transpose of M.  If M is incomplete as a
 * matrix, behaviour is undefined.  */
matrix_transpose( [], [] ) :- !.
matrix_transpose( X, [Y|U] ) :-
	matrix_transpose( X, Y, Z ),
	matrix_transpose( Z, U ).

matrix_transpose( [], [], [] ).
matrix_transpose( [[H]|T], [H|X], [] ) :-
	!,
	matrix_transpose( T, X, [] ).
matrix_transpose( [[H|Hs]|T], [H|X], [Hs|Y] ) :-
	matrix_transpose( T, X, Y ).
	    
/* wave embedding predicates */

/*
 nodes are pairs <name,label>


need to use prologs terms to represent trees.

plus(x,f(y))  plus(s(x),f(y))

the embedding is such that the label is always preserved. so the
representation can  ignore this information.  only need to know which
elements of skel correspond to those in the eraseure

eg in the above, n0(n1,n2(n3)) -> n4(n5(n6),n7(n8)) the embedding is
  n0 -> n4
  n1 -> n6
  n2 -> n7
  n3 -> n8

represent this as a pairing of tree domain elements

  root-root
  1-1.1
  2-2
  2.1-2.1

injections are represented like this.
*/

node_at([],Term,Node) :-
    Term =.. [Node|_].
node_at([SuccP|Pos], Term,Node) :-
    Term =.. [_|Args],
    P is SuccP - 1,
    nth(P,Args,Arg),
    node_at(Pos,Arg,Node).

/*
 * embedding(?E,+Term1,+Term2,+Pos1,+Pos2)
 *  E: T1 --> T2 is an embedding. Posi are the top-level
 * positions of the  roots of terms T1 and T2.  Positions are in
 * reverse order, with the root called [] and arguments numbered 
 * 1..N.  eg in f(x,g) f is at [] and g is at [2].
 * embedding/3 is as /5, but assumes the top-level positions are
 * the roots of T1 and T2 
 */
embedding(E,T1,T2) :-
    embedding(E,T1,T2,[],[]).
embedding([Addr1-Addr2],Atom1,Atom2,Addr1,Addr2) :-
    Atom1 == Atom2,
    atomic(Atom1),!.
embedding([Addr1-Addr2],Var1,Var2,Addr1,Addr2) :-
    Var1 == Var2,
    var(Var1),!.
embedding([Addr1-Addr2|Mapping], Term1,Term2,Addr1,Addr2) :-
    \+ var(Term2),
    \+ var(Term1),
    Term1 =.. [F|Args1],
    Term2 =.. [F|Args2],
    embedding_list(Mapping,Args1,Args2,Addr1,Addr2,1).
embedding(Map, Term1,Term2,Addr1,Addr2) :-
    \+ var(Term2),
    Term2 =.. [_F2|Args2],
    nth(N,Args2,Arg2),
    embedding(Map,Term1,Arg2,Addr1,[N|Addr2]).

 

embedding_list([],[],[],_,_,_).
embedding_list(Ms,[A1|A1s],[A2|A2s],Pos1,Pos2,N) :-
    embedding(M,A1,A2,[N|Pos1],[N|Pos2]),
    NN is N + 1,
    embedding_list(Mss,A1s,A2s,Pos1,Pos2,NN),
    append(M,Mss,Ms).

/*
 * EmbExt is the extension of Emb at all point where Emb
 * is not a node -> node mapping.  (Usually used when
 * Emb has been instantiated with terms
 * Note that in general substitutions increases the number of embeddings
 * (a la difference unification), but we only want to consider the (unique)
 * extension
 */

/*
 * ann_unify(+ATerm1,+ATerm2,Em)
 * aterm1 and aterm2 have an annotated unifier sigma where
 * sigma(aterm1) 
 */
ann_unify(aterm(Skel1,Erase1,Emb1),aterm(Skel2,Erase2,Emb2),Em) :-
    /* check these terms are well-formed */
    embedding(Emb1,Skel1,Erase1,[],[]),
    embedding(Emb2,Skel2,Erase2,[],[]),
    
    /* keep track of the instantiations */
    unify(Erase1,Erase2),  /* note that this binds in the Skels too */

    /* trivially, these terms are well-formed:
     *
     *  aterm(sigma(Skeli),sigma(Erase1),sigma(Embi))
     *
     * though we need to extend sigma(Embi) via id
     */
    embedding(Emb1new,Skel1,Erase1,[],[]),
    subset(Emb1,Emb1new),           /* and this is the new embedding */
                                    /* this always succeeds */
				    
    embedding(Emb2new,Skel2,Erase2,[],[]),
    subset(Emb2,Emb2new),           /* and this is the new embedding */
                                    /* this always succeeds */
    /* finally, check that the computed embedding exists */
    embedding(Em,Skel1,Skel2,[],[]).

    
 
/* Term is represented as an embedding. */ 
embedding_form(Term,aterm(Skel,Erasure,Em)) :-
    erase(Term,Erasure),
    skeletons(Term,Skels),
    member(Skel,Skels),
    embedding(Em,Skel,Erasure).

/*
 * regular_form(+Type,?Term,aterm(+Skel,+Erasure,+Em))
 * Term is represented using normal insitu annotations
 * add annotations into Erasure according to Em.  Type is one of
 * {merged,split}, according to whether Term's annotations should be
 * in normal-form (split) or in non-normal-form (merged).
 *
 * recurse throught Erasure, copying structure into Term.
 * if current position is in Em, then copy a wave_hole as well.
 */
regular_form(Type,Term,aterm(_Skel,Erasure,Em)) :-
    regular_form(Type,hole,[],Term,Erasure,Em).
regular_form(_Type,front,Pos,Hole,V,Em) :-
    iswh(Hole,V),
    var(V),
    member(_-Pos,Em),!.
regular_form(Type,front,Pos,WH,Erasure,Em) :-
    iswh(WH,Hole),
    member(_-Pos,Em),!,
    /* we are looking at a node in Erasure which is part of the skeleton,
     * and we are currently in a front, so add a wave-hole
     */	
    Erasure =.. [F|Eargs],
    regular_form_map(Type,1,hole,Pos,Holes,Eargs,Em),
    Hole =.. [F|Holes].
regular_form(Type,hole,Pos,WF,Erasure,Em) :-
    iswf(WF,hard,out,Front),
    \+member(_-Pos,Em),!,
    /* we are looking at a node in Erasure which is part of the front,
     * and we are currently in a hole, so add a wave-front
     */	
    Erasure =.. [F|Eargs],
    regular_form_map(Type,1,front,Pos,Fronts,Eargs,Em),
    Front =.. [F|Fronts].

/* anything else just recurse */
regular_form(split,hole,_Pos,Erasure,Erasure,_Em) :-
    \+compound(Erasure).
regular_form(split,hole,Pos,Term,Erasure,Em) :-
    compound(Erasure),
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,hole,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form(split,front,Pos, WH,Erasure,Em) :-
    %% Only add anntotation here if there is some of the skeleton
    %% below this place in the term tree.
    iswh(WH,WF),
    iswf(WF,hard,out,Term),
    member(_-HolePos,Em),
    append(_,Pos,HolePos),!,
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,front,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form(_Type,front,_Pos,Erasure,Erasure,_Em) :-
    %% otherwise, we are in a front and there are no holes below Pos
    \+compound(Erasure),!.
regular_form(split,front,Pos,Term,Erasure,Em) :-
    %% otherwise, we are in a front and there are no holes below Pos
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,front,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].

regular_form(merged,_Kind,_Pos,Erasure,Erasure,_Em) :-
    \+compound(Erasure),!.
regular_form(merged,Kind,Pos,Term,Erasure,Em) :-
    Erasure =.. [F|Eargs],
    regular_form_map(merged,1,Kind,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form_map(_Type,_,_Kind,_Pos,[],[],_Em).
regular_form_map(Type,N,Kind,Pos,[H|Holes],[E|Eargs],Em) :-
    regular_form(Type,Kind,[N|Pos],H,E,Em),
    NN is N + 1,
    regular_form_map(Type,NN,Kind,Pos,Holes,Eargs,Em).
    
/*
 * embedding_ground(?E,?Term1,+Term2,+Pos1,+Pos2)
 *  E: T1 --> T2 is an embedding. Posi are the top-level
 * positions of the  roots of terms T1 and T2.  Positions are in
 * reverse order, with the root called [] and arguments numbered 
 * 1..N.  eg in f(x,g) f is at [] and g is at [2].
 * embedding/3 is as /5, but assumes the top-level positions are
 * the roots of T1 and T2 
 * Similar to embedding/3 only (i) more generous mode since all
 * terms must be grounded and (ii) the 3rd clause is quite different
 * since it must cater for Term1 being variable: we refine this into
 * a skeletal functor and recurse.
 */
embedding_ground(E,T1,T2) :-
    embedding_ground(E,T1,T2,[],[]).
embedding_ground([Addr1-Addr2],Var,Atom,Addr1,Addr2) :-
    atomic(Atom),
    Var = Atom,!.
/* for sinks (dynamic wave-rule application
 * with sinks).  we dont care about the skeleton of the sink 
 * position
 */
embedding_ground([Addr1-Addr2],Var,SinkTerm,Addr1,Addr2) :-
    issink(SinkTerm,Term),
    issink(Var,Term),!.
/*embedding_ground([Addr1-Addr2], Var,Term2,Addr1,Addr2) :-
    \+ var(Term2),
    var(Var),
    Var = Term2.
*/
embedding_ground([Addr1-Addr2|Mapping], Term1,Term2,Addr1,Addr2) :-
    \+ atomic(Term2),
    Term2 =.. [F|Args2],			%term2 is ground
    /* decompose Term1 into a skeletal functor for F if Term1 is a var */
    length(Args2,N),length(Args1,N),
    Term1 =.. [F|Args1],
    embedding_ground_list(Mapping,Args1,Args2,Addr1,Addr2,1).
embedding_ground(Map, Term1,Term2,Addr1,Addr2) :-
    \+ var(Term2),
    Term2 =.. [_F2|Args2],
    nth(N,Args2,Arg2),
    embedding_ground(Map,Term1,Arg2,Addr1,[N|Addr2]).

embedding_ground_list([],[],[],_,_,_).
embedding_ground_list(Ms,[A1|A1s],[A2|A2s],Pos1,Pos2,N) :-
    embedding_ground(M,A1,A2,[N|Pos1],[N|Pos2]),
    NN is N + 1,
    embedding_ground_list(Mss,A1s,A2s,Pos1,Pos2,NN),
    append(M,Mss,Ms).

try_superimpose([],[]).
try_superimpose([[]],[]) :- !.
try_superimpose([[H-G]|Rest],[H-G|RestSup]) :-
    /* singletons are the single-hole case */
    !,try_superimpose(Rest,RestSup).
try_superimpose([Set|Rest],[SetMulti|RestSup]) :-
    /* insist that all elements of Set superpose with one another */
    superpose(Set,SetMulti),!,
    try_superimpose(Rest,RestSup).
try_superimpose([_Set|Rest],RestSup) :-
    try_superimpose(Rest,RestSup).


/*
 * S is a set of pairs of single-hole terms, and SM is the multi-hole
 * term resulting from superposing all elements of S.  Each skeleton
 * in S is assigned a unique colour.  We do this with constants rather
 * than variables to simplify the coding.  
 */
superpose(S,SM) :-
    superpose(S,_,SM).
superpose([],SM,SM).
superpose([H-G|Set],SoFar, SM) :-
    overlap(H-G,SoFar, SMtmp),
    superpose(Set,SMtmp, SM).

/* overlap(T1,T2,Result) Result is the result of overlapping T1 (a
 * single-hole term) with T2 (possibly multi-hole).  H and G are
 * coloured terms.
 */
overlap(H-G,SoFarH-SoFarG,SMH-SMG) :-
    !,overlap(H,SoFarH,SMH),
    overlap(G,SoFarG,SMG).
overlap(T,T,T) :- !.
/*
 * in the case of wave-fronts which align we look at the positions of
 * the wave-holes (which we find immediately inside the wave-front and
 * therefore why we require annotations in normal form).  There are
 * two cases:
 * 1. The wave-holes are in the same position (and these holes overlap
 * too).  There is one subtlety here which is that holes only align if
 * they are of the same colour, so we ensure that the resultant
 * overlapping holes is coloured with the union of the colours
 * annotating the separate holes.  Eg: the terms
 *
 *  ``f({``g(a,{b}red)''}red)'' and ``f({``g({a}green,b)''}green)''
 * 
 * overlap with a resulting term
 *     ``f({``g({a}green,{b}red)''}[red,green])''
 *
 * 2. There is no hole in Front2 at a position corresponding to the
 * hole in Front1.  Since Front1 and Front2 have disjoint coloured
 * skeletons we can simply copy the hole from Front1 into the
 * corresponding position in Front2.  Eg.
 * ``f({``g({h}red)''}red,p)''
 * 
 * There is some subtlety here; lets c1 be the colours of the holes in
 * Front2; if Front2 appears _inside_ a hole of colours c2, then it
 * should be the case that c1 \subseteq c2, since otherwise c2 \ c1
 * are redundant colours and are not part of the skeleton.
 * When extending Front2 with a new hole, should we add this colour to
 * "higher-up" holes should have this extra colour added.
 * Luckily we dont need to do this (think of the induction hypothesis).
 */

overlap(WF1,WF2,WF3) :-
    iswf(WF1,T,D,Front1),
    iswf(WF2,T,D,Front2),
    iswf(WF3,T,D,MultiFront),
    !,
    Front1 =.. [F|Args1],
    Front2 =.. [F|Args2],
    iswh_colour(WHC,[C1],Hole1),
    member_pos(Args1,N1,WHC),
    member_pos(Args2,N1,Term), 
    
    %% CASE 1.
    ((iswh_colour(Term,Colours,Hole2),
      overlap(Hole1,Hole2,NewHole),
      union([C1],Colours,NewColours),!);

    %% CASE 2.
     (\+ iswh_colour(Term,_,_),		%NOT a hole this time
      NewColours = [C1],			%preserve the colour
      NewHole = Hole1,!)),			%and the contents

    %% now make the new Front
    iswh_colour(HoleNewHole,NewColours,NewHole),
    subst_list(N1, HoleNewHole, Args2, MultiFrontArgs),
    MultiFront =.. [F|MultiFrontArgs]. 
    
/* cases where the terms dont even share wave-fronts */
overlap(WF,_,_) :- 
    iswf(WF,_T,_D,_Front1),!,fail.
overlap(_,WF,_) :- 
    iswf(WF,_T,_D,_Front1),!,fail.
    
overlap(T1,T2,Trec) :-
    T1 =.. [F|Args1],
    T2 =.. [F|Args2],				%they ought to be the same F
    overlap_map(Args1,Args2,TrecArgs),
    Trec =.. [F|TrecArgs].

overlap_map([],[],[]).
overlap_map([A|As],[B|Bs],[AB|ABs]) :-
    overlap(A,B,AB),
    overlap_map(As,Bs,ABs).

member_pos([], _,_) :- !,fail.
member_pos([T | _], 1, T ).
member_pos([_|Rest], N, T) :-
    member_pos(Rest, NN, T),
    N is NN + 1.

/*
 * add some colour annotations to Term.  First arg is the colour to
 * use. Safe on non-ground terms.  Mode ? ? ?
 */
coloured_term(_Colour,Var,Var) :-
    var(Var),!.
coloured_term(_Colour,Atom,Atom) :-
    atomic(Atom),!.
coloured_term(Colour,WH,WHC) :-
    iswh(WH,Hole),
    iswh_colour(WHC,[Colour],HoleC),
    !,coloured_term(Colour,Hole,HoleC).
coloured_term(Colour,Term,TermC) :-
    var(TermC),
    Term =.. [F|As],
    coloured_term_map(Colour,As,AsC),
    TermC =.. [F|AsC].
coloured_term(Colour,Term,TermC) :-
    var(Term),
    TermC =.. [F|AsC],
    coloured_term_map(Colour,As,AsC),
    Term =.. [F|As].

coloured_term_map(_Colour,[],[]).
coloured_term_map(Colour,[A|As],[AC|AsC]) :-
    coloured_term(Colour,A,AC),
    coloured_term_map(Colour,As,AsC).

/*
 * subst_list(N,T,Told,Tnew) T1 is same as T2 with its N'th element
 * replaced by T
 */
subst_list(_,[],[]).
subst_list(1,NewT,[_T|Ts],[NewT|Ts]) :- !.
subst_list(N,NewT,[T|Ts],[T|Tps]) :-
    NN is N - 1,
    subst_list(NN,NewT,Ts,Tps).

/*
 * Gnd difference match Goal and Hyp, stick the anntotations into NewGoal
 * Type is either merged or split, to indicated the style of
 * annotation in NewGoal (see comments for regular_form/3).
 */
ground_difference_match(Type,Hyp,Goal,NewGoal) :-
    embedding(E,Hyp,Goal),
    regular_form(Type,NewGoal,aterm(Hyp,Goal,E)).
/*
 * Gnd difference uynify Goal and Hyp, stick the anntotations into
 * NewGoal and NewHyp (cf matching case above).
 * Type is either merged or split, to indicated the style of
 * annotation in NewGoal (see comments for regular_form/3).
 */
ground_difference_unify(Type,Skel,Hyp,Goal,NewHyp,NewGoal) :-
    embedding_ground(E1,Skel,Goal),
    embedding_ground(E2,Skel,Hyp),
    regular_form(Type,NewGoal,aterm(Skel,Goal,E1)),
    regular_form(Type,NewHyp,aterm(Skel,Hyp,E2)).

parse_wave_rule(L :=> R, AnnL :=> AnnR) :-
    ground_difference_unify(split,_,L,R,AnnL,AnnR).

/*
 * ground_difference_unify_multi(+Hyp,+Goal,-NewHyp,-NewGoal).
 * Multi-hole case of ground_difference_unify/6. 
 */
ground_difference_unify_multi(Hyp,Goal,NewH,NewG) :-
    findall(NewHyp-NewGoal,
	    ground_difference_unify(split,_Skel,Hyp,Goal,NewHyp,NewGoal),
	    Singles),
    /*
     * we want to do a kind of maximal superposition, and by that I
     * mean to try the power-set of all superpositions 
     */
    power_set(Singles,PS),
    /* 
     * PS makes it easy to try to find all possible combinations of
     * superpositions.   Before we do that though, we have to assign
     * a unique colour to each of the elements in PS.
     */
    map_list(PS,I:=>O,
	    map_list(I,H-G:=>HC-GC, (%gensym(c,Colour),
				    coloured_term(b,H,HC),
				    coloured_term(b,G,GC)),O),PScoloured),
		    
    try_superimpose(PScoloured,MHGDUs),!,	% we get all the
						% solutions immediatedly
    member(NewH-NewG, MHGDUs).			% but succeed one at a time

/*
 * user-interface for "wave-rule" parsing.  NOTE this DOES NOT
 * know about measures.. only for playing! 
 */
parse_wave_rule_multi(L :=> R, AnnL :=> AnnR) :-
    ground_difference_unify_multi(L,R, AnnL,AnnR).

/* match each of Hyps with Goal and superimpose the result.  This is
   faster than the unification version because we do only half the
   work.  The other half is "const".  */
ground_difference_match_multi(Hyps,Goal,NewG) :-
    setof(const-NewGoal,
	    H^(member(H,Hyps),
	     ground_difference_match(split,H,Goal,NewGoal)),
	    Singles),
    
    power_set(Singles,PS),
    map_list(PS,I:=>O,
	     map_list(I,H-G:=>HC-GC, (%gensym(c,Colour),
			  coloured_term(b,H,HC),
			  coloured_term(b,G,GC)),O),PScoloured),
    
    try_superimpose(PScoloured,MHGDUs),!,	% we get all the
						% solutions immediatedly
    member(_-NewG, MHGDUs).			% but succeed one at a time


/* process T as an induction scheme */
add_induction_scheme(T) :-
    (recorded(theorem,theorem(T,scheme,G,_),_) -> true;
     clam_warning('There is no scheme named %t\n',[T])),
    (construct_scheme(G,Skels,Scheme)
	 -> (uniq_recorda(scheme,scheme(T,Skels,Scheme),_),
	     lib_writef(23,'Added induction scheme for %t\n', [T])) 
	 ;  clam_warning('Unable to parse induction scheme %t\n',[T])).    


/* Enable clauses to be added to the scheme/3 predicate on-the-fly */

/* construct_scheme/3
 *
 * Construct a clause for the scheme/3 predicate from Oyster type
 */
construct_scheme(Term,Skels,Scheme):-
    construct_scheme(Term,_,[],[],Skels,Scheme).

/* construct_scheme/6
 *
 * The arguments are as follows:
 *    Term    An induction scheme in Oyster/Clam syntax.
 *    P       The induction predicate, e.g., `phi'.
 *    Ts      The meta-variables associated with type variables, i.e., types
 *            t asserted to be t:u(n) for some n. Ts is a list in which each
 *            element is of the form Type-Metavar.
 *    Vs      The type of each variable encountered. Stored as a list of
 *            elements of the form Var-Type.
 *    Skels   A list of skeletal induction terms.
 *    Scheme  The meta-level representation of the induction scheme.
 */
construct_scheme(Type:u(_)=>Term,P,Ts,Vs,Skels,Scheme):-
    bind(Type,_,Ts,NewTs),
    construct_scheme(Term,P,NewTs,Vs,Skels,Scheme).
construct_scheme(Var:Type=>Term,P,Ts,Vs,Skels,Scheme):-
    construct_scheme(Term,P,Ts,[Var-Type|Vs],Skels,Scheme).
construct_scheme(PTerm,P,Ts,Vs,[],[]==>PhiApp):-
    predicate_app(PTerm,P,Vars),
    construct_args(Vars,Ts,Vs,Args),
    PhiApp =.. [phi|Args].
construct_scheme(CaseTerm=>Term,P,Ts,Vs,Skels,[CaseS|S]==>C):-
    construct_case(CaseTerm,P,Ts,Skels1,CaseS),
    construct_scheme(Term,P,Ts,Vs,Skels2,S==>C),
    append(Skels1,Skels2,Skels).

/* construct_case/5
 *
 * Construct the sequent for one hypothesis of an induction scheme.
 * Skels is forced to [] if the hypothesis is found to be a base case.
 */
construct_case(Term,P,Ts,[],CaseScheme):-
    construct_case(Term,P,Ts,[],base,_,CaseScheme).
construct_case(Term,P,Ts,Skels,CaseScheme):-
    construct_case(Term,P,Ts,[],step,Skels,CaseScheme).

/* construct_case/7
 *
 * The arguments are as follows:
 *    Term    A hypothesis of an induction scheme.
 *    P       As for construct_scheme/6.
 *    Ts      As for construct_scheme/6.
 *    Vs      The meta-variable associated with each object-level variable in
 *            the hypothesis. Each element of the list has the form Var-Meta.
 *    Case    Either `base' or `step'. A hypothesis is initially assumed to be
 *            a base case. If an assumption involving the induction predicate
 *            is encountered this assumption is revised.
 *    Skels   A list of skeletal induction terms for the hypothesis.
 *    H==>G   A meta-level representation of the induction hypothesis.
 */
construct_case(Var:Type=>Term,P,Ts,Vs,Case,Skels,[Meta:MetaType|H]==>G):-
    bind(Var,Meta,Vs,NewVs),
    construct_case(Term,P,Ts,NewVs,Case,Skels,H==>G),
    construct_type(Type,Ts,MetaType).
construct_case(PTerm=>Term,P,Ts,Vs,step,Skels,[PhiApp|H]==>G):-
    predicate_app(PTerm,P,HypTerms),
    construct_term(HypTerms,Vs,Metas,_),
    PhiApp =.. [phi|Metas],
    construct_case(Term,P,Ts,Vs,_,Skels,H==>G).
construct_case(PTerm,P,_,Vs,base,Skels,[]==>PhiApp):-
    predicate_app(PTerm,P,Terms),
    construct_term(Terms,Vs,Metas,Skels),
    PhiApp =.. [phi|Metas].

/* construct_term/4
 *
 * Constructs a meta-level term and skeletons from an object-level term.
 * The object-level term is processed recursively replacing all object-level
 * variables with their corresponding meta-variables as recorded in the
 * second argument, Vs.
 */
construct_term([],_,[],[]) :- !.
construct_term([Term|Terms],Vs,[Meta|Metas],[Skel|Skels]):- !,
    construct_term(Term,Vs,Meta,Skel),
    construct_term(Terms,Vs,Metas,Skels).
construct_term(Term,Vs,Meta,_):- 
    /* Term is atomic ... */
    Term =.. [_],
    /* ... and one of the variables bound in Vs */
    member(Term-Meta,Vs),!.
construct_term(Term,Vs,Meta,Skel):-
    Term =.. [Con|Terms],
    construct_term(Terms,Vs,Metas,Skels),
    Meta =.. [Con|Metas],
    Skel =.. [Con|Skels].

/* construct_args/4
 *
 * Constructs the arguments of the meta-level induction predicate, phi.
 * Ts and Vs are as for construct_scheme/6.
 */
construct_args([],_,_,[]).
construct_args([Var|Vars],Ts,Vs,[_:MetaType|Args]):-
    /* Get the type of the variable */
    member(Var-Type,Vs),
    /* Form the meta-level version of the type */
    construct_type(Type,Ts,MetaType),
    /* Process the rest of the arguments */
    construct_args(Vars,Ts,Vs,Args).

/* construct_type/3
 *
 * Constructs a meta-level type from an object-level type.
 * The object-level type is processed recursively replacing all object-level
 * type variables with their corresponding meta-variables as recorded in the
 * second argument, Ts.
 */
construct_type([],_,[]) :- !.
construct_type([Type|Types],Ts,[Meta|Metas]):- !,
    construct_type(Type,Ts,Meta),
    construct_type(Types,Ts,Metas).
construct_type(Type,Ts,Meta):-
    /* Type is atomic ... */
    Type =.. [_],
    /* ... and one of the type variables bound in Ts */
    member(Type-Meta,Ts).
construct_type(Type,Ts,Meta):-
    Type =.. [Con|Types],
    construct_type(Types,Ts,Metas),
    Meta =.. [Con|Metas].

/* predicate_app/3
 *
 * Matches a term of the form `P of a_1 of ... of a_n' for n>=1 such that
 * predicate_app(P of a_1 of ... of a_n,P,[a_1,...,a_n]).
 */
predicate_app(PTerm of Arg,P,Args):-
    predicate_app(PTerm,P,PArgs),
    append(PArgs,[Arg],Args).
predicate_app(P of Arg,P,[Arg]).

/* bind/4
 *
 * Concatenates Var-Meta to the head of Vs unless Var-Meta is already an
 * element of Vs.
 */
bind(Var,Meta,Vs,Vs):-
    member(Var-Meta,Vs).
bind(Var,Meta,Vs,[Var-Meta|Vs]).

/*
 * @(#)$Id: reduction.pl,v 1.28 2005/05/06 19:25:38 smaill Exp $
 *
 * $Log: reduction.pl,v $
 * Revision 1.28  2005/05/06 19:25:38  smaill
 * take out check_time_limit (dealt with by sictus timing module);
 *
 * Revision 1.27  2003/01/22 18:57:35  smaill
 * for DICE
 *
 * Revision 1.26  1999/03/31 14:12:52  img
 * check reduct is ground
 *
 * Revision 1.25  1998/09/29 17:02:28  img
 * ev/2: time check (for debugging); clauses for atom and u(_).
 *
 * Revision 1.24  1998/09/17 08:34:57  img
 * added clauses for predefined atomic inhabited types
 *
 * Revision 1.23  1998/09/16 13:39:57  img
 * ev/2: revised for improved performance.  Propositional rules are
 * built-in.
 *
 * Revision 1.22  1998/09/01 14:02:20  img
 * ev/10: clause for < deleted
 *
 * Revision 1.21  1998/08/26 12:16:57  img
 * reduction_rule/_: use unification.  ev/8: incomplete clauses
 * for = fixed.  Spurious clause for < removed.
 *
 * Revision 1.20  1998/07/29 15:15:27  img
 * Labelling did not accurately reflect status after applying rules such as
 * f(A) -> A in the case that A is in n.f.
 *
 * Revision 1.19  1998/07/27 12:08:40  img
 * singletons
 *
 * Revision 1.18  1998/06/10 08:05:54  img
 * evaluation code (experimental)
 *
 * Revision 1.17  1998/05/13 12:58:16  img
 * Labelling of repeated variables was not handled correctly: labellings
 * should be identical.  This wasn't happening since all complete
 * labellings were either cross or tick.  Bug fix is to label non-crossed
 * nodes with Prolog variables.  Added additional arg to rt/_ etc to pass
 * predicate used for discharging conditions.
 *
 * Revision 1.16  1998/03/25 10:28:51  img
 * Added support for polymorphic rewrites---type guessing takes place
 * when a rule is applied.  Wrapped all access to the recorded database.
 * Generalize conditional equations before making them rewrites.
 *
 * Revision 1.15  1998/02/17 13:51:53  img
 * record origin of equations
 *
 * Revision 1.14  1997/09/26 14:49:20  img
 * nf/[2,4], nf_plus/4 -> reduction_rtc/[2,4], reduction_tc/4
 *
 * Revision 1.13  1997/04/07 11:41:19  img
 * rationalize code for equal length lists.
 *
 * Revision 1.12  1997/01/14 10:44:23  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.11  1996/12/12 12:41:18  img
 * Error message predicates.
 *
 * Revision 1.10  1996/12/04 12:30:30  img
 * rt/7.1: Labels on the RHS of reduction rules were not correct in the
 * case of rules like f(X) :=> X, where X was labelled inside f.  If the
 * label is variable, make it a tick.
 *
 * Revision 1.9  1996/06/18  17:16:00  img
 * more informative error message
 *
 * Revision 1.8  1996/06/11  16:30:57  img
 * cosmetic changes
 *
 * Revision 1.7  1996/05/31  12:42:34  img
 * Check polarity on each rule application.
 *
 * Revision 1.6  1996/05/24  09:52:26  img
 * New reduction rule machinery.  Uses simplification ordering
 * (extensible version of RPOS) to prove that a rewrite relation is
 * well-founded.  (See MRG Blue Book notes 1073 and 1084 for more
 * details.)  A terminating TRS is kept in reduction_rule/6 (these are
 * the rewrite rules), and the pair of quasi-precedence (a binary
 * relation over the set of function symbols in the theory) and status
 * function is kept in registry/3.  add_rule/3 is used to add new rules
 * to the TRS.  (See also the reduction/2 method.)
 *
 * New term rewriting machinery.  Uses labelled term rewriting (see MRG
 * Blue Book note 1095) to normalize terms wrt reduction rules.  Labelled
 * term rewriting support is in place for use in rippling too.
 *
 * nf/4 and nf_plus/4 compute the ref. trans. clos. and trans. clos. of
 * the congruence closure of the reduction rule rewrite relation.  Use
 * nf_plus/4 to put a term into normal form (eg method normalize_term).
 *
 * Equal rules removed (now these are reduction rules).  Cancellation
 * rules kept since they can have a special status during ripple then
 * cancel.
 *
 * Revision 1.5  1995/11/28  20:20:38  img
 * Capture <=> as equivalence
 *
 * Revision 1.4  1995/10/24  14:53:15  img
 * removed old parsing code
 *
 * Revision 1.3  1995/05/17  02:17:52  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:32  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: reduction.pl,v 1.28 2005/05/06 19:25:38 smaill Exp $').

/* This file contains all the code needed to deal with reduction
   rules.  Reduction rules are rewrite rules which are particularly
   well behaved, and which are used in the symbolic evaluation method
   for doing simple rewrites on expressions. 

   Here we use a simplification ordering to demonstrate termination of
   the rewrite set.  A simplification ordering is based on EPOS,
   which is in turn based on RPOS (recursive path ordering with
   status).  */

/* reduction_rule(LHS, RHS, Cond, Dir, Origin,Rulename,Ref): Rulename
   is the name of a rewrite Cond=>LHS:=>RHS that has been proven to be
   measure-decreasing under some well-founded termination order.
   Origin is the name of a definition/theorem on which Rulename is
   based. Dir describes the polarity restrictions in using the rule.
   (Ref is the reference of the rule in the database.)

   Clam supports two different reduction rule sets in order to permit
   implicative rewrites to be used in either direction.  This is
   terminating because the polarity restriction on the use of the
   rules ensures that cycles are prevented.  Equality rules must be
   oriented left-to-right (or right-to-left) since they may be applied
   in positions of either polarity.  Thus, there are two registries,
   labelled "positive" and "negative", establishing termination of all
   reduction rules whose Dir is imp(left) and imp(right),
   respectively.  Equality rules are accounted for in both registries,
   since this simplifies the implementation.

   Equivalence rules L <=> R may be used in either direction, although
   they must be proven termination as L => R and R => L, and stored in
   separate TRSs.  For this reason they can no longer be seen as
   "equality" rules.

   The ground case is faster when no occurs check is required.  */
reduction_rule(LHS, RHS, Cond, Dir, Rulename,Ref) :-
    reduction_rule(LHS, RHS, Cond, Dir, _,Rulename,Ref).
reduction_rule(LHS, RHS, Cond, Dir, Origin,Rulename,Ref) :-
    reduction_rule(LHS, RHS, Cond, Dir, _,Origin,Rulename,Ref).

reduction_rule(LHS, RHS, Cond, Dir, TypeInfo,Origin,Rulename,Ref) :-
    reduction_rule(LHS, _,RHS, _,Cond, Dir, TypeInfo,Origin,Rulename,Ref).

/* reduction_rule/10 is as reduction_rule/8, but labelling of LHS and
   RHS is returned in the additional arguments.  */
reduction_rule(LHS, LHSlabel,RHS,RHSlabel, C, D, TypeInfo,Origin,Rulename,Ref) :-
    /* need to unify for soundness (The labels don't need to be unified) */
    recorded(reduction,reduction(
               LHS1, LHSlabel,RHS1,RHSlabel, C1, D1, TypeInfo1,Origin,Rulename),Ref),
    
    unify(reduction(LHS1,RHS1,C1, D1, TypeInfo1,Origin,Rulename),
	  reduction(LHS,RHS, C,  D,  TypeInfo, Origin,Rulename)).   

/* See if a (assumed ground) term is a redex wrt to the reduction rule
   db */
reduction_redex(LHS) :-
    reduction_rule(LHS,_,_,_,_,_).


/* Prepare Thm (which is somehow related to thm/def D) for processing
   by add_rule/2; Give user info if no rule was derived from some thm. */
add_reduction_rules_list(_Origin,[]).
add_reduction_rules_list(Origin,[Thm|Rest]) :-
    add_reduction_rules(Origin,Thm),
    add_reduction_rules_list(Origin,Rest).

/* D is the name of a definition or theorem, and Thm is the name of a
   theorem; process Thm for use as a rewrite rule having parentage D.
   As many rewrites as possible will be extracted from Thm to be used
   in rippling.  */
add_reduction_rules(D,Thm) :- add_rules(reduction,D,Thm).

/*    oyster_problem(Thm,[]==>Goal),
    matrix(Vars,Matrix,Goal),
    poly_type_variables(Vars,TypeVars),
    replace_universal_vars(MVs,Vars,TypeVars-Matrix,MTVs-LiftedGoal),
    map_list(Vars,(A:B):=>(A-B),FVars),
    replace_universal_vars(MVs,Vars,FVars,TypeInfo),    
    add_rule(reduction,Origin,Thm,MTVs,TypeInfo,LiftedGoal),
    if(\+ reduction_rule(_,_,_,_,Thm,_),
       clam_warning('No reduction rules were derived from %t.\n',[Thm])),     
    !,
    add_reduction_rules(Origin,Rest).
*/
/* The current TRS is kept in the recorded database.  The rewrite
   rules proper are those described by reduction_rule/7, and the
   registry is the pair (Tau,Prec).  Typically, Prec will not be a
   terminated list, since that allows it to be extended.  The
   extension of Tau is done is a different way.  It might be useful to
   have multiple TRSs, but for the moment there is only one.  */
registry(TRS,Tau,Prec,Ref) :-
    recorded(registry,registry(TRS,Tau,Prec),Ref).

/* This flag determines whether the registry will be extended
   dynamically during the application of the reduction method.  */ 
extending_registry :-
    fail.

                   /* TERM REWRITING STUFF */

/* Repeated application of reduction rules; uses labelled trees to
   speed up rewriting.  

   A labelling is a term built with constructors "node" and Prolog
   lists.  nodes are labelled with the atom "cross", or an
   uninstantiated variable.  A compelete labelling (CL) for a term T
   is one with the same term structure: "cross" means that the
   corresponding node in T is in normal form; var means that this is
   not known to be a cross.  Hence a CL determines which subterms of T
   to examine for redexes.  An incomplete labelling (IL) is like a CL
   but terms rooted with a var node do not share the term structure of
   the corresponding term.  (Two labelling well-formedness properties
   are assumed: all nodes below a crossed node are crossed and all
   nodes above a var node node are var.)  The variable of a Var nodes
   may appear elsewhere in the labelling when they are labelling
   identical variables in the corresponding term.

   (A term in normal form is labelled with a tree full of crosses.
   This seems wasteful, but the uniformity allows unification to be
   used to propagate labellings.)

   Labellings are used to skip (crossed) subterms which are known not
   to contain redexes.  The result is a much faster rewriting process.
   Labellings are propagated during rewriting (the reduction rule
   parser stores propagation information at load-time; see lib_load/_
   and add_rule/_).

   rt(Pos,T,Tl,Ref,S,Sl,Hyps): There are two possibilities:

   (i) T can be rewritten into S using a reduction rule described by
   Ref.  Sl will be a complete labelling of S.  Tl may be an
   incomplete labelling (cf ii), but the path to the the rewritten
   subterm is var.

   (ii) T and S are identical and in normal form. Tl is an labelling
   containing var nodes. Sl is a CL containing only crosses,
   reflecting the fact that S is in normal form.

   Pos is the position in T (S) of the redex (reduct).  Hyps is passed
   around in case conditions need to be established.  */

rt([],T,node(Tick,Ts),[Thm,Dir],S,node(Sl,Ss),Hyps,Elem) :-
    var(Tick),
    %% This base case clause has to do some manipulation to ensure
    %% that labelling information on terms bound to variables in the
    %% reduction rule is propagated from T into S.  For example,
    %% rewriting s(x*)=s(y+) into x=y, using the cancellation rule for
    %% s, should copy the annotation (* and +) on the terms x and y
    %% into the reduct x=y.  Otherwise it will be lost.  See
    %% processing of reduction rules in lib_load/_ and add_rule/_.
    reduction_rule(T,node(Tick2,Ts),S,node(Sl,Ss), Cond,Dir,TI,_Origin,Thm,_),
    var(Tick2),
    instantiate_type_variables(TI,Hyps),

    /* it is possible that type variables will not be instantiated by
       the above.  For example, consider rewriting f(nil)<=>q with all
       t. f(nil)<=>(nil=nil in t list).  The rewritten term is
       (nil=nil in T list), and the context of the rewrite is
       insufficient to deduce T.  In these situations it is crucial
       that the rewriting does not continue since the term is
       ill-formed.  */
    ground(S),
    (Cond = [] -> true; call(Elem,Hyps==>Cond)).
    %% No cut here since other conditions may be imposed on the rule
    %% applied (e.g., polarity).
    
rt(Pos,Term,_,_,Term,node(cross,[]),_Hyps,_Elem) :-
    atomic(Term),!,
    Pos = [].

rt([N|Pos],Term,node(Tick,ArgsL),Ref, NewTerm,
   node(Applied,NewArgsL),Hyps,Elem) :-
    var(Tick),
    Term =.. [F|Args],
    rt_(Args,1,N,Pos,ArgsL,NewArgs,NewArgsL,Applied,Ref,Hyps,Elem),
    %% tail call seems no more efficient
    NewTerm =.. [F|NewArgs].


/* as rt/_, but innermost-first redex.   THIS CODE HAS NOT BEEN TESTED */
rt_inout(NPos,Term,node(Tick,ArgsL),Ref, NewTerm,
   node(Cross,NewArgsLFinal),Hyps,Elem) :-
    compound(Term),
    var(Tick),
    Term =.. [F|Args],
    rt_inout_(Args,1,N,Pos,ArgsL,NewArgs,NewArgsL,Applied,TheRef,Hyps,Elem),
    (Applied == cross ->			% no redex found
     (   (Pos = [],
	  reduction_rule(Term,node(Tick,NewArgsL),
			 NewTerm,node(_,NewArgsLFinal),Cond,Dir,TI,_Origin,Thm,_),
	  instantiate_type_variables(TI,Hyps),
	  Ref = [Thm,Dir],
	  (Cond = [] -> true; call(Elem,Hyps==>Cond))) -> true;
	 (Cross = cross,
	  NewTerm =.. [F|NewArgs],
	  Ref = TheRef,
	  NewArgsLFinal=NewArgsL))
      ;						%redex found
     (NPos = [N|Pos],
      NewTerm =.. [F|NewArgs],
      Ref = TheRef,
      NewArgsLFinal=NewArgsL)).
		 
	 
/*rt_inout([],T,node(Tick,Ts),[Thm,Dir],S,node(Sl,Ss),Hyps,Elem) :-
    var(Tick),
    %% This base case clause has to do some manipulation to ensure
    %% that labelling information on terms bound to variables in the
    %% reduction rule is propagated from T into S.  For example,
    %% rewriting s(x*)=s(y+) into x=y, using the cancellation rule for
    %% s, should copy the annotation (* and +) on the terms x and y
    %% into the reduct x=y.  Otherwise it will be lost.  See
    %% processing of reduction rules in lib_load/_ and add_rule/_.
    reduction_rule(T,node(Tick2,Ts),S,node(Sl,Ss), Cond,Dir,TI,_Origin,Thm,_),
    var(Tick2),
    instantiate_type_variables(TI,Hyps),
    (Cond = [] -> true; call(Elem,Hyps==>Cond)).
    %% No cut here since other conditions may be imposed on the rule
    %% applied (e.g., polarity).
*/    
rt_inout([],Term,node(_,_),_,Term,node(cross,[]),_Hyps,_Elem) :-
    atomic(Term),!.


/* Try to rewrite one of the As.  Succeed when one has been rewritten,
   for elements of As that cannot be rewritten, recover the complete,
   fully crossed labelling.  */
rt_([],_M,_N,_Pos,[],[],[],cross,_,_Hyps,_Elem).
rt_([A|As],M,N,PosFinal,[node(Tick,L)|Ls],
    [NewA|NewAs],[node(NewALabel,NewAArgsLabel)|NewLs],
    FlagFinal,Ref,Hyps,Elem) :-
    var(Tick),!,
    %% There is no point in trying to rewrite A if it is crossed, so
    %% in the head we explicitly ensure that it has the form var L
    !,						% to allow use of clam_error
    rt(Pos,A,node(Tick,L),LocalRef,NewA,
       node(NewALabel,NewAArgsLabel),Hyps,Elem),
    (A==NewA
	 -> (MM is M + 1,
	     rt_(As,MM,N,PosFinal,Ls,NewAs,NewLs,FlagFinal,Ref,Hyps,Elem))
	 ;  (PosFinal = Pos, M = N, NewLs = Ls,
	     Ref = LocalRef, NewAs = As)).
rt_([A|As],M,N,Pos,[node(cross,Crossed)|Ls],[A|NewAs],
    [node(cross,Crossed)|NewLs],Applied,Ref,Hyps,Elem) :-
    %% A is crossed, so skip it and search for another term.  Notice
    %% that if A is labelled with tick the clause above will
    %% succeed since rt will, with NewALabel = cross.
    !,						%only for clam_error
    MM is M + 1,
    rt_(As,MM,N,Pos,Ls,NewAs,NewLs,Applied,Ref,Hyps,Elem).
rt_([_|_],_,_,_,[_|_],[_|_],[node(_,_)|_],_,_,_,_) :-
    clam_internal_error('rt_/10.4',[]).

/* Try to rewrite one of the As.  Succeed when one has been rewritten,
   for elements of As that cannot be rewritten, recover the complete,
   fully crossed labelling.  */
rt_inout_([],_M,_N,_Pos,[],[],[],cross,_,_Hyps,_Elem).
rt_inout_([A|As],M,N,PosFinal,[node(Tick,L)|Ls],
    [NewA|NewAs],[node(NewALabel,NewAArgsLabel)|NewLs],
    FlagFinal,Ref,Hyps,Elem) :-
    var(Tick),!,
    %% There is no point in trying to rewrite A if it is crossed, so
    %% in the head we explicitly ensure that it has the form var L
    !,						% to allow use of clam_error
    rt_inout(Pos,A,node(Tick,L),LocalRef,NewA,
       node(NewALabel,NewAArgsLabel),Hyps,Elem),
    (A==NewA
	 -> (MM is M + 1,
	     rt_inout_(As,MM,N,PosFinal,Ls,NewAs,NewLs,FlagFinal,Ref,Hyps,Elem))
	 ;  (PosFinal = Pos, M = N, NewLs = Ls,
	     Ref = LocalRef, NewAs = As)).
rt_inout_([A|As],M,N,Pos,[node(cross,Crossed)|Ls],[A|NewAs],
    [node(cross,Crossed)|NewLs],Applied,Ref,Hyps,Elem) :-
    %% A is crossed, so skip it and search for another term.  Notice
    %% that if A is labelled with tick the clause above will
    %% succeed since rt will, with NewALabel = cross.
    !,						%only for clam_error
    MM is M + 1,
    rt_inout_(As,MM,N,Pos,Ls,NewAs,NewLs,Applied,Ref,Hyps,Elem).
rt_inout_([_|_],_,_,_,[_|_],[_|_],[node(_,_)|_],_,_,_,_) :-
    clam_internal_error('rt_/10.4',[]).


/* Reflexive transitive closure of rt.  For a terminating rewrite
   relation this can be used to compute the normal form, S, of T. Elem
   is a predicate of arity 1 used to prove conditions of rules.  */
reduction_rtc(T,S,Tactic,Hyps,Elem) :-
    rt_tc(T-_,S-_,_,Tactic,Hyps,Elem),!.

reduction_rtc(T,S) :-
    reduction_rtc(T,S,_,[],immediate).

/* Transitive closure of rt.  As reduction_rtc/3, but requires that S
   is not already in normal form.  This is useful when used inside a
   method which is iterated with other methods (e.g., symbolic
   evaluation).  Elem is a predicate of arity 1 used to prove
   conditions of rules. */
reduction_tc(T,S,Tactic,Hyps) :-
    reduction_tc(T,S,Tactic,Hyps,immediate).
reduction_tc(T,S,Tactic,Hyps,Elem) :-
    rt_tc(T-_,S-_,Rewritten,Tactic,Hyps,Elem),!,
    Rewritten == rewritten.

/* Reflexive transitive closure of rt_inout.  For a terminating rewrite
   relation this can be used to compute the normal form, S, of T. Elem
   is a predicate of arity 1 used to prove conditions of rules.  */
reduction_inout_rtc(T,S,Tactic,Hyps,Elem) :-
    rt_inout_tc(T-_,S-_,_,Tactic,Hyps,Elem),!.

/* Transitive closure of rt_inout.  As reduction_inout_rtc/3, but
   requires that S is not already in normal form.  This is useful when
   used inside a method which is iterated with other methods (e.g.,
   symbolic evaluation).  Elem is a predicate of arity 1 used to prove
   conditions of rules. */
reduction_inout_tc(T,S,Tactic,Hyps,Elem) :-
    rt_inout_tc(T-_,S-_,Rewritten,Tactic,Hyps,Elem),!,
    Rewritten == rewritten.
    

/* +U and ?S are related under the reflexive transitive closure of rt.
   Rewritten is set to 'rewritten' if one or more rewrites are
   applied, for a terminating rewrite relation, this is when S and U
   are different.

   ?Sl and ?Ul are the labellings for S and U.  */
rt_tc(S-Sl,U-Ul,Rewritten,Tactic,Hyps,Elem) :-
    %% compute S ->* U via S -> T and then recurse for T ->* U
    rt(Pos, S,Sl, [Rule,TypeDir], T,node(Tl,TlArgs),Hyps,Elem),
    (\+ var(Tl)
      -> (U = T, Ul = node(Tl,TlArgs), Tactic=[])
      ;  (reverse(Pos,RPos),			%more work to do
	  polarity_compatible(S, RPos, TypeDir),
	  Rewritten=rewritten,
	  Tactic = [reduction(RPos,[Rule,TypeDir])|RestTac],
	  rt_tc(T-node(Tl,TlArgs),U-Ul,_,RestTac,Hyps,Elem))). 

rt_inout_tc(S-Sl,U-Ul,Rewritten,Tactic,Hyps,Elem) :-
    %% compute S ->* U via S -> T and then recurse for T ->* U
    rt_inout(Pos, S,Sl, [Rule,TypeDir], T,node(Tl,TlArgs),Hyps,Elem),
    (\+ var(Tl)
      -> (U = T, Ul = node(Tl,TlArgs), Tactic=[])
      ;  (reverse(Pos,RPos),			%more work to do
	  polarity_compatible(S, RPos, TypeDir),
	  Rewritten=rewritten,
	  Tactic = [reduction(RPos,[Rule,TypeDir])|RestTac],
	  rt_inout_tc(T-node(Tl,TlArgs),U-Ul,_,RestTac,Hyps,Elem))). 

/* Slabel and Tlabel are labellings for terms S and T, such that
   variables in S and T are uniformly labelled with unique variables
   in Slabel and Tlabel, and function symbols in S and T are labelled
   with renamings of Label. Such labellings are used during labelled 
   term rewriting to propagate labelling annotations across rewrite
   rules.  */ 
rule_labelling(S,Sl,T,Tl) :-
    term_labels(S,[],LS),
    term_labels(T,LS,LST),
    subterm_label(S-Slabel,LST),
    subterm_label(T-Tlabel,LST),
    copy_term(Slabel-Tlabel,Sl-Tl).
term_labels(T,LS,LS) :-
    subterm_label(T-_,LS),!.
term_labels(T,LS,[T-node(_FreshVar,[])|LS]) :-
    atomic(T),!.
term_labels(V,LS,[V-V|LS]) :-
    var(V),!.
term_labels(T,LS, [T-node(_FreshVar,Labelling) | NewLS]) :-
    T =.. [_|As],
    term_labels_(As,Labelling,LS,NewLS).

term_labels_([],[],LS,LS).
term_labels_([T|As],[Tl|Tls],LS,NewLS) :-
    term_labels(T,LS,TmpLS),
    subterm_label(T-Tl,TmpLS),
    term_labels_(As,Tls,TmpLS,NewLS).

subterm_label(T-LL,[TT-LL|_LS]) :-
    T == TT,!.
subterm_label(T-LL,[_|LS]) :-
    subterm_label(T-LL,LS).


/* COMPUTATION */

/* Evaulates ground (variable-free) A using topmost-rightmost strategy
   using available compuatation rules to some normal form V (typically
   V is a value).  'Computation rules' are in fact those definitional
   rules in the rewrite database that are equ/equiv, used from
   left-to-right.  Propositional rules are hard-wired.  */

   :- dynamic ev_rec/2.
   
% ev(_,_) :- check_time_limit,fail.
ev(A,B) :- ev_rec(A,B),!.
/* Some Oyster stuff */

/* the following types are inhabited */
ev(atom,{true}) :- !.
ev(u(_),{true}) :- !.
ev(pnat,{true}) :- !.
ev(int,{true}) :- !.
ev(_ list,{true}) :- !.
ev(_ tree,{true}) :- !.
ev(A<B,V) :-			%less on the integers
        ev(A,Av), integer(Av),
	ev(B,Bv), integer(Bv),
	(Av < Bv -> V = {true}; V = void).
ev(0<*s(_),{true}):- !.			%less on the pnats
ev(s(_)<*0,void):- !.
ev(0<*0,void):- !.
ev(A<*B,V) :-
        ev(A,Av),
	ev(B,Bv),
	ev(Av<*Bv,V).
ev(A=A in _,{true}) :- !.
ev(A=B in _,V) :- !,
	ev(A,Av),
	ev(B,Bv),
	(Av == Bv -> V = {true}; V = void).
ev(A=>B, V) :- !,
	ev(A,Av),
	(Av = void -> V = {true};
	    (ev(B,Bv),
	    (Bv = {true} -> V = {true}; V = void))).
ev(A<=>B, V) :- !,
	ev(A,Av),
	ev(B,Bv),
	(Av == Bv -> V = {true}; V = void).
ev(A\B, V) :- !,
	ev(A,Av),
	(Av = {true} -> V = {true};
	    (ev(B,Bv),
	    (Bv = {true} -> V = {true}; V = void))).
ev(A#B, V) :- !,
	ev(A,Av),
	(Av = void -> V = void;
	    (ev(B,Bv),
	    (Bv = {true} -> V = {true}; V = void))).

ev(T,V) :-
    compound(T),!,
    T =.. [F|As],
    ev_map(As,Bs),
    TT =.. [F|Bs],	
    (((rewrite_rule(TT,S, Cond,Dir,TI,Origin,Thm,_),
	(Dir = equiv(left); Dir = equ(_,left)),
	\+ Origin = Thm,			%its a computation rule
	instantiate_type_variables(TI,[]),
	(Cond = [] -> true; ev(Cond,{true}))) ->
	ev(S,V));
     (V = TT)).
    


ev(T,T).

ev_map([],[]).
ev_map([A|As],[Av|Bs]) :-
    ev(A,Av),
    assert(ev_rec(A,Av)),
    ev_map(As,Bs).


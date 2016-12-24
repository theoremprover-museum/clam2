/*
 * @(#)$Id: so.pl,v 1.33 2008/05/21 14:14:14 smaill Exp $
 *
 * $Log: so.pl,v $
 * Revision 1.33  2008/05/21 14:14:14  smaill
 * update for sicstus4
 *
 * Revision 1.32  1998/07/27 12:12:35  img
 * Conditional tracing messages
 *
 * Revision 1.31  1998/06/25 10:42:53  img
 * Slight speed improvements
 *
 * Revision 1.30  1998/05/13 12:58:43  img
 * list_to_set -> remove_dups
 *
 * Revision 1.29  1998/03/16 10:26:27  img
 * extend_registry_prove/3: in order to be more parsimonious with the
 * atom table use make_ground at the top-level rather than allowing
 * registry_ to ground variables using gensym.
 *
 * Revision 1.28  1998/02/05 18:02:27  img
 * registry_/6: head_args/3 skips typed equality (fixed)
 *
 * Revision 1.27  1997/09/26 14:55:14  img
 * prove/5 -> rpos_prove/5 (and family); delete/3 -> restrict_status/3
 * (when used in that role); restrict_status/3 added.
 *
 * Revision 1.26  1997/07/09 15:20:46  img
 * Drop self-tests in consistency predicates.
 *
 * Revision 1.25  1997/07/01 16:25:17  img
 * Exploit fact that inequalities cannot be present in registry unless >= is present also.
 *
 * Revision 1.24  1997/06/25 10:33:50  img
 * conjunction/10 split into two new predicates, conjunction/9 and
 * conjunction_cong/9.  The former is as _/9 is the same as _/10, only it
 * does not have a parameter which is the predicate to be used to compare
 * elements: it always uses compare_all/_.  conjunction_cong/9 always
 * uses congruent_all/_.  The reason is that the congruent_all does not
 * need to check S > (each element of Ts) in the lex. case, as
 * conjunction/10 did (incorrectly).  Predicates for the consistent
 * extension of the registry have been speeed up, mainly by incremental
 * checks, and passing the transitive closure of the quasi-precedence to
 * avoid recomputing it repeatedly.
 *
 * Revision 1.23  1997/06/20 12:26:52  img
 * Split precedence into >= and =\= parts (with a view to new datastructures).  consistent/5 added: incremental consistency checks on extended registries.
 *
 * Revision 1.22  1997/06/18 15:01:59  img
 * Some speed-ups; Pass Closure when it is known; drop _proper prefix on relation tests.
 *
 * Revision 1.21  1997/06/17 15:36:27  img
 * Variable renamings to drop Proper-ness.
 *
 * Revision 1.20  1997/06/17 14:32:43  img
 * Pass registry explicitly.
 *
 * Revision 1.19  1997/04/07 11:41:15  img
 * rationalize code for equal length lists.
 *
 * Revision 1.18  1997/01/14 10:44:26  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.17  1996/12/04 12:20:34  img
 * in_prec_relation_star/3: reflexive case missing
 * terminating/3: from wave_rules.pl
 *
 * Revision 1.16  1996/07/09 14:35:17  img
 * Efficiency improvements---mainly due to: recoding of
 * in_prec_relation/2 and family; in conjunction/_ the lexicographic
 * comparison is moved out of an inner loop and done only once.
 *
 * Revision 1.15  1996/06/19  12:52:18  img
 * Use exp_at rather than path_arg for Sicstus compatibility.
 *
 * Revision 1.14  1996/06/12  11:29:55  img
 * Tidying up and small bug fix in head/2.
 *
 * Revision 1.13  1996/05/21  14:33:43  img
 * speed improvements in consistent/2 (remove uncommitted statuses)
 *
 * Revision 1.12  1996/05/21  12:51:10  img
 * debug info removed
 *
 * Revision 1.11  1996/05/21  12:50:03  img
 * typo in equivalence case of in_prec_relation_star/3
 *
 * Revision 1.10  1996/05/14  18:20:16  img
 * added subterm check for negative case in prove.  improving bottleneck
 * in consistent/2 by passing the closure around.
 *
 * Revision 1.9  1996/04/19  10:05:27  img
 * remove debugging info
 *
 * Revision 1.8  1996/04/11  18:59:31  img
 * initial_registry/6 replaced with registry/6; registry/6 only produces
 * a new status function and maps variables to constants---the precedence
 * is no longer a parameter.  extend_registry_prove/4: extends a registry
 * (via registry/6 and prove/5) in order to embrace termination of a pair
 * of terms.
 *
 * The `Stat' argument to conjunction/_ has been removed: this is computed
 * locally rather than in the caller;  the reason this is possible is
 * that I was thinking that Stat ought to reflect the equivalence of
 * F and G, but of course it should reflect their identity.  Some extra
 * documentation added to the new conjunctin/9; made the treatment of
 * _ and undef similar by means of all_statuses/2.
 *
 * Revision 1.7  1996/04/05  11:57:37  img
 * working version, as in the BB note
 *
 * Revision 1.6  1996/02/02  10:39:51  img
 * First working version of EPOS;  CUT in partial case (F>=G).  (Example
 * at end of the file.)
 *
 * Revision 1.5  1996/02/02  10:15:29  img
 * duplicate solutions from compare_all and congruent_all removed
 * (albeit in an ugly way).
 *
 * Revision 1.4  1996/02/02  09:46:48  img
 * mildly working version;  duplicate solutions from compare_all and
 * congruent_all.
 *
 * Revision 1.3  1996/01/30  12:41:27  img
 * finished precedence extension support.  Now the problem is that
 * congruence (and elsewhere) tries to assign equal precedece to variables
 * (which are represented as constants).
 *
 * Revision 1.2  1996/01/26  12:57:43  img
 * prove_map/4 replaces rpos_quasi and rpos_strict;  initial_registry/3
 * added to lift prove from ground terms to non-ground terms.  This
 * is accompanied by removal of all variable support in terms, since
 * initial_registry maps variables to constants.
 *
 * Revision 1.1  1996/01/25  16:18:22  img
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: so.pl,v 1.33 2008/05/21 14:14:14 smaill Exp $').

/* Implementation of simplification ordering "recursive path ordering
 * with status".
 * 
 * These rules are based on the presentation in Steinbach's thesis
 * (Steinbach 1994).  See also Jouannaud 1992 (MIT/TM/219) for a more
 * efficient implementation of multiset ordering.  See also BB note
 * 1073 for comments pertaining to application in Clam.
 * 
 * RPOS is based on a quasi-precedence, >= and a status function tau.
 *   ?Tau is a mapping of function symbols to status.
 *   ?Prec is a quasi-precedence relation on function symbols.
 *  
 * Out of interest, keep a record of the proof.
 *                                                    (img/mrg/jan-96)
 */

/* We need these to be able to curry prove/4 via maplist later.  (Just
   a matter of argument order.)  */
rpos_quasi(TauPrec,NTP,Vars,Proof, S,T) :-
    rpos_prove(S >= T,TauPrec,NTP,Vars,Proof).
rpos_strict(TauPrec,NTP,Vars,Proof,S,T) :-
    rpos_prove(S > T, TauPrec,NTP,Vars,Proof).

/* Extend the registry so that S > T.  Note that Tau must be a proper
   list; Prec may be improper  */
extend_registry_prove(Tc-Prec,NTauC-NPrec,ST) :-
    copy_term(ST,SSTT),
    metavars(SSTT,MVars),
    make_ground(SSTT-MVars),
    remove_dups(MVars,Vars),
    map_list(Vars,Var:=>Var/ms,Tv),
    registry_pairs([],Tc,Tv,[SSTT],TcN,TvN),	% [] assumes no vars
    append(TcN,TvN,Tau),
    rpos_prove(SSTT,Tau-Prec,NTau-NPrec,Vars,_),
    delete_all(TvN,NTau,NTauC).

/* Orient a set of equations/implications according to EPOS and Tc and
   Prec.  Eqs is a list of equations (S=T) and implications (S=>T)
   that can be oriented S:=>T or (in case of = only) T:=S according to
   EPOS. 

   NTP is an extension of TP (a registry) as required to orient all
   these equations.  Rewrites is the resulting set of rewrite rules;
   Prfs is list of proofs.

*/
rew_sys(NTP,Prfs,RWS,Eqs) :-
    %% make a copy of the equation so that we don't lose the variables
    copy_term(Eqs,EqsCopy),
    registry_pairs(Vars,[],[],Eqs,Tc,Tv),	% Eqs is now ground
    %% Tc is the status function Tau extended to cover function
    %% symbols appearing in Eqs;  Tv is extension required to cover
    %% variables in Eqs: we need both to form a status function for
    %% the ordering.
    append(Tc,Tv,Tcv),
    rew_sys_(Tcv-[],NTP,Prfs,RWS,EqsCopy,Vars,Eqs).

rew_sys_(TP,TP,[],[],[],_,[]).
rew_sys_(TP,NTP,[Prf|Prfs],[SC:=>TC|RWS],[SC=TC|EqsCopy],Vars,[S=T|Eqs]) :-
    rpos_prove(S>T, TP,NTP2,Vars, Prf),
    rew_sys_(NTP2,NTP,Prfs,RWS,EqsCopy,Vars,Eqs).
rew_sys_(TP,NTP,[Prf|Prfs],[TC:=>SC|RWS],[SC=TC|EqsCopy],Vars,[S=T|Eqs]) :-
    rpos_prove(T>S, TP,NTP2,Vars, Prf),
    rew_sys_(NTP2,NTP,Prfs,RWS,EqsCopy,Vars,Eqs).
rew_sys_(TP,NTP,[Prf|Prfs],[TC:=>SC|RWS],[SC=>TC|EqsCopy],Vars,[S=>T|Eqs]) :-
    rpos_prove(T>S, TP,NTP2,Vars, Prf),
    rew_sys_(NTP2,NTP,Prfs,RWS,EqsCopy,Vars,Eqs).

/* Orient equation S=T by proving S>T and/or T>S */
orient(TP,NTP,Prf,left_to_right,S=T) :-
    rpos_prove_map(TP,NTP,[Prf], [S>T]).
orient(TP,NTP,Prf,right_to_left,S=T) :-
    rpos_prove_map(TP,NTP,[Prf], [T>S]).


/* map rpos_prove down pairs of terms */
rpos_prove_map(Tau-Prec,NTP,Proofs, ProblemList) :-
    registry_pairs(Vars,Prec,Tau,ProblemList,Tc,Tv),
    append(Tc,Tv,TauExt),
    rpos_prove_map_(TauExt-Prec,NTP,Proofs, Vars,ProblemList).

/* Map rpos_prove along a list of ground terms */
rpos_prove_map_(TauPrec,TauPrec,[], _Vars,[]).
rpos_prove_map_(TauPrec,NTP2,[Prf|Proofs], Vars,[Prob|ProblemList]) :-
    rpos_prove(Prob,TauPrec,NTP,Vars,Prf),
    rpos_prove_map_(NTP,NTP2,Proofs, Vars,ProblemList).



             /* EXTENSIBLE RECURSIVE PATH ORDERING WITH STATUS */

/* S is greater than or equivalent to T under Prec and Tau and
   simplification ordering RPOS.  If Prec and Tau are unterminated
   lists, they will be extended were possible.  Vars is a list of
   constants, possibly appearing in S and T, which are to be treated
   as variables.  Proof is a record of the proof.  */
rpos_prove(S =< T,TauPrec,NTP,Vars,Proof) :-
    rpos_prove(T >= S, TauPrec,NTP,Vars,Proof).
rpos_prove(S >= T,TauPrec,NTP,Vars,Proof) :-
    rpos_prove(S = T, TauPrec,NTP, Vars,Proof).	% CUT?
rpos_prove(S >= T,TauPrec,NTP,Vars,Proof) :-
    rpos_prove(S > T, TauPrec,NTP,Vars,Proof).

rpos_prove(T = T, TP,TP, _Vars,identity) :-
    %% Identical terms are congruent.
    !.
rpos_prove(A=B, _,_, _, _) :-
    %% A and B cannot be equivalent if A is a subterm of B.
    exp_at(B,[_|_],A),!,fail.
rpos_prove(A=B, _,_, _, _) :-
    %% A and B cannot be equivalent if B is a subterm of A.
    exp_at(A,[_|_],B),!,fail.
rpos_prove(S = T, TauPrec, NTP,Vars,equivalent) :-
    congruent(TauPrec,NTP,Vars,S,T).

/* rpos_prove(+S > +T, ?Tau-?Prec, NewTau-NewPrec, +Vars, ?Proof): S is
   strictly greater than T under the simplification ordering
   "recursive path ordering with status".  NewTau is a mapping
   describing the status functions, NewPrec is the precedence
   relation. These are extensions of Tau and Prec as required, to show
   reduction.  These pairs are called a registry: the registry must be
   consistent (as described by consistent/2). Prec is a pair: a
   quasi-ordering (reflexive and transitive) together with an
   inequality relation (irreflexive and symmetric).  The inequality
   relation is used in this context because we are dynamically
   extending the precedence; we might extend f>=g into either f=g (by
   adding g>=f to the quasi-ordering) or into f>g (by adding f=\=g).
   Normally, f>g is defined to be f>=g and not(g>=f), but this CWA is
   non-monotonic since then adding g>=f denies f>g.  =\= (inequality)
   makes explicit that f and g are different: f>g iff f>=g and f=\=g.
   >= and =\= are kept together in Prec.

   Proof is a record of the proof rules (given below) to establish
   this.

   S and T must be ground, though (zero-arity) constants appearing in
   Vars will be taken to stand for variables in terms of the registry.
   That is: x=\=y for distinct variables (= constants) x and y (no
   other relation holds between x and y), and x=x for all variables x.
   This is more efficient that carrying around this information in the
   registry.  initial_registry/6 shows how Vars can be constructed
   according to the above lifting regime (but note it is NOT kept as
   part of the registry, only computed there).

   When Tau and Prec cannot justify reduction, rpos_prove/5 will attempt to
   extend them incrementally (into NewTau/NewPrec).  This is referred
   to in the code below as "extending" the registry.  

   I have inserted comments which pertain to the "extensible" version
   of RPOS (called EPOS Forgaard84).  

   I use >> and >* in the comments for mutliset and lexicographic
   extension, respectively. 

   I will say it again: rpos_prove and friend WILL NOT WORK on non-ground S
   and T.  */

rpos_prove(S < T, TauPrec,NTP,Vars,Proof) :-
    rpos_prove(T > S,TauPrec,NTP,Vars,Proof).
/* These are some quickly testable subclasses */
rpos_prove(V > _T, _,_, Vars, lemma) :-
    %% A variable cannot be bigger than anything, since variables are
    %% only related by the "registry" to themselves.  We bypass quite
    %% a bit of computation by avoiding the registry and simply
    %% checking if S is a (constant denoting a) variable.
    member(V,Vars),!,fail.
rpos_prove(S > V, TP,TP, Vars, _) :-
    %% If V is a variable, the only way S>V is when S contains V as a
    %% proper subterm.  This is because V is unrelated to all symbols
    %% different from itself, and at least one symbol in S must be
    %% related to V, by the nature of EPOS.
    %%     In the case where V is a proper subterm of S, we see (by an
    %% argument detailed in the next but one clause) that S>V.
    member(V,Vars),!,
    exp_at(S,[_|_],V),!. %this is a least-commitment to the registry, 
                         %    so don't backtrack
rpos_prove(S > T, _,_, _Vars, _) :-
    %% If S is a proper subterm of T, S cannot be larger than T, for
    %% any terms S and T.  (We do not decide positive cases since that
    %% wouldn't give a proof---maybe that's OK, however, so it could
    %% be done to improve speed.)
    exp_at(T,[_|_],S),!,fail.			% cons ensures proper subterm
rpos_prove(S > T, TP,TP, _Vars, lemma) :-
    %% If S is a proper subterm of T, there always exists a proof that
    %% T>S (not using this rule), and furthermore, there exists a
    %% proof which will not extend the registry.  (Simply use the
    %% subterm property and congruence.)
    exp_at(S,[_|_],T),!.
rpos_prove(S > T, TP,NTP, Vars, subterm(Si) then Proof) :-
    %% if S is compound, we can take it apart and show that one of its
    %% subterms is >= to T.  In which case, by transitivity and the
    %% subterm property, we have S > T.  Speed improvement: for S to be
    %% greater than T (a variable) it must be the case that T appears
    %% in S... we could check this here.
    compound(S), args(S,Sargs),
    list_to_set(Sargs,Sset),
    member(Si,Sset),			%drop identical arguments
    rpos_prove(Si >= T, TP,NTP, Vars,Proof).
/* EPOS: the following clause is a conjunction of the two which
   follow.  We can proceed on the basis of F>=G providing the
   casesplit F=G holds. Inefficient since it duplicates work in case
   of only one of the branches being provable: it is then re-done
   later.  TODO: drop the next two clauses and drive them both from
   here.  */
/*  I don't like this clause.  It gives too much weight to the Prec 
rpos_prove(S > T, TP, TP3, Vars,
      partial(F>=G) then [StrictProof,EqProofs]) :-
    \+ member(T,Vars),
    \+ atomic(S),
    head_args(S,F,Ss), head_args(T,G,Ts),
    \+ F=G,
    in_extended_prec(F>=G,TP,Tau1-Prec1), % STRICT/NON-STRICT
    %% If we now have F=G because of the above addition of F>=G, there
    %% is no point in continuing with the strict (F>G) case.  Instead,
    %% fail and drop to the final clause for F=G.  Ditto for F>G.
    \+ in_prec_relation(F=G,Prec1),
    \+ in_prec_relation(F>G,Prec1),
    status(Tau1,F,FStat), status(Tau1,G,GStat),
    conjunction(Tau1-Prec1,TP2,F/FStat,G/GStat,S,Ss,Ts,Vars,EqProofs),
    (compound(T)
    -> (rpos_prove_map_forall(TP2, TP3, Vars, S, Ts,StrictProofs),
	StrictProof = (decomp(F>G) then StrictProofs))
      ; (TP3=TP2,StrictProof=decomp(F>G))), 
    %% **** This CUT reduces completeness: remove it if you want all
    %% **** solutions arising from alternative (less-general)
    %% **** registries. 
    !.						% CUT
*/
rpos_prove(S > T, TP,TP2, Vars, Proof) :-
    %% if the head of S is higher in the precedence than the head of
    %% T, and S is greater than all the subterms of T, we have S > T.
    %% If T is a "variable" G, there is no symbol F>G since G is
    %% unrelated by the registry to all symbols other than itself.
    \+ member(T,Vars),
    oyster_head(S,F), head_args(T,G,Ts),
    \+ F=G,
    in_extended_prec(F>G, TP,TP1),		% STRICT CASE
    (compound(T)
      -> (rpos_prove_map_forall(TP1, TP2, Vars, S, Ts,Proofs),
	  Proof = (decomp(F>G) then Proofs))
      ; (TP2=TP1,Proof=decomp(F>G))).		% if T is atomic we are done
          
rpos_prove(S > T, TP,TP2, Vars, extn(F/FStat=G/GStat) then Proofs) :-
    %% If the heads are equivalent, compare the arguments which must
    %% be greater for S > T.  If S is atomic we can fail.  The
    %% argument in that case is that neither args(S) >> _ nor args(S)
    %% >* _, by simple property of >> and >*.  If T is a variable,
    %% fail immediately, since vars are unrelated by the registry.
    \+ member(T,Vars),
    \+ atomic(S),
    head_args(S,F,Ss), head_args(T,G,Ts),
    in_extended_prec(F=G,TP,Tau1-Prec1),		% NON-STRICT CASE
    status(Tau1,F,FStat), status(Tau1,G,GStat),
    %% *EPOS* In case of an undefined status, we have to consider the
    %% conjunction of all three possibilities: ms, lr and lr, since we
    %% cannot proceed (without a commitment) unless we know that any
    %% of the three is suitable (we must ensure that any extensions
    %% subsequently made will not upset the ordering of previous
    %% terms).  Similarly, the precedence may be uncommited (where we
    %% have f >= g, but not g>=f or f=\=g) and we can proceed on this
    %% partial information: a conjunction of the cases for g>=f and
    %% f=\=g.  Then later commitment to either of these is sound. 
    conjunction(Tau1-Prec1,TP2,F/FStat,G/GStat,S,Ss,Ts,Vars,Proofs).

/* Extensions of the basic ordering */
rpos_prove(ms(Ss,Ts),TP,NTP, Vars,Proofs) :-
    multi_extension(TP,NTP,Vars,
		    congruent,
		    rpos_strict,
		    Ss,Ts,Proofs).
rpos_prove(lex(Tuple1,Tuple2),TP,NTP, Vars,Proofs) :-
    length(Tuple1,N), length(Tuple2,M),
    rpos_lex(N,M,TP,NTP,Tuple1,Tuple2,Vars,Proofs).


rpos_lex(0,M,TP,TP,_Tuple1,_Tuple2,_Vars,[]) :-
    M > 0,!.
rpos_lex(_N,_M,TP,NTP,[S|_],[T|_],Vars,[P]) :-
    rpos_strict(TP,NTP,Vars,P,S,T),!.
rpos_lex(N,M,TP,NTP2,[S|Ss],[T|Ts],Vars,[P|Proofs]) :-
    rpos_prove(S = T, TP,NTP1,Vars,P),!,		% earlier ones are equiv
    Np is N - 1,
    Mp is M - 1,
    rpos_lex(Np,Mp,NTP1,NTP2,Ss,Ts,Vars,Proofs).

/* Here is the Pettorossi version of multiset extension, in which it
 * is slightly easier to take account of an equivalence relation E on
 * terms (cf wave-rules.pl) */
multi_extension(TP,NTP,Vars,E,P,A,B,Proofs) :-
    mset_difference(TP,NTP1,Vars,E,A,B,AsB),
    \+ (AsB = []),		
    mset_difference(NTP1,NTP2,Vars,E,B,A,BsA),
    multi_extenstion_map(AsB,BsA,Proofs,NTP2,NTP,Vars,P).

multi_extenstion_map(_,[],[],TP,TP,_,_).
 multi_extenstion_map(AsB,[T/_|BsA],[multiset(S>T,Proof)|Proofs],TP,NTP2,Vars,P) :-
     mmember(S/_,AsB),
     /* try to keep the Registry unchanged, then we can CUT */
     Call =.. [P,TP,NTP,Vars,Proof,S,T],
     (Call -> TP == NTP;fail),!,
     multi_extenstion_map(AsB,BsA,Proofs,TP,NTP2,Vars,P).
multi_extenstion_map(AsB,[T/_|BsA],[multiset(S>T,Proof)|Proofs],TP,NTP2,Vars,P) :-
    mmember(S/_,AsB),
    /* need an extenstion, so no cut */
    Call =.. [P,TP,NTP,Vars,Proof,S,T],
    Call,
    multi_extenstion_map(AsB,BsA,Proofs,NTP,NTP2,Vars,P).



/* OLD:
map_list(BsA, (T/_):=>multiset(S>T,Proof),
	     (mmember(S/_,AsB),
	      call(P,Proof,S,T)),
	     Proofs).                  */

/* Here we extend our equivalence = to a congruence on terms.  The
   only interesting part of this is the need to incorporate the status
   function into the equivalence  */  
congruent(TP,TP,Vars,A,B) :-
    %% Variables are only congruent iff they are identical.
    (member(A,Vars);
     member(B,Vars)),
    !, A==B.
/*congruent(TP,Tau1-Prec1,Vars,A,B) :-
    atomic(A),atomic(B),!,
    in_extended_prec(A=B,TP,Tau1-Prec1),		% possibly extend
    %% if A and B are equivalent atoms, they can have any compatible
    %% status, including undef.  We try undef first since it is more
    %% general. 
    ((status(Tau1,A,undef),status(Tau1,B,undef));
     compatible_terms(Tau1,A,B)).
*/
congruent(TP,NTP,Vars,A,B) :-
    head_args(A,F,Fargs), head_args(B,G,Gargs),
    lengtheq(Fargs,Gargs),			% for both MS and Lex
    in_extended_prec(F=G, TP,Tau1-Prec1),		
    status(Tau1,F,Fstatus), status(Tau1,G,Gstatus),
    conjunction_cong(Tau1-Prec1,NTP,F/Fstatus,G/Gstatus,Fargs,Gargs,Vars,_).

/* Status functions.  A status function is represented as a finite
   mapping from function symbols to one of multiset, lex or undefined.
   Undefined is a special case for use with EPOS (treated as a
   conjunction of the other two cases).  Lex is parameterized from
   left to right or from right to left.  Other lex orderings are
   possible---change status/1 and status_eval/3.

   There are two styles of "undefined", one is an explicit status of
   "undef" which means that any one of the defined statuses may be
   used instead (e.g., later in some extension of the registry).  The
   other is an implicit representation where a Prolog variable
   indicates an uncommitted status.  These uncommitted variables may
   be instantiated (if needs be) to a proper status during a proof;
   however the search for a proof will not backtrack in an effort to
   leave such statuses uncommitted: if one branch of proof search can
   continue with a committment, that will happen, even if another
   branch would complete the proof without committment.  If you this
   level of control, you need to do it using "undef".
*/
is_status(lex(lr)).  is_status(lex(rl)).
is_status(ms).

status(Tau,Functor,Status) :-
    member(Functor/Status,Tau),!.

/* Status evaluation.  Other statuses functions could be added here,
   if you like.  */
status_eval(ms,List,MultiSet) :-
    list2mset(List,MultiSet).
/* below we are deliberately overloading lists as tuples. */
status_eval(lex(lr),Tuple,Tuple).
status_eval(lex(rl),Tuple,TupleRev) :-
    reverse(Tuple,TupleRev).

/* Check that the principle functors of terms A and B have compatible
   status.  */
compatible_terms(Tau,A,B) :-
    oyster_head(A,F), oyster_head(B,G),
    status(Tau,F,S1), status(Tau,G,S2),
    is_status(S1),is_status(S2),
    compatible(S1,S2).
compatible(S1,S2) :-
    var(S1),
    var(S2),!,
    S1=S2.
compatible(ms,ms).
compatible(lex(_),lex(_)).

/* Check that the registry is consistent (ie that it corresponds to a
   proper quasi-precedence, and that equivalent symbols are assigned
   compatible statuses.  Undefined status requires special treatment.

   NB. consistent does not instantiate any uncommitted registries; for
   example, [f/lex(_),g/undef] is consistent when f and g are
   equivalent.  This is sound provinding (as we do) that the
   particular committment of g to a fixed status is checked to be
   consistent.   For example, it would be incorrect to pick g/ms,
   since this is inconsistent.  One can read consistent/2 as "can be
   made consistent" rather than "all instantiations are consistent".  

   Uncommitted status assignments are removed from Tau before checking
   consistency, since these have no bearing on the outcome.  */
consistent(Tau,Prec) :-
    consistent_prec(Prec,Closure),
    consistent_status(Tau,Prec,Closure).

consistent_status(T,Prec,Closure) :-
    /* ground Closure outside forall/3 */
    if(var(Closure),precedence_closure(Prec,Closure)),
    no_uncommitted_statuses(T,Tau),
    /* Check that all equivalent symbols have compatible status */
    forall(F/Sf,Tau,
	   (Sf==ms				% ms must match ms or undef
	     -> forall(G/Sg,Tau,		% (note the use of unification)
		       if(in_prec_relation_star(F=G,Prec,Closure),
			  Sg=ms))
	     ; forall(G/Sg,Tau,			% lex case
		      if(in_prec_relation_star(F=G,Prec,Closure),
			 Sg=lex(_))))).

/* consistent(+Cond,+Closure,+Tau,+Prec,+D1,+D2,?NewPrec): Tau and Prec are a
   consistent registry.  NewPrec is a consistent extension of Prec in
   which Cond and all the conditions in D1 and D2 hold.  +Closure is
   either var or is taken to be the closure of Prec.  */
consistent(A=B,Closure,_Tau,Prec-INEQ,DP,[],DPPrec-INEQ) :-
    /* Assume: status(A) = status(B).  */
    /* Adding an equivalence.  Since we assume that A and B have
       compatible status, no status check is required (all symbols
       equivalent to A and B already in Tau are known to be
       consistent).  The precedence is inconsistent iff there is some
       F=H such that F>=G>=H and either F=\=G or G=\=H.  Adding A=B
       introduces new equalities, namely, all F=H such that A=F and,
       B=H since by transitivity and A=B, F=H.  Thus the precedence
       remains consistent iff for all G's such that A>=G>=B, neither
       A=\=G nor B=\=G.  */
    if(var(Closure),precedence_closure(Prec-INEQ,Closure)),
    forall {G \ (in_prec_relation_star(A >= G,Prec-INEQ,Closure), \+ G=A,
		 in_prec_relation_star(G >= B,Prec-INEQ,Closure), \+ G=B)}
	: (\+ in_prec_relation(A =\= G,Prec-INEQ,Closure),
	   \+ in_prec_relation(B =\= G,Prec-INEQ,Closure)),
    append(DP,Prec,DPPrec).

consistent(A>B,Closure,_Tau,Prec-INEQ,DP,[A=\=B],DPPrec-NewINEQ) :-
    if(var(Closure),precedence_closure(Prec-INEQ,Closure)),

    /* We are adding DP and DINEQ to acheive A>B. DP will normally be
       of the form A>=B, but may be empty.   Assume that A=B does not hold. 

       There is no need to check status assignments, since A>B cannot
       affect the equivalence relation.  

       In additon to A=\=B, other inequalities A=\=C may be required
       to ensure that A>C holds in the extension. (A>=C follows from
       A>=B and B>=C).  Obviously, adding A=\=C for all such C is
       inconsistent iff A=C, so we do that check on the precedence
       here too.  We need to add A=\=C to prevent later adding A=C;
       then we would have A=C and A>C which is inconsistent.  

       (In fact, it is not necessary to add these A=\=C: this test could
       be done on the fly as needed.  But in practice it is faster to
       do things this way.)

       (Note that A=\=C cannot already be in Prec since A=\=C is
       meaningless without the presence of A>=C: if A=\=C is present,
       then so must be A>=C, and hence A>C holds, contra to our
       assumption that it needs to be added.)  */

    findall(A=\=C,(in_prec_relation_star(B>=C,Prec-INEQ,Closure),
		   \+ C = B),NewDiff),
    /* check the consistency of these new inequalities (A=\=B is OK by assumption) */
    forall(X=\=Y,NewDiff, \+ in_prec_relation(X=Y,Prec-INEQ,Closure)),
    append([A=\=B|NewDiff],INEQ,NewINEQ),

    /* If DP is empty the consistency of the precedence is preserved
       if the inequalities above preserve it.

       The only way adding DP (= A>=B) can increase the number of
       equalities F=H, is if B>=A in Prec.  Proof: Assume F=H notin
       Prec, and B>=A notin Prec.  Hence either F>=H notin Prec or
       H>=F notin Prec.  Assume F>=H in Prec and H>=F notin Prec.  If
       F=H in PrecExt, F>=H and H>=F in PrecExt, but then H>=F must be
       of the form H>=...A>=B>=...>=F since A>=B is difference between
       Prec and PrecExt.  Then H>=A in Prec (not using A>=B) and B>=F
       in Prec (not using A>=B -- pick left and right-most A & B).
       Thus we have B>=F>=H>=A in Prec, which contradicts assumption
       B>=A notin Prec.  The other cases are similar.

       But we do not add A>B if B>=A, since this is contradictory.  So
       there are no new equalities F=H arising from addition of A>=B.
       Inconsistency arises then only by adding NewDiff and this is
       tested for above.  */
    append(DP,Prec,DPPrec).

consistent(A>=B,Closure,Tau,Prec-INEQ,[A>=B],[],DPPrec-INEQ) :-
    /* Adding A>=B can result in A=B or A>B.  So we check consistency
       of these cases by a recursive call.  */
    /* Adding A>=B only affects the equivalence relation when B>=A.
       If adding A>=B results in A=B, the status must be compatible.  
       If A=B does not result, the status remains consistent.
       For the precedence, adding A>=B in the presence of B>=A is the
       case we dealt with above.  */
    (in_prec_relation(B>=A,Prec-INEQ)
	 -> (/* check status */
	     status(Tau,A,As), status(Tau,B,Bs), compatible(As,Bs),
	     /* and call recursively */
	     consistent(A=B,Closure,Tau,Prec-INEQ,[A>=B],[],DPPrec-INEQ))

	 ;  (fail % in_prec_relation(B=\=A,Prec-INEQ) 
		 -> clam_error('Non-sensical q.p.')
		 ;  /* neither B>=A nor A=\=B are in Prec; no status
		    check is required  */
		 (DPPrec-INEQ = [A>=B|Prec]-INEQ,
		  consistent_prec(DPPrec-INEQ,_)))).
/*
consistent(_,_,Tau,Prec-INEQ,DP,DINEQ,NPrec-INEQ) :-
    append(DP,Prec,NPrec), append(DINEQ,INEQ,NINEQ),
    print('doing it the hard way'),nl,
    consistent(Tau,NPrec-NINEQ),
    clam_internal_error('Incremental consistency check (consistent/7)!').
*/

/* Prec is a consistent precedence.
   Normally this is trivial.  However, in the EPOS setting, we not
   only have a quasi-ordering >=, but an inequality relation =\=.
   These two must satisfy the following.
   if F > G and G >= H then F > H
   if F >= G and G > H then F > H
   which in terms of =\= is
   if (F >= G and G >= H) and (F=\=G or G=\=H) then F =\= H
   In a quasi-ordering, this condition is vacuous since it cannot be
   the case that H=F>G>=H since F>F is contradictory (F>=F and
   not(F>=F)).  Consistency then, can be seen as a means to ensure
   that >=, =\= implement a quasi-ordering.  */ 
consistent_prec_old(Prec,Closure) :-
    %% The following is rather messy, but it saves computing the
    %% transitive closure of Prec (upto) 4 times.  (See
    %% in_prec_relation_G/2 for explanation.)
    precedence_closure(Prec,Closure),
    forall {F-G-H \ (in_prec_relation_star(F >= G,Prec,Closure),
		     in_prec_relation_star(G >= H,Prec,Closure))}
	: (%print(F-G-H),nl,
	   ((in_prec_relation(F =\= G,Prec,Closure);
	     in_prec_relation(G =\= H,Prec,Closure))
		-> \+ in_prec_relation(F = H,Prec,Closure)
		; true)).
consistent_prec(Prec,Closure) :-
    %% The following is rather messy, but it saves computing the
    %% transitive closure of Prec (upto) 4 times.  (See
    %% in_prec_relation_G/2 for explanation.)
    if(var(Closure),precedence_closure(Prec,Closure)),
    forall {F-G-H \ (in_prec_relation_star(F = H,Prec,Closure),
		     \+ F = H,
		     in_prec_relation_star(F >= G,Prec,Closure),
		     \+ G=F,
		     in_prec_relation_star(G >= H,Prec,Closure),
		     \+ G=H)}
	: (\+ in_prec_relation(F =\= G,Prec,Closure),
	   \+ in_prec_relation(G =\= H,Prec,Closure)).

no_uncommitted_statuses([],[]).
no_uncommitted_statuses([_/T|Ts],Taus) :-
    var(T),!,
    no_uncommitted_statuses(Ts,Taus).
no_uncommitted_statuses([_/undef|Ts],Taus) :-
    !,no_uncommitted_statuses(Ts,Taus).
no_uncommitted_statuses([T|Ts],[T|Taus]) :-
    no_uncommitted_statuses(Ts,Taus).

/* Registry NTv \cup NTc is an extension of Tau to account
   for the variables Vars and functions appearing in TermList.  This
   predicate provides a convenient interface to RPOS on non-ground
   terms.  Vars is grounded in the process so making TermList suitable
   for rpos_strict, rpos_quasi and rpos_prove.  NTv is the part of the
   status function corresponding to the variables, and NTc covers
   functions.  This distinction is useful since EPOS is lifted to
   variable terms by extending Tau to cover them as if they were
   unique constants.  However in this scheme it is unnecessary  and
   unwanted to carry a huge registry around that records the entire
   history of variables: variables are local, not global.

   Working on TermList (i.e., accross many terms simultaneously) is
   more efficient than on terms singly because variables in common can
   be mapped to the same constants in the registry.  Term by term
   lifting would result in a larger registry and showing RPOS would be
   more expensive, but not stronger.

   Note: it is marginally more efficient to leave variables as
   variables (i.e., don't ground them) since they are known to have
   special properties concerningn Prec and Tau.  Grounding them means
   that we are forced to treat them as constants, and deduce those
   properties on the fly. This can be done slightly more quickly by
   passing Vars around, which allows one to quickly decide if a
   constant is, in fact, to be treated as a variable.

   Tau must be a proper list; Prec may be improper.
*/
registry([],Tc,Tv,[],Tc,Tv).
registry(Vars,Tc,Tv,[T|Ts],Tc3,Tv3) :-
    registry_(V1,Tc,Tv,T,Tc2,Tv2),
    registry(V2,Tc2,Tv2,Ts,Tc3,Tv3),
    union(V1,V2,Vars).

/* same as registry/6, but maps down a list of equations, implications
   or problems (>) */
registry_pairs([],Tc,Tv,[],Tc,Tv).
registry_pairs(Vars,Tc1,Tv1,[Pair|Ts],Tc4,Tv4) :-
    Pair =.. [_,S,T],
    registry_(V1,Tc1,Tv1,T, Tc2,Tv2),
    registry_(V2,Tc2,Tv2,S, Tc3,Tv3),
    registry_pairs( V3,Tc3,Tv3,Ts,Tc4,Tv4),
    union(V1,V2,V12),
    union(V3,V12,Vars).
    

registry_([Term],Tc,Tv,Term,Tc,[Term/ms|Tv]) :-	% extend Tv
    var(Term),!,				
    gensym('v',Term).

registry_([],Tc,Tv,Term,Tc,Tv) :-		% atoms done already
    member(Term/_,Tc),!.
registry_([],Tc,Tv,Term,Tc,Tv) :-
    member(Term/_,Tv),!.

registry_([],Tc,Tv,Term,[Term/ms|Tc],Tv) :-	% extend Tc
    atomic(Term),!.
registry_(Vars,Tc,Tv,Term,TcN,TvN) :-		% functions done already


/* head_args(Term,F,Args), % functions cannot be in Tv don't use head
    args since it treats equality specially, with the result that
    variables in the type don't get grounded (eeek).  This only causes
    a problem later because rpos_prove etc want ground terms.  */
    Term =.. [F|Args],
    member(F/_,Tc),!,
    registry(Vars,Tc,Tv,Args,TcN,TvN).   
registry_(Vars,Tc,Tv,Term,TcN,TvN) :-
%    head_args(Term,F,Args),
    Term =.. [F|Args],
    registry(Vars,[F/_|Tc],Tv,Args,TcN,TvN).
    
/* Define a quasi-precedence relation, Prec.  Prec is a list
   consisting of pairs of the form A>=B where >= is the
   quasi-precedence;  The following hold:

   A = B  iff A>=B and B>=A
   A > B  iff A>=B and not B>=A.  But since we want to avoid use of
   closure for negation, we make it explicit, =\=.  Thus we have:

   A = B  iff A>=B and B>=A
   A > B  iff A>=B and A =\=B.  (See BB note for more information.)

   The disadvantage of this is that we need to work harder to ensure
   that >= and =\= together make sense as a quasi-precedence relation. 

   >= is transitive and reflexive: here I have implemented >=* using
   Warshall's algorithm, because I assume it will be faster as >=
   becomes large.

   It is often the case that for many different symbols A and B, the
   precedence contains A=\=B.  For many pairs of symbols, this part of
   the relation can grow quite large when represented explicitly.  So
   instead they are represented in a separate set INEQ (carried around
   with the rest of the precedence) with the meaning that A in INEQ
   and B in INEQ implies A=\=B.  */

/* in_prec_relation(Pair,Prec).  See first if Pair is a member of
   Prec, otherwise compute the transitive closure, and check
   membership of that. (Use in_prec_relation_G/2 for enumerations.)
*/

in_prec_relation(Pair,Prec-INEQ) :- 
    !,in_prec_relation(Pair,Prec-INEQ,_).

in_prec_relation(_,_) :- 
    clam_error('Prec must be a pair of >= and =\\=').

/* as in_prec_relation/2, but Prec must be a proper list */
in_prec_relation(_,Prec-INEQ,_) :- 
    (var(Prec);var(INEQ)),!, 
    clam_error('in_prec_relation/2: internal error').
in_prec_relation(F=F,_Prec,_) :- 
    \+ var(F),!.
in_prec_relation(F>=F,_Prec,_) :- 
    \+ var(F),!.
in_prec_relation(F>=G,Prec-_,_) :- 
    memberchk(F>=G,Prec).			% quick tests
in_prec_relation(F=G,Prec-_,_) :- 
    memberchk(F>=G,Prec),
    memberchk(G>=F,Prec).
in_prec_relation(F=\=G,_Prec-INEQ,_) :- 
    \+ F==G,					% obviously
    %% Cut here since the last clause only computes the transitive
    %% closure---since  =\= is not transitive there is no need to
    %% waste effort on that.  Try fast look-up in INEQ first, then Prec
    !,
    (memberchk(F=\=G,INEQ); memberchk(G=\=F,INEQ)),!.

in_prec_relation(Pair,Prec,Closure) :-
    /* Try the transitive closure of >=. */ 
    (var(Closure) -> precedence_closure(Prec,Closure);true),
    in_prec_relation_star(Pair,Prec,Closure),!.

/* This version enumerates all solutions, ie works for non-ground
   Pair.  Again, only compute the Closure if that hasn't been done
   already.  */ 
in_prec_relation_G(Pair,Prec,Closure) :-
    (var(Closure) -> precedence_closure(Prec,Closure);true),
    in_prec_relation_star(Pair,Prec,Closure).

/* Enumerate solutions of Pair in Closure;  Pair may be non-ground;
   Prec is a proper list.  */
in_prec_relation_star(F=\=G,_Prec-INEQ,_Closure) :- 
    \+ F==G,
    %% this clause copied from in_prec_relation/3 because
    %% precedence_closure/2 does not deal with =\= 
    (member(F=\=G,INEQ); member(G=\=F,INEQ)).
in_prec_relation_star(V >= V,_Prec,_Closure) :-
    ground(V).
in_prec_relation_star(V1 >= V2,_Prec,Closure) :-
    member(V1-V2,Closure).
in_prec_relation_star(V1 = V2,_Prec,Closure) :-
    member(V1-V2, Closure),
    member(V2-V1, Closure).
in_prec_relation_star(V1 > V2,_Prec-INEQ,Closure) :-
    member(V1-V2,Closure),
    %% V1 and V2 are ground by now, so we can use once/1 without
    %% changing the solution set.
    once((member(V2=\=V1,INEQ); member(V1=\=V2,INEQ))). %symmetric

/* Pair is in the prec. relation Prec, allowing for Prec to be
   (consistently) extended to NewPrec.  Pair must
   be a ground term.  (TP= Tau-Prec, NTP=Tau-NewPrec.)  */
in_extended_prec(Pair,T1-P1,T2-P2) :-
    precedence_closure(P1,Closure),
    in_extended_prec(Pair,T1-P1,T2-P2,Closure).

in_extended_prec(Pair,T-P,T-P,Closure) :-
    in_prec_relation(Pair,P,Closure),!.

/* The following clauses deal with the extension of Prec with new
   elements which imply Pair.   Many of the check more properly should
   be in consistent/7, but some appear here for efficiency reasons,
   since they are computed anyway.  */

in_extended_prec(F=G,Tau-Prec,Tau-NewPrec,Closure) :-
    %% We can only extend with F=G if the statuses of F and G are
    %% compatible, so it may be necessary to extend Tau, or deny this
    %% extension.  Note that F and G can have a variable status.
    status(Tau,F,Fs), status(Tau,G,Gs), 
    \+ in_prec_relation(F=\=G,Prec,Closure),
    compatible(Fs,Gs),
    %% which one to add  depends:
    (in_prec_relation(F>=G,Prec,Closure)
	  -> DP=[G>=F]
	  ;  ((in_prec_relation(G>=F,Prec,Closure)
		   -> DP=[F>=G]
		  ;   DP= [G>=F,F>=G]))),
    %% Consistency checks should be done incrementally; need to think
    %% about that.
    consistent(F=G,Closure,Tau,Prec,DP,[],NewPrec),!.
in_extended_prec(F>G,Tau-Prec,Tau-NewPrec,Closure) :-
    %% We can only make F>G iff it is not the case that G>=F, and
    %% furthermore that F and G are not identical.
    \+ F==G,
    \+ in_prec_relation(G>=F,Prec,Closure),
    %% this means that we must ensure that both F>=G and F=\=G are in
    %% Prec.  If F>=G is not present, neither is F=\=G, since F=\=G is
    %% meaningless without F>=G (we check this for internal
    %% consistency). 
    (in_prec_relation(F>=G,Prec,Closure)
	 -> DP = []
	 ;  DP=[F>=G]),

/*    if(in_prec_relation(F=\=G,Prec,Closure),
       clam_error('Non-sensical quasi-precedence.')),*/
    consistent(F>G,Closure,Tau,Prec,DP,[F=\=G],NewPrec),!.
in_extended_prec(F>=G,Tau-Prec,Tau-NewPrec,Closure) :-
    consistent(F>=G,Closure,Tau,Prec,[F>=G],[],NewPrec).

/* We use some hacks to speed things up; Oyster specific.  This loses
   completeness.  */
oyster_head(_=_ in _,=) :-				% OYSTER SPECIFIC
    !.
oyster_head(A,F) :-
    A =.. [F|_].
args(A=B in _,[A,B]) :- !.
args(S,As) :-
    S =.. [_|As].
head_args(A=B in _,=,[A,B]) :- !.
head_args(A,F,Args) :-
    A =.. [F|Args].

/* Efficient version of append(L,D,P), (var(D); D==[]) */
is_improper(D,D,[]) :-
    (D == []; var(D)),!.
is_improper([L|Ls],D,[L|Ps]) :-
    is_improper(Ls,D,Ps).

/* It is necessary to extend both congruence and RPO to arguments.  In
   the case of status functions, these extensions must account for the
   status assigments.  For example, plus(a,b) and plus(c,d) are
   equivalent if plus has multiset status and {a,d} and {b,c} are
   equivalence classes.

   The trickery comes when the status functions are not decided upon:
   for soundness we attempt to rpos_prove all possible instantiations.
   This allows us to continue the proof with the least commitment to
   the refinement, in the knowledge that additional (necessary)
   refinements may be made by further extension.  "Least" is not
   unique; furthermore in the analysis here, we just choose at
   "random".

   conjunction/10 applies either lex or ms extension (of Pred) to Ss
   and Ts (term lists), depending upon the statuses FStat and GStat of
   their principle functors, F and G.  It is assumed that FStat and
   GStat are compatible since we assume that F and G are equivalent
   symbols.  (In fact this might not always be the case since the
   "partial" rule of EPOS calls conjunction/10 with the partial
   information F>=G.  But we proceed on the basis of equivalence.)

  In the case of an undef status, it is necessary to try all status
   assignments and succeed only if they all do.  Pred is expected to
   be compare_all (for strict RPOS) or congruent_all (for
   equivalence).

   Ground statuses other than undef are processed as expected.

   In the case of variable (including non-ground) statuses, we find
   the most general instantiation for which all ground instances are
   provable.  If such solution instances are incomparable, choose
   between them arbitrarily.  (Undef is not considered an instance of
   a variable status.).

   NB.  If F and G are the same symbol (F==G) the conjunctive form is
   slightly different since in that case it is legal to assign lex(_)
   status to F (and hence G) when only lex(lr)-lex(lr) and
   lex(rl)-lex(rl) pairs are provable.  It is meaningless to require
   (eg) lex(lr)-lex(rl), since lex(lr) and lex(rl) cannot be assigned
   simultaneously to the same function.  */

conjunction(Tau-Prec,NewTau-NewPrec,F/FStat,G/GStat,S,Ss,Ts,Vars,Prfs-Proofs) :- 
    /* Ss (the superterm of which is S) is greater than Ts */
    %% FGs is list of pairs of compatible ground instantiations of
    %% FStat and GStat (special treatment when F==G)
    findall(Fs-Gs,(all_statuses(FStat,Fs),
		   (F==G -> Fs=Gs; all_statuses(GStat,Gs)),
		   compatible(Fs,Gs)),FGs),
    restrict_status(Tau,F/FStat,TauF),			%remove F and G from Tau
    restrict_status(TauF,G/GStat,TauFG),
    %% For each of the pairs in FGs, try to build a proof with TauFG
    %% extended by the pair.  Extensions to the registry that
    %% occur in each of these proofs must be consistent in the
    %% following sense.  If we can prove for f=ms/g=ms and f=lex/g=lex
    %% then it is unsound to conclude for f=_.  We might later set
    %% g=lex and incorrectly instantiate f=ms, thinking that f=_ could
    %% be arbitrarily instantiated.  The simplest solution to this
    %% problem is to insist that TauFG and Prec are shared across the
    %% branches, so that g=ms and g=lex is excluded. 

    %% In case of Fs (and hence Gs) being lexicographically compared,
    %% there is a side condition to show that S > "each element in
    %% Ts".  We test this condition here rather than in compare_all
    %% (where it was done previously) since it prevents duplication of
    %% effort in the multiple cases (lr,rl combinations).
    (F==G ->
     ((rpos_prove_map_forall([F/Fs|TauFG]-Prec,Tau1-Prec1,Vars,S,Ts,Prfs)
	   -> (Flag=yeslex,
	       restrict_status(Tau1,F/_,Tau12),
	       restrict_status(Tau12,G/_,Tau2))	     
	   ;  (Prfs=nolex,Tau2-Prec1=TauFG-Prec)),
      Stat = ident,
      NewTau = [F/FStatNew|Tau3],
      conjunction_all_map(FGs,Solns,Flag,compare_all,F,G,Stat,Tau2-Prec1,Tau3-Prec2,
			  Vars,Ss,Ts));
     ((rpos_prove_map_forall([F/Fs,G/Gs|TauFG]-Prec,Tau1-Prec1,Vars,S,Ts,Prfs)
	   -> (Flag=yeslex,
	       restrict_status(Tau1,F/_,Tau12),
	       restrict_status(Tau12,G/_,Tau2))	     
	   ;  (Prfs=nolex,Tau2-Prec1=TauFG-Prec)),
      Stat = diff,
      NewTau = [F/FStatNew,G/GStatNew|Tau3],
      conjunction_all_map(FGs,Solns,Flag,compare_all,F,G,Stat,Tau2-Prec1,Tau3-Prec2,
			  Vars,Ss,Ts) )),
    NewPrec= Prec2,
    conjunction_choose(Solns,Stat,FStatNew,GStatNew,Proofs),
    (FStat==undef -> var(FStatNew); FStat=FStatNew),
    (GStat==undef -> var(GStatNew); GStat=GStatNew).

conjunction_cong(Tau-Prec,NewTau-NewPrec,F/FStat,G/GStat,Ss,Ts,Vars,Proofs) :- 
    /* Ss and Ts are congruent */
    %% FGs is list of pairs of compatible ground instantiations of
    %% FStat and GStat (special treatment when F==G)
    findall(Fs-Gs,(all_statuses(FStat,Fs),
		   (F==G -> Fs=Gs; all_statuses(GStat,Gs)),
		   compatible(Fs,Gs)),FGs),
    restrict_status(Tau,F/FStat,TauF),			%remove F and G from Tau
    restrict_status(TauF,G/GStat,TauFG),
    %% For each of the pairs in FGs, try to build a proof with TauFG
    %% extended by the pair.  Extensions to the registry that
    %% occur in each of these proofs must be consistent in the
    %% following sense.  If we can prove for f=ms/g=ms and f=lex/g=lex
    %% then it is unsound to conclude for f=_.  We might later set
    %% g=lex and incorrectly instantiate f=ms, thinking that f=_ could
    %% be arbitrarily instantiated.  The simplest solution to this
    %% problem is to insist that TauFG and Prec are shared across the
    %% branches, so that g=ms and g=lex is excluded. 
    (F==G ->
     (Stat = ident, NewTau = [F/FStatNew|Tau3],
      conjunction_all_map(FGs,Solns,Flag,congruent_all,F,G,Stat,TauFG-Prec,Tau3-Prec2,
			  Vars,Ss,Ts));
     (Stat = diff, NewTau = [F/FStatNew,G/GStatNew|Tau3],
      conjunction_all_map(FGs,Solns,Flag,congruent_all,F,G,Stat,TauFG-Prec,Tau3-Prec2,
			  Vars,Ss,Ts) )),
    NewPrec= Prec2,
    conjunction_choose(Solns,Stat,FStatNew,GStatNew,Proofs),
    (FStat==undef -> var(FStatNew); FStat=FStatNew),
    (GStat==undef -> var(GStatNew); GStat=GStatNew).


/* Map conjunction_all_ down a list, with a consistent registry */
conjunction_all_map([],[],_Flag,_Pred,_F,_G,_,TP,TP,_Vars,_Ss,_Ts).
conjunction_all_map([Fs-Gs|FGs],[Fs-Gs-Proof|Recs],Flag,Pred,F,G,ident,
		    TauFG-Prec,NTauFG-NP,Vars,Ss,Ts) :-
    if(Fs=lex(_),Flag==yeslex),
    conjunction_all_(Pred,[F/Fs|TauFG]-Prec, Tau1-Prec1,F/Fs,G/Gs, Ss,Ts,Vars,Proof),
    !,
    restrict_status(Tau1,F/_,Tau2),
    conjunction_all_map(FGs,Recs,Flag,Pred,F,G,ident,Tau2-Prec1,NTauFG-NP,Vars,Ss,Ts).
conjunction_all_map([Fs-Gs|FGs],[Fs-Gs-Proof|Recs],Flag,Pred,F,G,diff,
		    TauFG-Prec,NTauFG-NP,Vars,Ss,Ts) :-
    if(Fs=lex(_),Flag==yeslex),
    conjunction_all_(Pred,[F/Fs,G/Gs|TauFG]-Prec,Tau1-Prec1,F/Fs,G/Gs,Ss,Ts,Vars,Proof),
    !,
    restrict_status(Tau1,F/_,Tau12), restrict_status(Tau12,G/_,Tau2),
    conjunction_all_map(FGs,Recs,Flag,Pred,F,G,diff,Tau2-Prec1,NTauFG-NP,Vars,Ss,Ts).
conjunction_all_map([_|FGs],Recs,Flag,Pred,F,G,Stat,TP,NTP,Vars,Ss,Ts) :-
    conjunction_all_map(FGs,Recs,Flag,Pred,F,G,Stat,TP,NTP,Vars,Ss,Ts).

/* undef may be any proper status (but do not instantiate variables to
   undef  */
all_statuses(Undef,Status) :- 
    Undef == undef,!,
    is_status(Status).
all_statuses(Status,Status) :-
    is_status(Status).

/* TauG is a status function mapping G to Gs; Tau is as TauG but with
   this mapping removed.  */  
restrict_status(TauG,G/Gs,Tau) :- delete_one(TauG,G/Gs,Tau).


/* Solns is a list containing successful ground instantiations for
   FStat and GStat, together with a proof for that case.  If FStat and
   GStat are non-ground, then all valid groundings of them must be
   compatible. 
   
   The distinction between "ident" and "diff" is that for identical
   functions to be assigned variable (undef) status we require only a
   subset of all the possible combinations.  (This does not apply to
   pairs of functions which are only equivalent however.)  */
conjunction_choose(Solns,ident,_,_,[P,P2,P3]) :- %embarassing
    member(ms-ms-P,Solns),
    member(lex(lr)-lex(lr)-P2,Solns),
    member(lex(rl)-lex(rl)-P3,Solns),!.
conjunction_choose(Solns,diff,_,_,[P,P1,P2,P3,P4]) :- %embarassing
    member(ms-ms-P,Solns),
    member(lex(lr)-lex(rl)-P1,Solns),
    member(lex(lr)-lex(lr)-P2,Solns),
    member(lex(rl)-lex(rl)-P3,Solns),
    member(lex(rl)-lex(lr)-P4,Solns),!.
conjunction_choose(Solns,_,ms,ms,[P]) :-
    member(ms-ms-P,Solns).
conjunction_choose(Solns,diff,lex(_),lex(_),[P1,P2,P3,P4]) :-
    member(lex(lr)-lex(rl)-P1,Solns),
    member(lex(lr)-lex(lr)-P2,Solns),
    member(lex(rl)-lex(rl)-P3,Solns),
    member(lex(rl)-lex(lr)-P4,Solns),!.
conjunction_choose(Solns,ident,lex(_),lex(_),[P2,P3]) :-
    member(lex(lr)-lex(lr)-P2,Solns),
    member(lex(rl)-lex(rl)-P3,Solns),!.
conjunction_choose(Solns,diff,lex(lr),lex(_),[P1,P2]) :-
    member(lex(lr)-lex(rl)-P1,Solns),
    member(lex(lr)-lex(lr)-P2,Solns),!.
conjunction_choose(Solns,diff,lex(rl),lex(_),[P1,P2]) :-
    member(lex(rl)-lex(rl)-P1,Solns),
    member(lex(rl)-lex(lr)-P2,Solns),!.
conjunction_choose(Solns,diff,lex(_),lex(lr),[P1,P2]) :-
    member(lex(rl)-lex(lr)-P1,Solns),
    member(lex(lr)-lex(lr)-P2,Solns),!.
conjunction_choose(Solns,diff,lex(_),lex(rl),[P1,P2]) :-
    member(lex(rl)-lex(rl)-P1,Solns),
    member(lex(lr)-lex(rl)-P2,Solns),!.
conjunction_choose(Solns,_,lex(D1),lex(D2),[P1]) :-
    member(lex(D1)-lex(D2)-P1,Solns).

conjunction_all_(Pred,TP,NTP,_/Fs,_/Gs,Ss,Ts,Vars,Proof) :-
    status_eval(Fs,Ss,Fargs), status_eval(Gs,Ts,Gargs),
    Call =.. [Pred,TP,NTP,Fs,Fargs,Gargs,Vars,Proof],
    call(Call).  % One of the two clauses beloww...

compare_all(TP,NTP,Fs,Fargs,Gargs,Vars,Proof) :-
    (Fs = lex(_)
      -> rpos_prove(lex(Fargs,Gargs), TP, NTP, Vars,Proof)
      ;  rpos_prove(ms(Fargs, Gargs), TP, NTP, Vars,Proof)).
congruent_all(TP,NTP,Fs,Fargs,Gargs,Vars,congruent_all) :-
    (Fs = lex(_)
	 -> congruent_map(TP,NTP,Vars,Fargs,Gargs)
	 ;  mseteq(TP,NTP,Vars,congruent,Fargs,Gargs)).

/* Map down a list (with a consistent registry).  */
congruent_map(TP,TP,_Vars,[],[]).
congruent_map(TP,NTP2,Vars,[F|Flex],[G|Glex]) :-
    congruent(TP,NTP,Vars,F,G),
    congruent_map(NTP,NTP2,Vars,Flex,Glex).

rpos_prove_map_forall(TP,TP,_Vars,_,[],[]).
rpos_prove_map_forall(TP,NTP,Vars,S,[T|Ts],[P|Ps]) :-
    /* try to keep the registry unchanged */
    (rpos_prove(S>T,TP,NTP2,Vars,P) -> TP == NTP2;fail),!,
    rpos_prove_map_forall(NTP2,NTP,Vars,S,Ts,Ps).
rpos_prove_map_forall(TP,NTP,Vars,S,[T|Ts],[P|Ps]) :-
    rpos_prove(S>T,TP,NTP2,Vars,P),
    rpos_prove_map_forall(NTP2,NTP,Vars,S,Ts,Ps).

terminating(Reg,T,S) :-
    %% Show that T > S under registry R.  Extend R if necessary and
    %% possible.
    (registry(Reg,Tau,Prec,RegRef)
	 -> true				%a registry exists
	 ;  (Tau=[],Prec=[]-[])),
    extend_registry_prove(Tau-Prec,TauExt-PrecExt,T>S),
    ((Tau == TauExt, Prec==PrecExt)
      -> true
      ;  (plantraced(23,(clam_info('[Extended registry %t] ',[Reg]),nl)),
	  if(not(var(RegRef)),erase(RegRef)),
	  recorda(registry,registry(Reg,TauExt,PrecExt),_))),!.

/* Compute the reflexive transitive closure ?ST of +Graph.  Graph is a
   list of relation pairs having the form [A>=B,...]  where >= is
   reflexive and transitive.  From this we construct the reflexive
   transitive closure.  */
precedence_closure(S-_INEQ, ST) :-
    map_list(S,(A>=B):=>(A-B),true,SS),
    p_to_s_graph(SS,Sg),
    warshall(Sg,SC),				%trans closure
    s_to_p_graph(SC,ST).

/* Transitive clousre stuff due to O' Keefe */
%   s_vertices(+S_Graph,  ?Vertices)
%   strips off the neighbours lists of an S-representation to produce
%   a list of the vertices of the graph.  (It is a characteristic of
%   S-representations that *every* vertex appears, even if it has no
%   neighbours.)
s_vertices([], []).
s_vertices([Vertex-_Neighbours|Graph], [Vertex|Vertices]) :-
	s_vertices(Graph, Vertices).
%   p_vertices(+P_Graph, ?Vertices)
%   unifies Vertices with the set of non-isolated vertices of P_Graph
%   represented as a list in standard order.  It is a characteristic
%   of P-representation that a vertex only appears if it is attached
%   to some edge.

p_vertices(P_Graph, Vertices) :-
	p_vertices_1(P_Graph, Bag),
	sort(Bag, Vertices).

p_vertices_1([], []).
p_vertices_1([From-To|Edges], [From,To|Vertices]) :-
	p_vertices_1(Edges, Vertices).
%   p_to_s_graph(+P_Graph, ?S_Graph)
%   converts a graph from P-representation to S-representation.
%   If the graph has N nodes and E edges, the cost is O(ElgE).

p_to_s_graph(P_Graph, S_Graph) :-
	sort(P_Graph, EdgeSet),
	p_vertices(EdgeSet, VertexSet),
	p_to_s_group(VertexSet, EdgeSet, S_Graph).


p_to_s_group([], _, []).
p_to_s_group([Vertex|Vertices], EdgeSet, G0) :-
	p_to_s_group(EdgeSet, Vertex, G0, G1, RestEdges),
	p_to_s_group(Vertices, RestEdges, G1).

p_to_s_group([V-X|Edges], V, [V-[X|Neibs]|G], G, RestEdges) :- !,
	p_to_s_group(Edges, V, Neibs, RestEdges).
p_to_s_group(Edges, V, [V-[]|G], G, Edges).

p_to_s_group([V-X|Edges], V, [X|Neibs], RestEdges) :- !,
	p_to_s_group(Edges, V, Neibs, RestEdges).
p_to_s_group(Edges, _, [], Edges).



%   s_to_p_graph(+S_Graph, ?P_Graph)
%   converts a graph from S-representation to P-representation.
%   A unique choice is made: edges appear in standard order.
%   If the graph has N nodes and E edges, the cost is O(E).

s_to_p_graph([], []).
s_to_p_graph([Vertex-Neibs|G], P_Graph) :-
	s_to_p_graph(Neibs, Vertex, P_Graph, Rest_P_Graph),
	s_to_p_graph(G, Rest_P_Graph).


s_to_p_graph([], _, P_Graph, P_Graph).
s_to_p_graph([Neib|Neibs], Vertex, [Vertex-Neib|P], Rest_P) :-
	s_to_p_graph(Neibs, Vertex, P, Rest_P).



%   s_to_p_trans(+S_Graph, ?P_Graph)
%   converts the TRANSPOSE of a graph in S-representation to
%   P-representation, without actually building the transpose.
%   If the graph hasN nodes and E edges, the cost is O(E).
%   A unique representation is returned, but it has no useful
%   properties other than having no duplicates (it is not ordered).

s_to_p_trans([], []).
s_to_p_trans([Vertex-Neibs|G], P_Graph) :-
	s_to_p_trans(Neibs, Vertex, P_Graph, Rest_P_Graph),
	s_to_p_trans(G, Rest_P_Graph).

s_to_p_trans([], _, P_Graph, P_Graph).
s_to_p_trans([Neib|Neibs], Vertex, [Neib-Vertex|P], Rest_P) :-
	s_to_p_trans(Neibs, Vertex, P, Rest_P).

%   warshall(+Graph, ?Closure) computes Closure from graph in
%   O(N**3) time.  To obtain the transitive closure of a
%   graph in P-representation, convert it to S-representation.
%   The closure will be the dominant cost.  Note that there
%   can be a lot of graphs with a given closure, so it wouldn't
%   make much sense to call this with a variable as first
%   argument.

warshall(Graph, Closure) :-
	warshall(Graph, Graph, Closure).
warshall([], Closure, Closure).
warshall([V-_|G], E, Closure) :-
	memberchk(V-Y, E),	%  Y := E(v)
	warshall(E, V, Y, NewE),
	warshall(G, NewE, Closure).
warshall([], _, _, []).
warshall([X-Neibs|G], V, Y, [X-NewNeibs|NewG]) :-
	memberchk(V, Neibs),
	!,
	ord_union(Neibs, Y, NewNeibs),
	warshall(G, V, Y, NewG).
warshall([X-Neibs|G], V, Y, [X-Neibs|NewG]) :-
	warshall(G, V, Y, NewG).


%%% Local Variables:
%%% mode:prolog
%%% End:






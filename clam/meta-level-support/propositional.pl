/*
 * @(#)$Id: propositional.pl,v 1.17 2005/05/09 18:28:25 smaill Exp $
 *
 * $Log: propositional.pl,v $
 * Revision 1.17  2005/05/09 18:28:25  smaill
 * build in commuted equality hyps
 *
 * Revision 1.16  2005/05/06 19:25:23  smaill
 * take out check_time_limit (dealt with by sictus timing module);
 * use meta-vars instead of trying to get fresh object vars
 *
 * Revision 1.15  1999/02/02 09:42:11  img
 * Added wfftacs to \ intro rules
 *
 * Revision 1.14  1999/01/07 16:32:19  img
 * *** empty log message ***
 *
 * Revision 1.13  1998/09/17 08:34:01  img
 * unfold_iff/0: (added)
 *
 * Revision 1.12  1998/09/16 13:49:05  img
 * is_propositional/1 (added);  extended propositional/2 with new axiom
 * clauses to cover some non-propositional stuff, much as elementary/2
 * does.  The intention is to prefer propositional/2 over elementary/2
 * since it should (now) have the same coverage (excepting
 * well-formedness goals) but be much faster.
 *
 * Revision 1.11  1998/08/26 12:13:44  img
 * totally reimplemented to avoid unnecessary proof-search in ipc_4 case:
 * this rule is semi-invertible!
 *
 * Revision 1.10  1998/06/10 08:21:13  img
 * introduce d.f.t first (unifying with elementary).  See mthd(elementary).
 *
 * Revision 1.9  1998/05/13 12:54:44  img
 * fix
 *
 * Revision 1.8  1998/04/27 13:39:59  img
 * Added {true} proposition
 *
 * Revision 1.7  1997/09/26 14:37:22  img
 * typo
 *
 * Revision 1.6  1997/06/05 10:32:59  img
 * New decider for IPC
 *
 * Revision 1.5  1997/01/14 10:44:21  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.4  1995/07/18 14:16:03  img
 * hyp(V) instead of intro since the derived rule sometimes gets it wrong
 *
 * Revision 1.3  1995/05/17  02:17:49  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:28  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: propositional.pl,v 1.17 2005/05/09 18:28:25 smaill Exp $').

/* This file contains a decision procedure for the propositional part
 * of the Nuprl logic.  See Dyckhoff's JSL article for information
 * (1992).  */

is_propositional(P) :-
    propositional(P,_).

/* propositional(+Sequent,?Tactic) succeeds iff Sequent is provable in
   the intuistionistic predicate calculus; Tactic is the Oyster
   tactic.  <=> is translated as normal, {true} is assumed to simplify
   to a type containing '0'.  */

propositional(H==>V:T=>P,(intro(new[Y]) then wfftacs) then Tac) :-
%   (free([V],H) -> Y=V; hfree([Y],H)), !,  % keep Y as a meta-variable
    append(H,[Y:T],HNew),

    propositional(HNew==>P,Tac).

propositional(H==>G,P) :-ipc_tautology(H==>G,P).

ipc_tautology(H==>G, unfold_iff then Prf) :-
    !,
    no_biimplications(G,GG),
    !,ipc_derivable(Prf,H==>GG),!.
ipc_tautology(G,unfold_def_all(_ <=> _) then Prf) :-
    no_biimplications(G,GG),
    ipc_derivable(Prf,[]==>GG),!.

/* Build a derivation for Seq */
atomic_prop(_ # _) :- !,fail.
atomic_prop( _  \ _ ) :- !,fail.
atomic_prop( _ => _ ) :- !,fail.
atomic_prop(_ <=> _ ) :- !,fail.
atomic_prop( void ) :- !,fail.
atomic_prop( _ ).

ax_ipc_rule(intro(explicit(0)) then simplify then wfftacs, _==>{true}) :- !.
ax_ipc_rule(hyp(V), H==>G) :- member(V:G,H), !.
ax_ipc_rule(hyp(V), H==>(A = B in T)) :- member(V:(B = A in T), H), !.
ax_ipc_rule(elim(V), H==>_) :- member(V:void,H).

/* additions for some recursive types */
ax_ipc_rule(identity, _==>X=X in _).
ax_ipc_rule(identity_equiv, _==>X<=>X).
ax_ipc_rule(contradiction(V), H==>_) :-
    member(V:C1=C2 in T,H),
    \+ C1 == C2,
    constant(C1,T),
    constant(C2,T).
ax_ipc_rule(clam_arith(N:L=R in pnat), H==>_) :-    
    member(N:L=R in pnat,H),
    ground(L-R),
    memberchk(L-R,[s(_)-0,0-s(_),s(X)-X,X-s(X)]).
ax_ipc_rule(clam_arith(N:L=R in T list), H==>_) :-    
    member(N:L=R in T list,H),
    ground(L-R),
    memberchk(L-R,[(_::_)-nil,nil-(_::_)]).

%ipc_derivable(_,_) :-
%    check_time_limit,
%    fail.
ipc_derivable(Rule,Seq) :-
    ax_ipc_rule(Rule,Seq),!.
ipc_derivable((intro(new [V])then wfftacs)then Tac, H==>(A=>B)) :-
    !,
    ipc_derivable(Tac,[V:A|H]==>B).

ipc_derivable(intro then [TacA,TacB], H==>A#B) :-
    !,
    ipc_derivable(TacA, H==>A),!,
    ipc_derivable(TacB,H==>B).

ipc_derivable(elim(V,new [VA,VB,_]) then Tac, H==>G) :-
    select(V:(A#B),H,HH),!,
    ipc_derivable(Tac,[VA:A,VB:B|HH]==>G).

ipc_derivable(elim(V,new [VA,VB,_,_]) then [TacA,TacB], H==>G) :- 
    select(V:(A\B),H,HH),!,
    ipc_derivable(TacA, [VA:A|HH]==>G),!,
    ipc_derivable(TacB, [VB:B|HH]==>G).

ipc_derivable(intro(left) then [Tac,wfftacs], H==>A\_) :-
    ipc_derivable(Tac, H==>A).
ipc_derivable(intro(right) then [Tac,wfftacs], H==>_\B) :-
    ipc_derivable(Tac,H==>B).

ipc_derivable((elim(V,new [VB]) then
                 [intro(explicit(0)) then simplify then wfftacs,
		  idtac])then Tac,H==>G) :-
    select(V:{true}=>B, H,HH),!,
    ipc_derivable(Tac,[VB:B|HH]==>G).

ipc_derivable((elim(V,new [VB]) then [hyp(VA), idtac])then Tac,H==>G) :-
    select(V:A=>B,H,HH),
    member(VA:AA,HH),
    (A=AA; (A = (X = Y in T), AA = (Y = X in T))),
    atomic_prop(A),!,
    ipc_derivable(Tac, [VB:B|HH]==>G).


ipc_derivable((lemma(ipc_dp_imp_e2,new[L])
			then [elim_on_thin(L,[C,D,B,G]) 
				  then elim(L,new [L2]) then
				  [intro(new [VCBD]) then [idtac,wfftacs],
				   elim(L2,new[L3])
			then
				       [hyp(V),hyp(L3)]]])then Tac,H==>G) :-
    select(V:(C # D)=>B,H,HH),!,
    ipc_derivable(Tac, [VCBD:(C=>(D=>B))|HH]==>G).

ipc_derivable((lemma(ipc_dp_imp_e3,new[L1])then
		  elim_on_thin(L1,[C,D,B,G])then elim(L1,new[L3])then
		  [(intro(new[L3])then wfftacs)then elim(L3,new[VC,VD,_])then idtac,
		   elim(L3,new[L4])then[hyp(V),hyp(L4)]])then Tac,H==>G) :-
    select(V:(C\D)=>B, H, HH),!,
    ipc_derivable(Tac, [VC:C=>B,VD:D=>B|HH]==>G).

ipc_derivable((lemma(ipc_dp_imp_e4,new[L1])
		  then elim_on_thin(L1,[G,B,C,D])
		  then elim(L1,new[L2])then
		  [intro then
		       [(intro(new[L2])then[idtac,wfftacs]),
			(intro(new[L2])then[idtac,wfftacs])],
		   elim(L2,new[L3])then[hyp(V),hyp(L3)] ])then [Tac1,Tac2],H==>G) :-
    select(V:(C=>D)=>B, H, HH),
    ipc_derivable(Tac2,[L2:D=>B|HH]==>(C=>D)),!,
    ipc_derivable(Tac1,[L2:B|HH]==>G).

/* no_biimplications(+U,?V) U and V are equivalent propositions but V
   does not contain <=>.  (Identical but for occurrences of (A<=>B) in
   U being replaced with (A=>B)#(B=>A) in V.  */
no_biimplications(A<=>B,(AA=>BB)#(BB=>AA)) :-
	no_biimplications(A,AA),
	no_biimplications(B,BB).
no_biimplications([],[]).
no_biimplications([A|As],[AA|AAs]) :-
	no_biimplications(A,AA),
	no_biimplications(As,AAs).
no_biimplications(A,A) :-atomic_prop(A),!.
no_biimplications(A,AA) :- A =.. [P|As],
	no_biimplications(As,AAs),
	AA =.. [P|AAs].


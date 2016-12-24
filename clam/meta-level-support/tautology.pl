/*
 * @(#)$Id: tautology.pl,v 1.4 1997/01/14 10:44:33 img Exp $
 *
 * $Log: tautology.pl,v $
 * Revision 1.4  1997/01/14 10:44:33  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:18:01  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:47  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: tautology.pl,v 1.4 1997/01/14 10:44:33 img Exp $').

/*
 * This file contains tactics for simple reasoning in type theory.
 *
 * The crucial predicates are tautology/2 for the calculation of a
 * tactic that will proof a goal, and tautology/1 for the execution of it.
 */

	% tautology(+Sequent,?Tactic) will compute Tactic that will prove
	% Sequent, provided Sequent is a propositional tautology.
	% 
	% We have two clauses for tautology/2, one to stick in the
	% hyp-list if not already provided, and one if hyp-list is
	% already provided. In both cases tautology/2 calls tautology/3
	% to find tactic for sequent H==>G given a list of hyps
	% previously elim'd.
        % Note form with goal given as list, for compatability
        % with Clam.
tautology(_==>[],_).
tautology(H==>{A|B},_) :- tautology(H==>A,_),tautology(H==>B,_).
tautology(H==>[G],T) :- tautology(H==>G,T).
tautology([]==>G,Tactic) :- hyp_list(H),tautology([],H==>G,Tactic).
tautology([H|Hs]==>G,Tactic) :- nonind_hyps([H|Hs],HH),
             tautology([],HH==>G,Tactic).

	% tautology/3 looks for simplified rule that is applicable,
	% checks that it has not been used before, adds it to list of
	% hyps elim'd, finds recursively tactics for each of the
	% subgoals, and combines tactics to form overall tactic.
tautology(L,H==>G,Tactic) :- 
    prule(Rule,H==>G,Sublist),
    \+ repeat(L,H==>G),
    add_seq(L,H==>G,LL),
    tautologylist(LL,H,Sublist,Tacticlist),
    newtautology(Tactic,Rule,Tacticlist).

add_seq(L,H==>G,[H==>G|L]).

	% tautologylist/4 finds tactics for each of list of sequents, in
	% presence of hypothesis list H (these lists are stored
	% incrementally in rules, so we have to use update/3 to find
	% full hyp list for subgoals). 
tautologylist(_,_,[],[]):- !.
tautologylist(L,H,[Subseq],[Subtactic]) :- !,
    update(H,Subseq,Subgoal),
    tautology(L,Subgoal,Subtactic),!.
tautologylist(L,H,[H1|T1],[H2|T2]) :- 
    tautologylist(L,H,[H1],[H2]),
    tautologylist(L,H,T1,T2).

newtautology(Rule,Rule,[]) :- !.
newtautology(intro(left) then [Subtact,wfftacs],intro(left),[Subtact]):-
    !.
newtautology(intro(right)then [Subtact,wfftacs],intro(right),[Subtact]):-
    !.
newtautology(intro then [Subtact,wfftacs],intro(a),[Subtact]) :- !.
newtautology(Rule then Subtact,Rule,[Subtact]) :- !.
newtautology(Rule then Tacticlist,Rule,Tacticlist).

update(H,(HH==>GG),(K==>GG)) :- !,
    append(H,HH,K).
update(H,(==> GG),(H==>GG)).

repeat(L,H==>G) :- member(HH==>G,L),
                   setof(X,Y^member(Y:X,HH),S1),
                   setof(XX,Y^member(Y:XX,H),S2),
                   seteq(S1,S2).

	%  prule/3 is simplified version of NurPRL rule/3 with arguments
	%  (Rule,Sequent,Subgoal).  Special rule (wfftacs) for wf-goals.
prule(hyp(X), H==>G ,[]):- member(X:G,H).
	% int is used as "true" in definitions (e.g. even, leq, etc):
prule(istrue,_==>{true},[]) .            
prule(elim(X),H==>_ ,[]):- member(X:void,H).
prule(intro(a),H==>A=>B,[[Y:A]==>B ]):- free([Y],H).
prule(elim(F),H==>T,[==>A,[Y:B]==>T ]):- member(F:A=>B,H),free([Y],H).
prule(intro,_==>A#B,[==>A,==>B]). 
prule(elim(Z),H==>T,[[U:A,V:B,W:dummy]==>T]):-
    member(Z:A#B,H),free([U,V,W],H).
prule(wfftacs,_==>G in u(_),[]) :- \+ functor(G,=,2).
prule(elim(V),H==>T ,
    [ [X:A ,N1:dummy]==>T,
      [Y:B ,N2:dummy]==>T ]):- member(V:A\B,H),free([X,Y,N1,N2],H).
prule(intro(left),_==>A\_ , [==>A]).
prule(intro(right),_==>_\B ,[==>B]).

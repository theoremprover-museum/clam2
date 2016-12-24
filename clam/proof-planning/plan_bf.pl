/*
 * @(#)$Id: plan_bf.pl,v 1.7 1997/01/14 10:45:26 img Exp $
 *
 * $Log: plan_bf.pl,v $
 * Revision 1.7  1997/01/14 10:45:26  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.6  1996/12/04 12:59:02  img
 * Added conjecture and time taken slot to proof_plan object.
 *
 * Revision 1.5  1995/10/03  13:13:08  img
 * added "plan" record for library mechanism to access
 *
 * Revision 1.4  1995/05/17  02:19:04  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.3  1995/03/01  04:15:31  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.2  1995/02/08  17:28:40  img
 * 	* added resetAppInd
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_bf.pl,v 1.7 1997/01/14 10:45:26 img Exp $').

/*
 * This file contains code for a breadth-first proof planner.
 */

	% bplan(+Input,?Plan,?Effects) see comments on dplan/4 in
	% plan-df.pl for explanation of modes and usage.
	%
	% This planner generates plans breadth-first: First generate all
	% plans of length n before generating any plan of length n+1.
	% The main idea is to swap the order of the two conjuncts  of
	% the last clause of dplan (ie. the generate step and the plan step).
	% This changes the order of the backtrack points, so that we
	% will now first backtrack through all possible additions to a plan
	% before generating a longer plan. This gives us breadth first.
	%
	% However, the complication is that we then want to add the new
	% node at the bottom of the plan, instead of at the bottom of
	% the new single step. We somehow have to keep track of where to
	% add the new step to the previously generated plan. That's why
	% we give some more structure to the Output slot: this is now no
	% longer just a list of open subgoals, but a list of sublists of open
	% subgoals, one sublist for each node at the fringe of the tree.
	% For each node in the fringe we maintain a variable pointing to
	% it, (generated in the first clause of bplan/4), so that we can
	% add the new node in that place (using attach_to_tree) without
	% traversing the whole tree from the top. The dangling variables
	% are mopped up at the end of the planning process
	%
	% The extra structure in the list of open subgoals means we have
	% to do a double iteratation to get to the open goals themselves
	% (using it_it_applicable).
	%
	% We explicitly delete [] nodes from the set of open goals (and
	% also delete the corresponding pointers from the list of
	% pointers), to avoid the double production of succeeding branches.
	%
	% First clauses of bplan are for human consumption only: insert
	% arguments for Effects, Input and the list of variable-pointers,
	% and finish by deleting dangling variables and by flattening
	% the list of lists of effects into a single list of Effects.
	% (Actually, the richer representation of the Effects as lists
	% of lists might be more desirable in the end, in which case the
	% append/2 call should go.
bplan :-
    bplan(Plan),
    print_plan(Plan),
    bplan:=Plan.

bplan(Plan) :- bplan(Plan,[]).
bplan(Plan,Effects) :-
    goal(Input), hyp_list(H),
    resetAppInd,
    bplan(H==>Input,Plan,Effects),
    cthm =: T,
    uniq_recorda(proof_plan,proof_plan(H==>Input,T,_,Plan,bfplan),_).

bplan(Input,Plan,Effects) :-
    	(Effects==[] -> Es=[] ; true),
    bplan(Input,Plan1,Es,_),
    append(Es,Effects),
    remove_open_nodes(Plan1,Plan).

% dynamic declaration for collecting stats:
% :- dynamic bplan/4.
bplan(Input, Plan then Var, [], [Var]) :-
    applicable(Input, Plan, _,[]).
bplan(Input, Plan then Var, [[Effect|Effects]], [Var]) :-
    applicable(Input, Plan, _,[Effect|Effects]).
bplan(Input, Plan, Effects, Vars) :-
    bplan(Input, Plan, E1,V1s),
    delete(E1,V1s,[],E2,Vs), E2=[_|_],
    	(Effects==[] -> E3=[] ; true),
    it_it_applicable(E2,Ms,_,E3),
	(Effects==[] -> true ;
    append(E3,Effects)
    	),
    it_attach_to_tree(Ms,Vs,Vars).


	% All it_it_applicable does is iterate applicable over a list of
	% lists of open goals, by iterating it_applicable for doing the
	% single iteration over the sublists.
it_it_applicable([],[],[],[]).
	it_it_applicable([I|Is],[M|Ms],[P|Ps],E) :-
	    E==[],!,
	    it_applicable(I,M,P,[]),
	    it_it_applicable(Is,Ms,Ps,[]).
it_it_applicable([I|Is],[M|Ms],[P|Ps],[E|Es]) :-
    it_applicable(I,M,P,E),
    it_it_applicable(Is,Ms,Ps,Es).

it_applicable([],[],[],[]).
	it_applicable([I|Is],[M|Ms],[P|Ps],E) :-
	    E==[],!,
	    applicable(I,M,P,[]),
	    it_applicable(Is,Ms,Ps,[]).
it_applicable([I|Is],[M|Ms],[P|Ps],[E|Es]) :-
    applicable(I,M,P,E),
    it_applicable(Is,Ms,Ps,Es).

	% attach_to_tree(+Methods,+Vars,-NewVars)
	% attach_to_tree iterates over two lists: a list of methods (the
	% first argument) and a list of variables (the second argument),
	% and does two things for each method/variable:
	%  1) The method is unified with the variable (thereby attaching
	%     it to the plan-tree in which the variable appeared
	%     somewhere at the fringe
	%  2) A new variable is inserted below the method. This variable
	%     will serve as a pointer for the next recursive call of
	%     bplan. A list of these new variables is returned as the
	%     third argument. Thus, the ouput list of attach_to_tree
	%     (the third argument), will in a next recursion of bplan
	%     re-appear as an input list (the second argument).
	%
	% These two actions could have been done by two separate
	% predicats, but it would mean iterating over the list of
	% methods twice, while we get away with one iteration this way.
attach_to_tree([],[],[]).
attach_to_tree([H|T1],[H then Var|Vs], [Var|Vars]) :-
    attach_to_tree(T1,Vs,Vars).

	% it_attach_to_tree iterates attach_to_tree over a list of lists
	% of methods, flattening the resulting lists of lists of
	% variables into a single list.
it_attach_to_tree([],[],[]).
it_attach_to_tree([H1|T1],[H2|T2],Vars) :- !,
    attach_to_tree(H1,H2,HVars),
    it_attach_to_tree(T1,T2,TVars),
    append(HVars,TVars,Vars).

	% remove_open_nodes(+Plan,?Plan) recursively descends into a
	% plan-tree, and removes all open nodes of the form "... then Var"
	% that live at the fringe of the tree.
remove_open_nodes(M then V, M) :- var(V),!.
remove_open_nodes(M1 then M2, M1 then M3) :- remove_open_nodes(M2,M3).
remove_open_nodes([],[]).
remove_open_nodes([H|T],[HH|TT]) :-
    remove_open_nodes(H,HH),
    remove_open_nodes(T,TT).

	% delete(L1,L2,Elem,NewL1,NewL2)
	% L1 and L2 are lists of equal length.
	% Every element of L1 unifying with Elem is deleted, giving NewL1.
	% Every corresponding element of L2 is also deleted, giving NewL2
delete([],[],_,[],[]).
delete([Kill|T1],[_|T2],Kill,NewT1,NewT2) :- !,
    delete(T1,T2,Kill,NewT1,NewT2).
delete([H1|T1],[H2|T2],Kill,[H1|NewT1],[H2|NewT2]) :-
    delete(T1,T2,Kill,NewT1,NewT2).


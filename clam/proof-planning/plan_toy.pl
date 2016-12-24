/*
 * @(#)$Id: plan_toy.pl,v 1.4 1997/01/14 10:45:37 img Exp $
 *
 * $Log: plan_toy.pl,v $
 * Revision 1.4  1997/01/14 10:45:37  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:15  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:56  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_toy.pl,v 1.4 1997/01/14 10:45:37 img Exp $').

/*
 * This file contains two versions of a toy planner, one depth first,
 * the other breadth first. Both planners use the generate_node/3
 * predicate to generate nodes in the plan-tree.
 */

/*
 * GOVERMENT HEALTH WARNING: Loading this file can seriously damage your heath!
 * In order to make this file self-contained, some predicates from other
 * files are redefined in this file. When loading this file into CLaM
 * you will therefore override other definitions and probable change
 * them slightly, causing CLaM to stop working!
 *

	% generate_node(Input, Node, Output).
	% To be changed freely for different toy applications.
/*
	% Useful for iterative deepening planners. See comments at idwtplan.
generate_node(1,	1,	[11,12]).
 generate_node(11,	11,	[111]).
 generate_node(11,	11,	[112]).
  generate_node(112,	112,	[]).
  generate_node(111,	111,	[1111]).
   generate_node(1111,	1111,	[]).
 generate_node(12,	12,	[121]).
  generate_node(121,	121,	[1211]).
   generate_node(1211,	1211,	[]).
*/
	% Version of the above with one infinitely deep branch.
generate_node(0,	0,	[9999]).
generate_node(0,	0,	[1]).
generate_node(1,	1,	[11,12]).
 generate_node(11,	11,	[111.1]).
 generate_node(11,	11,	[111.2]).
 generate_node(11,	11,	[112]).
  generate_node(111.1,	111.1,	[1111]).
  generate_node(112,	112,	[]).
  generate_node(111.2,	111.2,	[9999]).
   generate_node(1111,	1111,	[]).
   generate_node(X,	X,	[Y]) :-
       X>=9999, Y is X+1, write('visited '),write(X),nl.
 generate_node(12,	12,	[121]).
  generate_node(121,	121,	[1211]).
   generate_node(1211,	1211,	[]).
/*
generate_node(N, a(N), []).
generate_node(N, z(N), [M,M]) :- M is N*10.
*/
/*
generate_node(N, a(N), [M,M]) :- M is N*2.
generate_node(N, b(N), [M,M]) :- M is N*10.
generate_node(N, c(N), [M,M]) :- M is -N.
*/

	% Depth first planner: A plan is one node followed by sequence
	% of plans, on for every subnode of the first node.
	% It's depth first because we first backtrack through all possible
	% trees P2 underneath P1 before redoing our choice for P1.
	%
	% First clause for human consumption only, to initialise
	% top-node to 1. 
dtplan : dtplan(Plan), print_plan(Plan).
dtplan(Plan) :- dtplan(Plan,[]).
dtplan(Plan, Output) :- dtplan(1, Plan, Output).
dtplan(Input, Plan, []) :- generate_node(Input, Plan, []).
dtplan(Input, P1 then P2, Output) :-
    generate_node(Input, P1, [O|Os]),
    iterate_dtplan([O|Os], P2, Output).

iterate_dtplan([],[],[]).
iterate_dtplan([I|Is], [P|Ps], Os) :-
    dtplan(I,P,O1),
    iterate_dtplan(Is,Ps,O1s),
    append(O1,O1s,Os).

	% Breadth first planner.
	% The main idea is to swap the order of the two conjunts from
	% the last clause of dtplan (ie the generate step  and the plan step).
	% This changes the order of the backtrack points, so that we will
	% now first backtrack through all possible additions to a plan
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
	% it, (generated in the first clause of btplan/4), so that we can
	% add the new node in that place (using attach_to_tree) without
	% traversing the whole tree from the top (is this close to a
	% "difference structure"?)
	% The dangling variables should be moppped up at the end if this
	% planner were used in real life.
	%
	% The extra structure in the list of open subgoals means we have
	% to do a double iteratation to get to the open goals themselves
	% (using it_it_gen_node).
	%
	% We explicitly delete [] nodes from the set of open goals (and
	% also delete the corresponding pointers from the list of
	% variable pointers), to avoid the double production of succeeding
	% branches by both clauses of btplan/3.
btplan :- btplan(Plan), print_plan(Plan).
btplan(Plan) :- btplan(Plan,[]).
btplan(Plan, Output) :- btplan(1, Plan, Output,_).
btplan(Input, Plan then Var, [Output], [Var]) :-
    generate_node(Input, Plan, Output).
btplan(Input, Plan, Output,Vars) :-
    write('btplan called'),nl,
    btplan(Input, Plan, O1,V1s),
    delete(O1,V1s,[],O,Vs), O=[_|_],
    it_it_gen_node(O,Ps,Os),
    attach_to_tree_d(Ps,Vs,Vars),
    append(Os,Output).

attach_to_tree_d([],[],[]).
attach_to_tree_d([H1|T1],[H2|T2],Vars) :- !,
    attach_to_tree(H1,H2,HVars),
    attach_to_tree_d(T1,T2,TVars),
    append(HVars,TVars,Vars).
attach_to_tree([],[],[]).
attach_to_tree([H|T1],[H then Var|Vs], [Var|Vars]) :-
    attach_to_tree(T1,Vs,Vars).

	% Below is a version of attach_to_tree[_d] which uses difference
	% lists to collect the new variables (ie the third argument).
	% This enables us to use dl_append/3 rather than append/3 to
	% collect the sublists of variables into a single list. When
	% using this version, the call to attach_to_tree_d/3 in btplan/4
	% should have Vars-[] as its last argument, instead of just Vars.
	% This SHOULD be faster, but .... for reasons completely unclear to
	% me, it is actually 10% slower. Anybody volunteers an explanation?
/*
 * attach_to_tree_d([],[],T-T).
 * attach_to_tree_d([H1|T1],[H2|T2],Vars) :- !,
 *     attach_to_tree(H1,H2,HVars-TailHVars),
 *     attach_to_tree_d(T1,T2,TVars-TailTVars),
 *     dl_append(HVars-TailHVars,TVars-TailTVars,Vars).
 * attach_to_tree([],[],T-T).
 * attach_to_tree([H|T1],[H then Var|Vs], [Var|Vars]-TailVars) :-
 *     attach_to_tree(T1,Vs,Vars-TailVars).
 * dl_append(Xs-Ys,Ys-Zs,Xs-Zs).
 */

it_it_gen_node([],[],[]).
it_it_gen_node([I|Is],[P|Ps],[O|Os]) :-
    it_gen_node(I,P,O),
    it_it_gen_node(Is,Ps,Os).

it_gen_node([],[],[]).
it_gen_node([I|Is],[P|Ps],[O|Os]) :-
    generate_node(I,P,O),
    it_gen_node(Is,Ps,Os).

append([],[]).
append([H],H).
append([H1,H2|T],N) :-
    append(H1,H2,H),
    append([H|T],N).

	% delete(L1,L2,Elem,NewL1,NewL2)
	% L1 and L2 are lists of equal length.
	% Every element of L1 unifying with Elem is deleted, giving NewL1.
	% Every corresponding element of L2 is also deleted, giving NewL2
delete([],[],_,[],[]).
delete([Kill|T1],[_|T2],Kill,NewT1,NewT2) :- !,
    delete(T1,T2,Kill,NewT1,NewT2).
delete([H1|T1],[H2|T2],Kill,[H1|NewT1],[H2|NewT2]) :-
    delete(T1,T2,Kill,NewT1,NewT2).


	% Below is a version of the depth-first planner which does
	% iterative deepening.
	%
	% idtplan(+Depth,+Bound,+Input,?Plan,?Output,?MaxDepth) is just as
	% dtplan(Input,Plan,Output), except that Depth represents the
	% current length of (this branch of) the plan, and Bound
	% represents the current maximum on the depth of the plan.
	% MaxDepth is the length of the longest branch in the proof (and
	% will not exceed Bound). 
	% The top-level predicate idtplan/2 calls idtplan/5 with
	% increasingly large Bound.
	%
	% Interesting variation of first clause would be to identify
	% MaxDepth and Bound. This would generate only plans of depth
	% Bound. Apart from maybe being useful in its own right, it also
	% suppresses returning solutions already found under shorter
	% Bounds (However, it only suppresses *returning* them, not
	% *generating* them which is what we want).
	%
	% Notes:
	% - would be nice if we wouldn;t have to redo all work up
	%   to level n when increasing bound to n+1
	% - would be nice if we could avoid solutions being generated
	%   twice (this maybe comes for free if we do the previous point)
	% - would be nice if we could increase bounds by steps of d,
	%   rather than fixed d=1
	% - would be nice if we could spot plan failure before max depth
	%   is reached, to prevent endless looping. This would be
	%   possible by introducing a clause 
	%   for idtplan that succeeds when D>B, and sets a global flag.
	%   The first clause of idtplan should then check that this flag
	%   has indeed been set before increasing the Bound. If the flag
	%   is not set, there is no point in increasing the Bound, and
	%   we should fail alltogether.
	% - would be nice if we could impose an overall limit on the
	%   size of Bound, to stop everything when things get too
	%   ridiculous. Would be possible by introducing MaxBound as an
	%   argument to idtplan/4, and to check that Bound=<MaxBound
	%   before calling idtplan/6
idtplan :- idtplan(Plan), print_plan(Plan).
idtplan(Plan) :- idtplan(Plan,[],_).
idtplan(Plan, Output, MaxDepth) :-
    genint(Bound),
    writef('Set max depth to %t\n',[Bound]),
    idtplan(1, Bound, 1, Plan, Output, MaxDepth),
    (MaxDepth=Bound
     -> true
     ;  (writef('previously reported soln suppressed\n'),fail)
    ).

idtplan(D,B,_,_,_,_) :-
    D>B, writef('trying to overstep depth %t\n',[B]),!,fail.
idtplan(D,B,Input, Plan, [], D) :-
    D=<B,
    generate_node(Input, Plan, []),
    writef('visited %t\n',[Input]),
    writef('	Branch terminated at depth %t (max depth is %t)\n',[D,B]).
idtplan(Depth,Bound,Input, P1 then P2, Output, MaxDepth) :-
    Depth < Bound, Depth1 is Depth+1,
    generate_node(Input, P1, [O|Os]),
    writef('visited %t\n',[Input]),
    iterate_idtplan(Depth1,Bound,[O|Os], P2, Output, MaxDepths),
    max(MaxDepths,MaxDepth).

iterate_idtplan(_,_,[],[],[],[]).
iterate_idtplan(D,B,[I|Is], [P|Ps], Os,[D1|Ds]) :-
    idtplan(D,B,I,P,O1,D1),
    iterate_idtplan(D,B,Is,Ps,O1s,Ds),
    append(O1,O1s,Os).

	% Alternative version of the iterative deepener, which uses a
	% different metric to cut of search. The above (idtplan) uses
	% depth (length of the longest branch), whereas the below
	% (idwtplan) uses weight (number of nodes in the plan).
	%
	% idtplan and itd2plan behave differently on one of the search
	% spaces defined at the top of the file, which is of the form:
	%
	%            1      
	%          / + \    
	%        11     12  
	%       /--\     |  
	%     111  112  121 
	%      |         |   
	%    1111       1211
	%
	% (where + means conjunctive branch and -- means disjunctive branch).
	% In this space, the first plan found by idtplan will be
	% 
	%                1 then [11 then 111 then 1111,
	%		         12 then 121 then 1211]
	%
	% followed by
	% 
	%                1 then [11 then 112,     
	%		         12 then 121 then 1211]
	%
	% as a second choice, whereas idwtplan would generate them in
	% exactly the reverse order.
idwtplan :- idwtplan(Plan), print_plan(Plan).
idwtplan(Plan) :- idwtplan(Plan,[],_).
idwtplan(Plan, Output, MaxDepth) :-
    genint(Bound),
    writef('Set max depth to %t\n',[Bound]),
    idwtplan(1, Bound, 1, Plan, Output, MaxDepth),
    (MaxDepth=Bound
     -> true
     ;  true %(writef('previously reported soln suppressed\n'),fail)
    ).

idwtplan(D,B,_,_,_,_) :-
    D>B, writef('trying to overstep depth %t\n',[B]),!,fail.
idwtplan(D,B,Input, Plan, [], D) :-
    D=<B,
    generate_node(Input, Plan, []),
    writef('visited %t\n',[Input]),
    writef('	Branch terminated at depth %t (max depth is %t)\n',[D,B]).
idwtplan(Depth,Bound,Input, P1 then P2, Output, MaxDepth) :-
    Depth =< Bound, 
    generate_node(Input, P1, [O|Os]),
    writef('visited %t\n',[Input]),
    iterate_idwtplan(Depth,Bound,[O|Os], P2, Output, MaxDepth).

iterate_idwtplan(D,_,[],[],[],D).
iterate_idwtplan(D,B,[I|Is], [P|Ps], Os,D3) :-
	(Os==[]->O1=[];true),
    D1 is D+1,
    idwtplan(D1,B,I,P,O1,D2),
    writef('first conjunctive subplan finished?\n'),
    append(O1,O1s,Os),
    iterate_idwtplan(D2,B,Is,Ps,O1s,D3).



/*
 * @(#)$Id: plan_idht.pl,v 1.4 1997/01/14 10:45:35 img Exp $
 *
 * $Log: plan_idht.pl,v $
 * Revision 1.4  1997/01/14 10:45:35  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:14  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:53  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_idht.pl,v 1.4 1997/01/14 10:45:35 img Exp $').

 /*
 *This file contains a version of the depth-first planner which does
 * deepening.
 */

/*
 * Some notes on the combinatorics of iterative deepening:
 * If b is the branching rate of the search space, and
 *    at(n) is the number of nodes at level n, and
 *    u(n) is the number of nodes up to and including level n, and
 *    id(n) is the number of nodes visited by iterative deepening to
 *              a depth of n
 * Then:
 *    at(0)=1, at(n+1)=b*at(n) ==> at(n)=b^n
 *    u(0) =1, u(n+1)=sigma(i from 0 to n+1 of at(i)) ==>u(n)=(b^(n+1)-1)/(b-1)
 *    id(0) =1, id(n+1)=sigma(i from 0 to n-1 of id(i))+u(n)=
 *                    sigma(i from 0 to n of u(i))    ==>
 *              id(n)=(b^(n+2)-b)/((b-1)^2) - (n+1)/(b-1)
 * Interestingly, id(n)=O(b^n), and also u(n)=O(b^n), and also at(n)=O(b^n) 
 * in other words, the work done for id(n) is completely dominated by the
 * last iteration of the search on the full tree of depth n, which is in
 * turn dominated by the work done at the lowest level in the tree.
 *
 * See also the analysis in "Optimal path finding algorithms", R.E.Korf,
 * in "Search in AI", L.Kanal, V.Kumar (eds.), Springer Verlag 1988, pp.
 * 223-267, section 2.3.
 *
 * There, iterative deepening (ID) is also compared with breadth-first 
 * search (BF). Both ID and BF are of O(b^n), but BF is of course more
 * efficient in run-time than ID. However, the ratio between their
 * running times is only b/(b-1)[1], whereas the space requirements of BF
 * is O(b^n) and that of ID is only O(n). Thus, ID is asymptotically
 * optimal in both time and space, whereas BF is asymptotically optimal
 * only in time and really bad in space, and the running times of ID and
 * BF are very close.
 *
 * [1] This can be seen as follows: let bf(n) be the number of nodes
 * visited by searching breadth-first up to and including level n,
 * then (obviously) bf(n)=at(n)=(b^(n+1)-1)/(b-1),
 * and id(n)/bf(n)=b/(b-1)-(n+1)/(b^(n+1)-1)~=~b/(b-1)
 *
 * Some quick measurements have shown that on the collection of pnat
 * theorems (assp,comp2,comm,assm,dist,comp), using the methods with
 * generalisation and induction, but without the ind_strat, the
 * branching factor was 2.77714 (over 175 nodes).
 */

	% idhtplan(Hints,+Depth,+Bound,+Input,?Plan,?Output,?MaxDepth) is just as
	% dplan(Input,Plan,Output), except that Depth represents the
	% current length of (this branch of) the plan, and Bound
	% represents the current maximum on the depth of the plan.
	% MaxDepth is the length of the longest branch in the proof (and
	% will not exceed Bound). 
	% The top-level predicate idhtplan/2 calls idhtplan/5 with
	% increasingly large Bound.
	%
	% An interesting variation of the first clause is to identify
	% MaxDepth and Bound. This will generate only plans of depth
	% Bound. Apart from maybe being useful in its own right, it also
	% suppresses returning solutions already found under shorter
	% Bounds (However, it only suppresses *returning* them, not
	% *generating* them which is what we would want).
	%
	% Second clause is for tracing info only. Otherwise it could
	% just be deleted.
	%
	% Notes:
	% - would be nice if we wouldn;t have to redo all work up
	%   to level n when increasing bound to n+1
	% - would be nice if we could avoid solutions being generated
	%   twice (this maybe comes for free if we do the previous point)
	% - would be nice if we could increase bounds by steps of d,
	%   rather than fixed d=1. Could be done by writing genint(N,Delta),
	%   where genint/1 is like genint/2 with Delta=1, and passing
	%   Delta into idhtplan/4 as an extra argument. What we can also
	%   do is to increase d non-constantly. We first step through
	%   the top few layers of the tree with big strides (since
	%   overshooting (the penalty for d being too big) in those
	%   regions is not too expensive), but lower down we only
	%   increase by small amounts. Current version of delta/1 does:
	%   d={8,4,2,1,1,1....}, and thus generates as values for Bound:
	%   Bound={8,12,,14,15,16,17,...}
	% - would be nice if we could spot plan failure before max depth
	%   is reached, to prevent endless looping. This would be
	%   possible by introducing a clause 
	%   for idhtplan that succeeds when D>B, and sets a global flag.
	%   The first clause of idhtplan should then check that this flag
	%   has indeed been set before increasing the Bound. If the flag
	%   is not set, there is no point in increasing the Bound, and
	%   we should fail alltogether.
	% - would be nice if we could impose an overall limit on the
	%   size of Bound, to stop everything when things get too
	%   ridiculous. Would be possible by introducing MaxBound as an
	%   argument to idhtplan/4, and to check that Bound=<MaxBound
	%   before calling idhtplan/6
	%
	% idhtplan/2 can be used if we're not interested in depth-arg.
	% Provided for consistency with other planners, which are all of
	% arity 2.
	%
	% Notice how the first clause of idhtplan (the terminating case),
	% allows D=<B, but that the second clause (the recursive case)
	% requires D<B. This is because in this case we know we are
	% going to need at least one more level to finish the plan
	% (otherwise the first case would have triggered, and we
	% woulnd't have reached the second).
idhtplan(Hints) :- idhtplan(Hints,Plan),print_plan(Plan),idhtplan:=Plan.

idhtplan(Hints,Plan) :- idhtplan(Hints,Plan,[]).

idhtplan(Hints,Plan,Effects) :-
        goal(Input), hyp_list(H),
	idhtplan(Hints,H==>Input,Plan,Effects).

idhtplan(Hints,Input,Plan,Effects) :- 
    all_present(Hints),
    abolish(no/1),
    assert(no(nothing)),
    idhtplan(Hints,Input, Plan, Effects, _).

idhtplan(Hints, Input, Plan, Effects, MaxDepth) :- 
    bound(Bound),
    plantraced(10,writef('Increased max depth to %t\n',[Bound])),
    MaxDepth=Bound, % supresses reporting results found under lower Bound
    idhtplan(Hints, 1, Bound, Input, Plan, X/\X, root, Effects, MaxDepth).

% Dynamic declaration for collecting stats:
% :- dynamic idhtplan/9.

idhtplan(Hints,D,B, Input, Plan, Plan/\Method, Path, Effects, D) :-
    D=<B,
    next_mthd( Hints, _, Input, Method, Plan/\Method, Path, Effects ),
    plantraced(20,
	    writef('%rTerminating method at depth %t: %t\n',['|',D,D,Method])).

idhtplan(Hints,D,Bound,Input, Plan, Plan_so_far/\Next, Path, Effects, MaxD) :-
    D < Bound, D1 is D+1,
    next_mthd( Hints, Rest, Input, Method, Plan_so_far/\Next, Path, [E|Es] ),
    \+no(Method),
    Next = (Method then New),
    concat_method(Path,Method,NewPath),
    plantraced(20,
	       writef('%rSelected method at depth %t: %t\n',['|',D,D,Method])),
    iterate_idhtplan(Rest,D1,Bound,[E|Es],Plan,
                     Plan_so_far/\New, NewPath, 1, Effects, MaxDs),
    max(MaxDs,MaxD).

	% iterate_idhtplan/10 is just like iterate_dplan/8, but it also
	% collects the max. depths for all the branches (in the last
	% arg), so that idhtplan can take the max of that list.


iterate_idhtplan(_,_,_,[],Plan,Plan/\[],_,_,[],[]).

iterate_idhtplan(Hints,
                 D,
                 B,
                 [Input|Inputs], 
                 Plan,
                 Plan_so_far/\[N|Ext],
                 Path,
                 Branch,
                 Effects, 
                 [D1|Ds]) :-

    (Effects==[]->Effect=[];true),
    add_branch(Branch,Path,NewPath),
    idhtplan(Hints,D,B,Input, _, Plan_so_far/\N, NewPath, Effect, D1),
    (Effect==[]->!;true),
    append(Effect,OtherEffects,Effects),
    NewBranch is Branch +1,
    iterate_idhtplan(Hints,D,B,Inputs, Plan, Plan_so_far/\Ext,
                      Path, NewBranch, OtherEffects,Ds).



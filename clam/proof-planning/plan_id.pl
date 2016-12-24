/*
 * @(#)$Id: plan_id.pl,v 1.8 1997/01/14 10:45:34 img Exp $
 *
 * $Log: plan_id.pl,v $
 * Revision 1.8  1997/01/14 10:45:34  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.7  1996/12/04 12:59:05  img
 * Added conjecture and time taken slot to proof_plan object.
 *
 * Revision 1.6  1995/10/03  13:13:12  img
 * added "plan" record for library mechanism to access
 *
 * Revision 1.5  1995/05/17  02:19:12  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.4  1995/03/01  04:15:49  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.3  1995/02/08  17:28:44  img
 * 	* added resetAppInd
 *
 * Revision 1.2  1994/09/16  10:53:44  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_id.pl,v 1.8 1997/01/14 10:45:34 img Exp $').

/* Some notes on the combinatorics of iterative deepening:
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

        % idplan(+Depth,+Bound,+Input,?Plan,?Output,?MaxDepth) is just as
        % dplan(Input,Plan,Output), except that Depth represents the
        % current length of (this branch of) the plan, and Bound
        % represents the current maximum on the depth of the plan.
        % MaxDepth is the length of the longest branch in the proof (and
        % will not exceed Bound). 
        % The top-level predicate idplan/2 calls idplan/5 with
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
        %   Delta into idplan/4 as an extra argument. What we can also
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
        %   for idplan that succeeds when D>B, and sets a global flag.
        %   The first clause of idplan should then check that this flag
        %   has indeed been set before increasing the Bound. If the flag
        %   is not set, there is no point in increasing the Bound, and
        %   we should fail alltogether.
        % - would be nice if we could impose an overall limit on the
        %   size of Bound, to stop everything when things get too
        %   ridiculous. Would be possible by introducing MaxBound as an
        %   argument to idplan/4, and to check that Bound=<MaxBound
        %   before calling idplan/6
        %
        % idplan/2 can be used if we're not interested in depth-arg.
        % Provided for consistency with other planners, which are all of
        % arity 2.
        %
        % Notice how the first clause of idplan (the terminating case),
        % allows D=<B, but that the second clause (the recursive case)
        % requires D<B. This is because in this case we know we are
        % going to need at least one more level to finish the plan
        % (otherwise the first case would have triggered, and we
        % woulnd't have reached the second).
idplan :-
    idplan(Plan),
    print_plan(Plan),
    idplan:=Plan.

idplanTeX :-
    idplanTeX(Plan),
    print_plan(Plan),
    idplan:=Plan.

idplan(Plan) :- idplan(Plan,[]).

idplanTeX(Plan) :-
    startoutputTeX,
    idplan(Plan,[]),
    stopoutputTeX.

/* allow a maximum depth to be predetermined */
idplan_max(D) :- idplan_max(D,Plan),print_plan(Plan),idplan:=Plan.
idplan_max(Depth,Plan) :-			
    goal(Input), hyp_list(H),
    resetAppInd,
    idplan_max(H==>Input,Plan,[],Depth),
    cthm =: T,
    uniq_recorda(proof_plan,proof_plan(H==>Input,T,_,Plan,idplan),_).

idplan_max(Input, Plan, Effects, MaxDepth) :- 
    print_planning_info(boundinc,tuple(MaxDepth)),
    idplan(1, MaxDepth, Input, Plan, Effects, MaxDepth).

idplan(Plan,Effects) :-
    goal(Input), hyp_list(H),
    resetAppInd,
    idplan(H==>Input,Plan,Effects).

idplan(Input,Plan,Effects) :- idplan(Input, Plan, Effects, _).

idplan(Input, Plan, Effects, MaxDepth) :- 
    bound(Bound),
    print_planning_info(boundinc,tuple(Bound)),
    MaxDepth=Bound, % supresses reporting results found under lower Bound
    idplan(1, Bound, Input, Plan, Effects, MaxDepth).

% Dynamic declaration for collecting stats:
% :- dynamic idplan/6.
idplan(A,B,C,D,E,F) :- idplan_(A,B,C,D,E,F).

idplan_(D,B,Input,Plan,Effects,_MD) :-
    Input=(H==>G),       
    print_planning_info(pre,tuple(D,H,G)),
    applicable(H==>G,Method,_,RealEffects),
    proceed_idplan(D,B,Input,Method,RealEffects,Effects,D,Plan).
idplan_(D,_,_,_,_,_) :-
    print_planning_info(failure,tuple(D)),
    !,
    fail.

proceed_idplan(D,B,_Input,Method,Effects,Effects,D,Plan) :-
    D =< B,
    Effects \= _-_,
    print_planning_info(postTerm,tuple(D,Method)),
    Plan = Method.
proceed_idplan(D,B,_Input,Method,[E|Es],Effects,MD,Plan) :-
    % [E|Es] = RealEffects
    D < B,
    print_planning_info(selection,tuple(D,Method)),
    D1 is D+1,  
    iterate_idplan(D1,B,[E|Es],RestPlans,Effects,MaxDs),%empty substitution
    Plan = (Method then RestPlans),
    max(MaxDs,MD).

        % iterate_idplan/6 is just like iterate_dplan/3, but it also
        % collects the max. depths for all the branches (in the last
        % arg), so that idplan can take the max of that list.
iterate_idplan(_,_,[],[],[],[]).
iterate_idplan(D,B,[Input|Inputs], [Plan|Plans], Effects, [D1|Ds]) :-
        (Effects==[]->Effect=[];true),
    idplan(D,B,Input,Plan,Effect,D1),
        (Effect==[]->!;true),
    append(Effect,OtherEffects,Effects),
    iterate_idplan(D,B,Inputs,Plans,OtherEffects,Ds).

        % This is the predicate that generates new values for the
        % maximum depth of the tree to be searched.
        %
        % First version just increases B by 1 on every backtrack.
% bound(B) :- genint(B).
        % Second version increases B by a fixed Delta on every backtrack.
% bound(B,Delta) :- genint(B,Delta).
        % Third version icreases B by a varying amount, computed by delta/1
        % beware interaction with suppression of results from
        % previous depths if delta is not unit increment!!
bound(B) :- genint(N), bound(N,B).
bound(0,0).
bound(N,B) :- N>0, N1 is N-1, bound(N1,B1),delta(N,D), B is B1+D.
delta(_,1).


/*
 * @(#)$Id: plan_gdf.pl,v 1.4 1997/01/14 10:45:31 img Exp $
 *
 * $Log: plan_gdf.pl,v $
 * Revision 1.4  1997/01/14 10:45:31  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:09  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:42  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_gdf.pl,v 1.4 1997/01/14 10:45:31 img Exp $').

/*
 * This file contains code for a version of the depth-first proof
 * planner from plan-df.pl which does ordering on the applicable
 * methods, rather than just taking the order in which they occur in the
 * database.
 *
 * For comments on the code of the planner, see plan-df.pl. This file
 * only contains comments for the bits of code different from plan-df.pl
 */

gdplan :- gdplan(Plan), print_plan(Plan),gdplan:=Plan.
gdplan(Plan) :- gdplan(Plan,[]).
gdplan(Plan,Effects) :-
    goal(Input), hyp_list(H),
    gdplan(H==>Input,Plan,Effects).

        % The most obvious implementation would select a method by
        % running applicable/4 exhaustively via setof, and then run a
        % selection routine to pick an element from the resulting list
        % of Methods+Effects, using the selection routine as a
        % backtrack point. However, this involves computing the effects
        % of all applicable methods, which is very expensive (eg.
        % ind_strat), while these may be thrown away straight away
        % during selection.  
        % A good (bad) example of this is the goal: plus(a,b)=plus(a,b)
        % This would involve computing a very expensive ind_strat(a),
        % while the first thing that would happen is the selection of
        % simplify.
        %
        % To avoid this problem we let the selection method generate the
        % effects of the selected method, so that it can decide which
        % effects it wants/needs to compute, avoiding the exhaustive
        % computation of the setof-solution.
        % This also allows for some special case coding for Effects=[]
        % inside the selection routine.
% Dynamic declarion to be switched on when taking stats.
% :- dynamic gdplan/3.

gdplan(Input,Method,Effects) :-
    select_method(Input,Method,Effects),
            plantraced(20,writef('Selected method: %t\n',[Method])).
gdplan(Input, First then RestPlans, Effects) :-
    select_method(Input, First, [E|Es]),
            plantraced(20,writef('Selected method: %t\n',[First])),
    iterate_gdplan([E|Es],RestPlans,Effects).

iterate_gdplan([],[],[]).
iterate_gdplan([Input|Inputs], [Plan|Plans], Effects) :-
        (Effects==[]->Effect=[];true),
    gdplan(Input,Plan,Effect),
        (Effect==[]->!;true),
    append(Effect,OtherEffects,Effects),
    iterate_gdplan(Inputs,Plans,OtherEffects).


        % g_applicable is like applicable/[1,2], but uses the
        % select_method predicate.
g_applicable(M) :-
    goal(I), hyp_list(H),
    g_applicable(H==>I,M).
g_applicable(I,M) :-
    select_method(I,M,_).

        % select_method(+Input, ?Method, ?Effects) selects a
        % Method and computes the corresponding Effects from the set of
        % all methods applicable to Input. Care is taken to not compute
        % any expensive effects of methods we will not select anyway
        % (see also comment above at gdplan/3). We also don't want to
        % recompute the set of applicable methods for every selection
        % clause (takes in the order of 1 sec of CPU time), so we start by
        % computing that, and passing that set of 
        % applicable methods into the selection clauses. 
        %
        % One PROBLEM with the current code of select_methods is that
        % care has to be taken while writing the code that no 
        % methods will be selected more than once. This would
        % affect the backtracking behaviour of the planner rather badly,
        % reproducing whole parts of the search space.
        %
        % We also do some special case coding for when Effects=[]. If we
        % want (or can get) Effects=[], we take any old method we can
        % find that does the trick.
select_method(Input,Method,[]) :-
    applicable(Input,Method,_,[]),!.
select_method(Input,Method,[E|Es]) :-
    findset(M,applicable(Input,M),Ms),
    Ms \= [],
    select_method(Input,Ms,Method,[E|Es]).

        % If any of
        % [iterator({base,wave}),base,wave,fertilize_{left,right}]
        % are applicable, take that and don't look back.
        % The cut should avoid endless backtracking over permutations of
        % these methods.  Notice that the order of
        % [base,wave,fertilize_{left,right}] is significant. 
select_method(Input, Ms, Method, Effects) :-
%    yn(3,'find [base,wave,fertilize_{left,right}]: '),
    (/*
     Method=base_rewrites(_) ;
     Method=ripple_out(_) ;
     */
     Method=base(_,_) ;
     Method=wave(_,_)  ;
     Method=fertilize_left(_,_) ;
     Method=fertilize_right(_,_)),
    member(Method,Ms),
    applicable(Input,Method,_,Effects),!.

        % Try to avoid inductive methods. If this doesn't
        % work, the next clause schedules inductions.
select_method(Input, Ms, Method, Effects) :-
%    yn(3,'avoid induction: '),
    member(Method,Ms),
    Method\=ind_strat(_,_),
    Method\=induction(_,_),
    applicable(Input,Method,_, Effects).

        % If we can't avoid induction, take the induction on the
        % variable with least flawed positions.
        % We compute for every variable inductive candidate Var
        % a pair [N,Var], whith N the number of flawed
        % occurences of Var. We then sort the list on N, and pick 
        % variables with successively more flawed occurences. Again, we
        % prefer ind_strats over inductions.
        %
        % All this could be extended with a more informed
        % recursion-analysis in the future.
select_method(H==>G,Ms,Method,Effects) :-
%    yn(3,'find least flawed induction: '),
    findset([NrFlaws,S,Var:T], 
       (findset((S,Var:T),(member(ind_strat(S,Var:T),Ms);
                     member(induction(S,Var:T),Ms)),Vars),
        Vars \= [],
        member((S,Var:T),Vars),
        all_flawed_pos(Var,G,FlawPoss),
        length(FlawPoss,NrFlaws)
       ), NrsFlaws),
    NrsFlaws \= [],
    sort(NrsFlaws, SortedVars),
    (Method=ind_strat(S,BestVar:T);Method=induction(S,BestVar:T)),
    member([_,S,BestVar:T],SortedVars),
    member(Method,Ms),
    applicable(H==>G,Method,_,Effects).

        % flawed_pos(?SubExp,+Exp,?Pos): SubExp occurs in a flawed
        % position inside Exp at position Pos, where flawed is defined
        % as: occuring as an argument of a recursive predicate, but in a
        % non-recursive position. 
flawed_pos(SubExp,Input,[N|FlawPos]) :-
    exp_at(Input,[N|FlawPos],SubExp),
    N\=0, % functors are excluded from competition.
    exp_at(Input,[0|FlawPos],F),
    prim_rec(F,M), M\=N.


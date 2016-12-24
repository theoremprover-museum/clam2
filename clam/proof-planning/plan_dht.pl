/*
 * @(#)$Id: plan_dht.pl,v 1.6 1997/01/14 10:45:28 img Exp $
 *
 * $Log: plan_dht.pl,v $
 * Revision 1.6  1997/01/14 10:45:28  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.5  1996/12/04 12:59:04  img
 * Added conjecture and time taken slot to proof_plan object.
 *
 * Revision 1.4  1996/08/01  10:52:35  img
 * Add plan object to database. Use print_planning_info.
 *
 * Revision 1.3  1995/05/17  02:19:07  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:37  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_dht.pl,v 1.6 1997/01/14 10:45:28 img Exp $').

/*
 * This file contains code for a depth-first proof planner with a hint
 * mechanism. For description see: <Dissertation to come>.
 */

	% dhtplan(+Hints,+Input,?Plan,?Effects) generates a plan (ie. a sequence
	% of (actually a tree of) applications of methods), that, when
	% applied to Input will produce Effects.
	%
	% Usage as dhtplan(+,+, -, []) forces the generation of
	% complete plans, but it is of course also possible to generate
	% partial plans, via dhtplan(+,+,-,-). Usage as dhtplan(+,+,+) will
	% check the correctness of a plan, and dhtplan(+,+,-) will compute
	% the effects of a plan.
	% 	
	% The plan is produced in a depth-first manner:
	% We choose a first step in the plan, and then generate all
	% possible sequel plans before redoing our choice for the first step.
	% 	
	% This planner behaves very similar to the dplan in plan-df file.
	% In this planner the one more argument (the first one)  is added to 
	% receive a list of hints. If the list is empty, the planner will 
        % behave like dplan. If hints are provided, the planner will try to 
        % use them at before it uses the next applicable hint.
	%
        % Another difference is that this planner builds the complete plan by 
        % "pushing" down the partial plan built so far, to the next recursion
        % level. This is necessary to show the user the status of the plan 
        % when using the interactive (askme) mode. 
        %
        % Another argument contains the path from the root to the currently 
        % investigated node. This is used to check for the applicablility of 
        % hints.
        % 
        % Again, first clauses for human consumption only: provides
	% Input (the current goal and hypothesis list) and Effects ([]).
dhtplan(Hints) :- dhtplan(Hints,Plan), print_plan(Plan),dhtplan:=Plan.
dhtplan(Hints,Plan) :- dhtplan(Hints,Plan,[]).
dhtplan(Hints,Plan,Effects) :-
    goal(Input), hyp_list(H),
    resetAppInd,
    dhtplan(Hints,H==>Input,Plan,Effects),
    cthm =: T,
    uniq_recorda(proof_plan,proof_plan(H==>Input,T,_,Plan,dhtplan),_).

	% Actually, I've been lying about the arity: the real predicate
	% is dhtplan/4. All the last argument does is pass on the current
	% depth of the plan for debugging output purposes.
dhtplan(Hints,Input,Plan,Effects) :-
    all_present(Hints),
    abolish(no/1),
    assert(no(nothing)),
    dhtplan(Hints,Input,Plan,X/\X,root,Effects,0).


%-------------------------------------------------------------------sny
% Name: dhtplan/7
%
% Arguments:
%  1) A list of Hints (+).
%  2) An input sequent (+).
%  3) Plan (?), normally (-).
%  4) Partial plan (+). 
%  5) Path from root to current sequent in partial plan (+).
%  6) Desired effects (?).
%  7) Depth.
%
% Comments: In Plan/\V, V is the variable in Plan where the next step 
% will be instantiated. 
%


% Dynamic declaration to be switched on when collecting stats. I hate
% Quintus for this!
% :- dynamic dhtplan/4.

dhtplan( Hints, Input, Plan, Plan/\Method, Path, Effects, D ) :-
    next_mthd( Hints, _, Input, Method, Plan/\Method, Path, Effects ),
    print_planning_info(postTerm,tuple(D,Method)).

dhtplan( Hints, Input, Plan, Plan_so_far/\Next, Path, Effects, D ) :-
    next_mthd( Hints, Rest, Input, Method, Plan_so_far/\Next, Path, [E|Es] ), 
    \+no(Method),
    Next = (Method then New),
    concat_method(Path,Method,NewPath),
    plantraced(25, (Input=(_==>G),writef('==>%t\n',[G]))),	   
    print_planning_info(selection,tuple(D,Method)),
    D1 is D+1,	
    iterate_dhtplan(Rest, [E|Es], Plan, Plan_so_far/\New, NewPath, 1, Effects, D1).

	% All iterate_dhtplan does is iterate dhtplan/4 over a conjunction of
	% subgoals. Not really for human consumption.
	%
	% Optimisation 1:
	% The natural order of the conjuncts in clause 2 is:
	%  1. first do dhtplan(Hints,Input), giving Plan and Effects
	%  2. then do iterate_dhtplan, giving Plans and OtherEffects
	%  3. combine the whole sjebang using append.
	% However, in the case that Effects is intantiated by the user
	% (for instance in the likely case that Effects=[]), it's a
	% waste to have the [Other]Effect arguments to dhtplan and
	% iterate_dhtplan be uninstantiated. After having done dhtplan, giving
	% Effects, we can safely compute OtherEffects via append, before
	% giving it to iterate_dhtplan. This might not help at all (if Effects
	% is var), but will help a lot if Effects is bound.
	%
	% Optimisation 2:
	% Moving append forward in the conjunction still leaves Effect
	% always unbound, even when Effects is bound. We put in a special
	% case optimisation for the case Effects=[], when we can
	% confidently set Effect to [].
	% 
	% Optimisation 3:
	% A final optimisations
	% 		(Effect=[]->!;true)
	% Having this around commits plans once they are succesful, ie.
	% if we know a branch can be done successfully one way, we won't
	% try to compute any other ways of doing it. This of course
	% affects the completeness of the planner.
	%
	% These three optimisations together reduce the search time for
	% the ind_strat by a factor of 20. This version is
	% exactly as fast for complete plans as a planner that can only
	% do complete plans (the programmer said proudly...)


%-------------------------------------------------------------------sny
% Name: iterate_dhtplan.
%
% Arguments:
%  1) List of hints (+).
%  2) Input list (+).
%  3) Plan (?), usually (-).
%  4) Partial plan built so far (with marker), (+).
%  5) Path from root to current sequent (+).
%  6) Branch label. Marks the position of Input in the original list (+).
%  7) Desired Effects (?).
%  8) Depth variable.
%
% Comments:
%

iterate_dhtplan( _, [], Plan, Plan/\[], _, _, [], _ ).

iterate_dhtplan( Hints,
	         [Input|Inputs],  
                 Plan, 
                 Plan_so_far/\[N|Ext], 
                 Path,
                 Branch,
                 Effects, 
                 D ):-
     
    	(Effects==[]->Effect=[];true),
    add_branch(Branch,Path,NewPath),
    dhtplan( Hints, Input, _, Plan_so_far/\N, NewPath, Effect, D ),
    	(Effect==[]->!;true),
    append(Effect,OtherEffects,Effects),
    NewBranch is Branch +1,
    iterate_dhtplan(Hints,Inputs, Plan, Plan_so_far/\Ext, 
                    Path, NewBranch, OtherEffects,D).


%-------------------------------------------------------------------sny


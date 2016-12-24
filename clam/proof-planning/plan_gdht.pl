/*
 * @(#)$Id: plan_gdht.pl,v 1.4 1997/01/14 10:45:32 img Exp $
 *
 * $Log: plan_gdht.pl,v $
 * Revision 1.4  1997/01/14 10:45:32  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:10  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:45  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_gdht.pl,v 1.4 1997/01/14 10:45:32 img Exp $').

/*
 * This file contains code for a version of the depth-first proof
 * planner from plan-df.pl which does ordering on the applicable
 * methods, rather than just taking the order in which they occur in the
 * database.
 *
 * For comments on the code of the planner, see plan-df.pl. This file
 * only contains comments for the bits of code different from plan-df.pl
 */

gdhtplan(Hints) :- gdhtplan(Hints,Plan), print_plan(Plan),gdhtplan:=Plan.
gdhtplan(Hints,Plan) :- gdhtplan(Hints,Plan,[]).
gdhtplan(Hints,Plan,Effects) :-
    goal(Input), hyp_list(H),
    gdhtplan(Hints,H==>Input,Plan,Effects).

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

gdhtplan(Hints,Input,Plan,Effects) :-
    all_present(Hints),
    abolish(no/1),
    assert(no(nothing)),
    gdhtplan(Hints,Input,Plan,X/\X,root,Effects,0).


%-------------------------------------------------------------------sny
% Name: gdhtplan/7
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


gdhtplan( Hints, Input, Plan, Plan/\Method, Path, Effects, D ) :-
 (applicable_hints( Hints, Rest, Input, Method,  Plan/\Method, Path, Effects ) ;
   select_method(Input,Method,Effects), Rest=Hints),
               plantraced(20,
           writef('%rTerminating method at depth %t: %t\n',['|',D,D,Method])).

gdhtplan( Hints, Input, Plan, Plan_so_far/\Next, Path, Effects, D ) :-
   (applicable_hints( Hints, Rest, Input, Method,  
                      Plan_so_far/\Next, Path, [E|Es] ) ;
   select_method(Input,Method, [E|Es]), Rest=Hints),
    \+no(Method),
    Next = (Method then New),
    concat_method(Path,Method,NewPath),
	   plantraced(25, (Input=(_==>G),writef('==>%t\n',[G]))),	   
           plantraced(20,
           writef('%rSelected method at depth %t: %t\n',['|',D,D,Method])),
    D1 is D+1,	
iterate_gdhtplan( Rest, [E|Es], Plan, Plan_so_far/\New, NewPath, 1, Effects, D1).

	% All iterate_gdhtplan does is iterate gdhtplan/4 over a conjunction of
	% subgoals. Not really for human consumption.
	%
	% Optimisation 1:
	% The natural order of the conjuncts in clause 2 is:
	%  1. first do gdhtplan(Hints,Input), giving Plan and Effects
	%  2. then do iterate_gdhtplan, giving Plans and OtherEffects
	%  3. combine the whole sjebang using append.
	% However, in the case that Effects is intantiated by the user
	% (for instance in the likely case that Effects=[]), it's a
	% waste to have the [Other]Effect arguments to gdhtplan and
	% iterate_gdhtplan be uninstantiated. After having done gdhtplan, giving
	% Effects, we can safely compute OtherEffects via append, before
	% giving it to iterate_gdhtplan. This might not help at all (if Effects
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
% Name: iterate_gdhtplan.
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

iterate_gdhtplan( _, [], Plan, Plan/\[], _, _, [], _ ).

iterate_gdhtplan( Hints,
	         [Input|Inputs],  
                 Plan, 
                 Plan_so_far/\[N|Ext], 
                 Path,
                 Branch,
                 Effects, 
                 D ):-
     
    	(Effects==[]->Effect=[];true),
    add_branch(Branch,Path,NewPath),
    gdhtplan( Hints, Input, _, Plan_so_far/\N, NewPath, Effect, D ),
    	(Effect==[]->!;true),
    append(Effect,OtherEffects,Effects),
    NewBranch is Branch +1,
    iterate_gdhtplan(Hints,Inputs, Plan, Plan_so_far/\Ext, 
                    Path, NewBranch, OtherEffects,D).





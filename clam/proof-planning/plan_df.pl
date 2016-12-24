/*
 * @(#)$Id: plan_df.pl,v 1.18 2005/05/06 19:40:17 smaill Exp $
 *
 * $Log: plan_df.pl,v $
 * Revision 1.18  2005/05/06 19:40:17  smaill
 * Use sicstus timing devices
 *
 * Revision 1.17  1999/05/19 15:59:00  julianr
 * Modified library mechanism to produce commuted variants of loaded equations
 * which involve a commutative function, and changed the timing code.
 *
 * Revision 1.16  1998/11/10 16:06:53  img
 * added generalized resource bound exception handler
 *
 * Revision 1.15  1998/09/30 07:41:25  img
 * added resource exception handler
 *
 * Revision 1.14  1998/05/13 13:05:50  img
 * allow Duration spec in dplan
 *
 * Revision 1.13  1997/11/12 15:16:23  img
 * fix dplanTeX
 *
 * Revision 1.12  1997/11/11 17:25:47  img
 * idplanTeX added
 *
 * Revision 1.11  1997/01/14 10:45:27  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.10  1996/12/11 14:19:40  img
 * typo.
 *
 * Revision 1.9  1996/12/06 14:48:24  img
 * Spurious comment removed.
 *
 * Revision 1.8  1996/12/06 14:39:05  img
 * Time-out/timing support added.
 *
 * Revision 1.7  1996/12/04 12:54:45  img
 * Some modifications useful for benchmarking.
 *
 * Revision 1.6  1995/10/03  13:13:10  img
 * added "plan" record for library mechanism to access
 *
 * Revision 1.5  1995/05/17  02:19:05  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.4  1995/03/01  04:15:34  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.3  1995/02/08  17:28:42  img
 * 	* added resetAppInd
 *
 * Revision 1.2  1994/09/16  10:53:42  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_df.pl,v 1.18 2005/05/06 19:40:17 smaill Exp $').

?- use_module(library(timeout)).

        % dplan(+Input,?Plan,?Effects) generates a plan (ie. a sequence
        % of (actually a tree of) applications of methods), that, when
        % applied to Input will produce Effects.
        %
        % Usage as dplan(+, -, []) forces the generation of
        % complete plans, but it is of course also possible to generate
        % partial plans, via dplan(+,-,-). Usage as dplan(+,+,+) will
        % check the correctness of a plan, and dplan(+,+,-) will compute
        % the effects of a plan.
        %       
        % The plan is produced in a depth-first manner:
        % We choose a first step in the plan, and then generate all
        % possible sequel plans before redoing our choice for the first step.
        %       
        % The idea is very simple: a plan is either the application of a
        % single method (clause 1), or the application of a single
        % method followed by subsequent plans (clause 2).
        %
        % The only thing to notice is that we force the effects of
        % applicable to be non-[]. Otherwise we would repeat results with
        % Effects=[] already generated by the clause 1.
        % 
        % Again, first clauses for human consumption only: provides
        % Input (the current goal and hypothesis list) and Effects ([]).
dplan :-
    dplan(Plan),
    print_plan(Plan),
    dplan:=Plan.
dplan(Plan) :-
    dplan(_,Plan).
dplan(Duration,Plan) :-
    dplan(Duration,Plan,[]).

dplanTeX :-
    dplanTeX(Plan),
    print_plan(Plan),
    dplan:=Plan.
dplanTeX(Plan) :-
    startoutputTeX,
    dplan(Plan),
    stopoutputTeX.

dplan(Duration,Plan,Effects) :-
    goal(Input),
    hyp_list(H),
    dplan(Duration,Plan,Effects,Input,H).    

dplan(Duration,Plan,Effects,Input,H) :-
    resetAppInd,
   ( var(Duration) -> dplan_unlimited( Plan, Effects,Input,H )
   ;
       statistics(runtime,[StartMS|_]),
       on_exception(resource_error(_,Res,_),
                    ( time_out(dplan(H==>Input,Plan,Effects,0), Duration, Result),
                       (   Result = time_out
		              -> ( clam_warning('Time limit of %ts exceeded.',[Duration]),
				   fail )
		         ; true )),
		    (  clam_warning('Out of resource (%t)',[Res]), fail ) ),
        statistics(runtime,[EndMS|_]),
    Taken is EndMS - StartMS,
    cthm =: T,
    clam_info('Time taken for %t is %t milliseconds.\n',[T,Taken]),
    uniq_recorda(proof_plan,proof_plan(H==>Input,T,Taken,Plan,dplan),_)
   ).

dplan_unlimited( Plan, Effects,Input,H ) :-
	statistics(runtime,[StartMS|_]),
	on_exception(resource_error(_,Res,_),
                     dplan(H==>Input,Plan,Effects,0),
		    (  clam_warning('Out of resource (%t)',[Res]), fail ) ),
        statistics(runtime,[EndMS|_]),
	Taken is EndMS - StartMS,
	cthm =: T,
	clam_info('Time taken for %t is %t milliseconds.\n',[T,Taken]),
	uniq_recorda(proof_plan,proof_plan(H==>Input,T,Taken,Plan,dplan),_).
    
%    (\+ var(Duration) ->  timeout_in(Duration,_,ExceptionLabel) ; ExceptionLabel = -1),
%    (ExceptionLabel = -1 ; (ExceptionLabel > -1 ; delete_timeout(ExceptionLabel), fail)),
%    statistics(runtime,[StartMS|_]),
%    on_exception(resource_error(_,Res,_),
%		 on_exception(timedout(ExceptionLabel),
%			      dplan(H==>Input,Plan,Effects,0),
%			      (clam_warning('Time limit of %ts exceeded.',[Duration]), delete_timeout(ExceptionLabel), fail)),
%		 (clam_warning('Out of resource (%t)',[Res]),fail)),
%    (delete_timeout(ExceptionLabel) -> true ; true),
%    statistics(runtime,[EndMS|_]),
%    Taken is EndMS - StartMS,
%    cthm =: T,
%    clam_info('Time taken for %t is %t milliseconds.\n',[T,Taken]),
%    uniq_recorda(proof_plan,proof_plan(H==>Input,T,Taken,Plan,dplan),_).

% Dynamic declaration to be switched on when collecting stats. I hate
% Quintus for this!
% :- dynamic dplan/4.

	% dplan has been modified so that it no longer
	% prefers terminating methods.

dplan(A,B,C,D) :- dplan_(A,B,C,D).
dplan_(Input,Plan,Effects,D) :-
    Input=(H==>G),
    print_planning_info(pre,tuple(D,H,G)),          
    applicable(Input,Method,_,RealEffects),
    proceed_dplan(D,Input,Method,RealEffects,Effects,Plan).
dplan_(_, _, _, D ) :-
    print_planning_info(failure,tuple(D)),
    !, fail.

proceed_dplan(D,_Input,Method,Effects,Effects,Plan) :-
    Effects \= _-_,
    print_planning_info(postTerm,tuple(D,Method)),
    Plan = Method.
proceed_dplan(D,_Input,Method,[E|Es],Effects,Plan) :-
    % [E|Es] = RealEffects
    print_planning_info(selection,tuple(D,Method)),
    D1 is D+1,  
    iterate_dplan([E|Es],RestPlans,Effects,D1),
    Plan = (Method then RestPlans).

        % All iterate_dplan/4 does is iterate dplan/4 over a conjunction of
        % subgoals. Not really for human consumption.
        %
        % Optimisation 1:
        % The natural order of the conjuncts in clause 2 is:
        %  1. first do dplan(Input), giving Plan and Effects
        %  2. then do iterate_dplan, giving Plans and OtherEffects
        %  3. combine the whole sjebang using append.
        % However, in the case that Effects is intantiated by the user
        % (for instance in the likely case that Effects=[]), it's a
        % waste to have the [Other]Effect arguments to dplan and
        % iterate_dplan be uninstantiated. After having done dplan, giving
        % Effects, we can safely compute OtherEffects via append, before
        % giving it to iterate_dplan. This might not help at all (if Effects
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
        %               (Effect=[]->!;true)
        % Having this around commits plans once they are succesful, ie.
        % if we know a branch can be done successfully one way, we won't
        % try to compute any other ways of doing it. This of course
        % affects the completeness of the planner.
        %
        % These three optimisations together reduce the search time for
        % the ind_strat by a factor of 20. This version is
        % exactly as fast for complete plans as a planner that can only
        % do complete plans (the programmer said proudly...)
iterate_dplan([],[],[],_).
iterate_dplan([Input|Inputs], [Plan|Plans], Effects, D) :-
        (Effects==[]->Effect=[];true),
    dplan(Input,Plan,Effect,D),
    (Effect=[]->! ; true ),
    append(Effect,OtherEffects,Effects),
    iterate_dplan(Inputs,Plans,OtherEffects,D).


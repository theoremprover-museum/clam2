/*
 * @(#)$Id: applicable.pl,v 1.18 2005/05/06 19:39:36 smaill Exp $
 *
 * $Log: applicable.pl,v $
 * Revision 1.18  2005/05/06 19:39:36  smaill
 * take out check_time_limit
 *
 * Revision 1.17  1998/09/16 13:53:25  img
 * Reordered clauses for applcble/5, and added applcble_pure/5.
 * Intention is to improve speed.
 *
 * Revision 1.16  1998/06/25 10:45:02  img
 * cosmetics; give warning on failing post-conditions
 *
 * Revision 1.15  1998/05/13 13:01:45  img
 * formatting of tracing
 *
 * Revision 1.14  1998/02/17 13:54:23  img
 * applcble/5: prettify o/p on tracing
 *
 * Revision 1.13  1997/10/09 14:58:54  img
 * call_conjunction/1 replaced with call_precondition/1
 *
 * Revision 1.12  1997/09/26 15:09:49  img
 * pre- and post-conditions no longer stored internally as lists, but
 * instead as Prolog conjunctions.  This means there is no need to waste time
 * transforming lists into conjunctions.
 *
 * Revision 1.11  1997/01/14 10:45:17  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.10  1996/12/06 14:38:59  img
 * Time-out/timing support added.
 *
 * Revision 1.9  1996/12/04 12:43:59  img
 * Call to check_time_limit/0, a place-holder for time-out check.
 *
 * Revision 1.8  1995/11/28  16:15:33  img
 * experimental "until" methodical
 *
 * Revision 1.7  1995/05/17  02:18:56  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.6  1995/05/15  15:39:32  img
 * 	* print_planning_info: print hypotheses
 *
 * Revision 1.5  1995/03/01  04:15:19  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.4  1995/03/01  03:44:15  img
 * 	* plan tracing does not display hypotheses
 *
 * Revision 1.3  1995/02/08  17:25:37  img
 * 	* removed unwanted debugging info
 * 	* scoped plan tracing; resetAppInd in planners
 *
 * Revision 1.2  1994/09/20  11:13:24  dream
 * 	* display the goal when tracing at level 30 or above
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: applicable.pl,v 1.18 2005/05/06 19:39:36 smaill Exp $').

/* version which has scoped plan tracing.*/
:- dynamic appIndent/1.
appIndent(0).

/*
 * This file contains procedures that reason about/with the methods
 * specified in the file method.pl, and contains such things as: is a
 * particular method applicable, which methods are applicable, what
 * would be the results of a method if we applied it, etc.
 */

/*
 * The main predicate is applicable/[1;2;3;4] and the corresponding
 * applicable_submethod/[1;2;3;4] for submethods. 
 * The predicates applicable/{1,2} check if a method is applicable
 * (either to current sequent or to a specified sequent), and
 * the predicates applicable/{3,4} check if a method is applicable
 * (either to current sequent or to a specified sequent), but also
 * compute what the effects- and output-slots would be if the method
 * were applied.
 *
 * In order to avoid a lot of repetition between the clauses for methods
 * and submethods, we map both applicable/n and applicable_submethod/n
 * into applcbl/n+1 (n=1,2,3,4) which does the work for both, but
 * distinguishes between methods and submethods on the basis of an extra
 * first argument.
 *
 * Also, the clauses for the methodicals try/1, then/2 and or/2 live in the
 * file methodical.pl, and we map the relevant cases of applcble/n to
 * applicable_{try,then,or}/n. 
 */

applicable(Method) :- applcble(method,Method).
applicable(Input,Method) :- applcble(method,Input,Method).
applicable(Method,Post,Effects) :- applcble(method,Method,Post,Effects).
% Switch dynamic declaration on for taking stats (nodesvisited)
% :- dynamic applicable/4.
applicable(Input,Method,Post,Effects) :-
    applcble(method,Input,Method,Post,Effects).

applicable_submethod(Method) :-
    applcble(submethod,Method).
applicable_submethod(Input,Method) :-
    applcble(submethod,Input,Method).
applicable_submethod(Method,Post,Effects) :-
    applcble(submethod,Method,Post,Effects).
applicable_submethod(Input,Method,Post,Effects) :-
    incAppInd,
    applcble(submethod,Input,Method,Post,Effects),
    decAppInd.
applicable_submethod(_Input,_Method,_Post,_Effects) :-
    appIndent(Indent),
    NewIndent is Indent - 4,
    retractall(appIndent(_)),
    asserta(appIndent(NewIndent)),
    !,fail.


/*
 * applcbl/[1;2;3;4] does the real work for both applicable/[1;2;3;4]
 * and applicable_submethod/[1;2;3;4].
 * From now on, for "Method", read "Method or Submethod depending on the
 * first argument".
 */

	% applcble(+Type,?Method) checks if Method is applicable in the
	% current context. Notice that Method can be partially or wholly
	% uninstantiated, so that applcbl/1 can be used to search for
	% all applicable methods. 
	%
	% First clause for human consumption only: provides Input
	% automatically using the current goal and hypothesis list.
applcble(Type,Method) :-
    goal(Input), hyp_list(H),
    applcble(Type,H==>Input,Method).
	% For the try/1 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of try/1 methodical.
applcble(Type,Input,Try_Method) :-
    functorp(Try_Method,try,1), !,
    applicable_try(Type,Input,Try_Method).
	% For the then/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of then/2 methodical.
applcble(Type,Input,Then_Method) :-
    functorp(Then_Method,then,2),!,
    applicable_then(Type,Input,Then_Method).
	% For the or/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of or/2 methodical.
applcble(Type,Input,Or_Method) :-
    functorp(Or_Method,or,2), !,
    applicable_or(Type,Input,Or_Method).
applcble(Type,Input,Until_Method) :-
    functorp(Until_Method,until,2), !,
    applicable_until(Type,Input,Until_Method).
applcble(Type,Input,Method) :-
    apply(Type,[Method,Input,Pre,_,_,_]),
    plantraced(30,writef('trying %t %t...\n',[Type,Method])),
    call_precondition(Pre).

	% applcble(+Type,?Input,?Method, ?Post,?Effects): succeeds if Method is
	% applicable on Input and Post and Effects are the resulting
	% postconditions and effects. Possible usage includes
	% applcble(+,+,+,-,-) to compute postconds/effects of a given method,
	% applcble(+,+,-,-,-) to search for applicable methods , and
	% applcble(+,+,-,-,+) or applcble(+,+,-,+,-) to search for methods
	% that will give certain desired postconditions/effects. 
	%
	% applcbl/5 subsumes applcbl/3, but is more expensive.
	% Therefore we keep applcbl/3 around anyway.
	% 
	% We cant get away with just calling applcbl/3, but rather
	% have to explicitly call the body of applcbl/3 as the 
	% first two conjuncts in order to bind the local variables in
	% the definition of Method. This is rather unfortunate.
	%
	% Again, first clause for human consumption only: provides Input
	% automatically using the current goal and hypothesis list.
applcble(Type,Method,Post,Effects) :-
    goal(Input), hyp_list(H),
    applcble(Type,H==>Input,Method,Post,Effects).
	% For the try/1 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of try/1 methodical.

applcble(Type,Input,Method,Post,Effects) :-
    var(Method),!,
    applcble_pure(Type,Input,Method,Post,Effects).

applcble(Type,Input,try(M),Post,Effects) :-
    !,
    applicable_try(Type,Input,try(M),Post,Effects).
	% For the then/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of then/2 methodical.
applcble(Type,Input,then(A,B),Post,Effects) :-
    !,applicable_then(Type,Input,then(A,B),Post,Effects).
	% For the or/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of or/2 methodical.
applcble(Type,Input,or(A,B),Post,Effects) :-
    !,applicable_or(Type,Input,or(A,B),Post,Effects).
	%
applcble(Type,Input,[M|Ms] until M2,Post,Effects) :-
    !,applicable_until(Type,Input,[M|Ms] until M2 ,Post,Effects).

applcble(Type,Input,Method,Post,Effects) :-
    applcble_pure(Type,Input,Method,Post,Effects).
applcble_pure(Type,Input,Method,Post,Effects) :-
    Input = (H==>G),
    appIndent(NewIndent),
    apply(Type,[Method,Input,Pre,Post,Effects,_Tactic]),
    plantraced(40, indentApp(NewIndent)),
    
    plantraced(30,(functor(Method,M,A),
		   (writef('--> Trying preconditions %t %t on\n',
			  [Type,M/A]), indentApp(NewIndent),
		    writef('    %t\n',[H]), indentApp(NewIndent),
		    writef('    ==>%t\n',[G])))),
    on_backtracking
	(plantraced(40,(indentApp(NewIndent), 
			writef('<<- preconditions of %t %t failed\n',
			       [Type,M/A])))),
    call_precondition(Pre),
    % check_time_limit,
    plantraced(40,(indentApp(NewIndent),
		   writef('--- preconditions of %t %t succeeded\n',
			  [Type,M/A]))),
    on_backtracking
	plantraced(40,(functor(Method,M,A), indentApp(NewIndent),
		       writef('--> Retrying preconditions %t %t on\n',
			      [Type,M/A]), indentApp(NewIndent),
		       writef('    %t\n',[H]), indentApp(NewIndent),
		       writef('    ==>%t\n',[G]))),

    (try_postconditions(Post)
      -> plantraced(40,(indentApp(NewIndent),
			writef('<-- postconditions of %t %t suceeded\n',
			       [Type,M/A])))
      ;  (functor(Method,M,A),
	  clam_warning('Postconditions of %t %t failed.\n',[Type,M/A]),
	  plantraced(40,(indentApp(NewIndent),
			 writef('<?? Postconditions failed %t %t\n',
				[Type,M/A]))),fail)).

indentApp(0).
indentApp(N) :-
    \+N = 0,
    write(' '),
    NN is N - 1,
    indentApp(NN).

incAppInd :-
    appIndent(X),
    retractall(appIndent(_)),
    NewIndent is X + 4,
    asserta(appIndent(NewIndent)).

decAppInd :-
    appIndent(Indent),
    NewIndent is Indent - 4,
    retractall(appIndent(_)),
    asserta(appIndent(NewIndent)).
decAppInd :-
    incAppInd,fail.

resetAppInd :-
    retractall(appIndent(_)),
    asserta(appIndent(0)).
 
call_precondition(L) :- call(L).

try_postconditions(L):- call(L),!.

	% applicable_anymethod/[1,2,3,4] represent the union of
	% applicable[1,2,3,4] and applicable_submethod/[1,2,3,4].
	%
	% Included more for completeness than for usefulness...
applicable_anymethod(Input,Method,Postconds,Effects) :-
    applicable(Input,Method,Postconds,Effects).
applicable_anymethod(Input,Method,Postconds,Effects) :-
    applicable_submethod(Input,Method,Postconds,Effects).

applicable_anymethod(Method,Postconds,Effects) :-
    applicable(Method,Postconds,Effects).
applicable_anymethod(Method,Postconds,Effects) :-
    applicable_submethod(Method,Postconds,Effects).

applicable_anymethod(Input,Method) :- applicable(Input,Method).
applicable_anymethod(Input,Method) :- applicable_submethod(Input,Method).

applicable_anymethod(Method) :- applicable(Method).
applicable_anymethod(Method) :- applicable_submethod(Method).


mdebug :- source_dir(F),
          concat( F, '/pp/mspy', MSPY ),
          compile(MSPY).


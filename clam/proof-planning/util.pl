/*
 * @(#)$Id: util.pl,v 1.48 2008/05/21 14:14:15 smaill Exp $
 *
 * $Log: util.pl,v $
 * Revision 1.48  2008/05/21 14:14:15  smaill
 * update for sicstus4
 *
 * Revision 1.47  2005/05/09 18:29:17  smaill
 * make timed out op fail
 *
 * Revision 1.46  2005/05/06 19:41:02  smaill
 * Use sicstus timing procedures to replace home brew
 *
 * Revision 1.45  2003/01/22 18:59:10  smaill
 * for DICE
 *
 * Revision 1.44  1999/05/19 15:59:00  julianr
 * Modified library mechanism to produce commuted variants of loaded equations
 * which involve a commutative function, and changed the timing code.
 *
 * Revision 1.43  1999/02/02 09:54:49  img
 * apply_plan/3: cosmetic change
 *
 * Revision 1.42  1998/08/26 12:35:49  img
 * needs/2 -> is_needed/2.  writef -> lib_writef where appropriated.
 *
 * Revision 1.41  1998/07/29 15:16:14  img
 * *** empty log message ***
 *
 * Revision 1.40  1998/07/27 12:15:50  img
 * unify/2 moved into Oyster source
 *
 * Revision 1.39  1998/06/10 09:40:24  img
 * *** empty log message ***
 *
 * Revision 1.38  1998/06/10 09:36:15  img
 * timed goal execution; moved object-level stuff
 *
 * Revision 1.37  1998/02/17 13:55:17  img
 * show_rule/1 added
 *
 * Revision 1.36  1998/02/11 12:40:59  img
 * erase_example fixed
 *
 * Revision 1.35  1997/11/12 15:17:39  img
 * Removed smath declaration from TeX output
 *
 * Revision 1.34  1997/11/11 17:47:07  img
 * Alteration to TeX output format
 *
 * Revision 1.33  1997/11/08 12:27:04  img
 * Dont allow failure of lib-save to upset benchmarking
 *
 * Revision 1.32  1997/10/09 14:56:35  img
 * do_all/5 added
 *
 * Revision 1.31  1997/09/26 15:03:42  img
 * delete/3-like predicated added (Quintus and SICStus versions differ);
 * call_conhunction/1 removed;  equal_modulo_meta_variable_renaming(..)
 * moved here from method_pre.pl.
 *
 * Revision 1.30  1997/07/09 15:30:12  img
 * foldr/4, foldl/4 and delete_all/3 added.
 *
 * Revision 1.29  1997/06/05 10:48:29  img
 * Extra argument on eqn/2 tag.
 *
 * Revision 1.28  1997/04/07 11:47:45  img
 * Remove some library support code that is no longer needed here;
 * check_time_limti/0: succeed if the end_time/1 is a variable;  make/0
 * and family removed since no longer useful.
 *
 * Revision 1.27  1997/01/14 10:45:43  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.26  1996/12/12 12:42:02  img
 * Error message stuff.
 *
 * Revision 1.25  1996/12/11 14:19:09  img
 * Start of a distinction between a user error and an internal error.
 *
 * Revision 1.24  1996/12/06 14:39:11  img
 * Time-out/timing support added.
 *
 * Revision 1.23  1996/12/04 13:04:00  img
 * toggle_format/1 etc: removed: replaced this functionality with
 * portray_level/3 etc.  check_time_limit/0: added: will generate an
 * exception on time-out.
 *
 * Revision 1.22  1996/07/10  08:43:11  img
 * typo
 *
 * Revision 1.21  1996/07/09 14:58:59  img
 * meta_try/1 added: same as try/1 tactical, only at meta-level.
 * Cosmetic surgury in clam_info/1.
 *
 * Revision 1.20  1996/07/03  10:37:00  img
 * print_plan/_: revert to standard printing from version 1.7
 *
 * Revision 1.19  1996/06/18  17:22:27  img
 * Bugs in benchmarking fixed.  Shows when things are skipped.  Status
 * field is now a list, so that multiple attributes can be assigned.
 *
 * Revision 1.18  1996/06/11  16:45:33  img
 * erase_object/1: delete synthesis objects too; show_rule/1 added for
 * the user.
 *
 * Revision 1.17  1996/05/24  10:03:19  img
 * erase_object/1 rewritten; erase_example/1 rewritten (removes the plan
 * object too).
 *
 * Revision 1.16  1996/05/22  09:10:53  img
 * erase_example/1: empty the registry during benchmark.
 * clam_info/2 and clam_warning/2 added.
 *
 * Revision 1.15  1995/11/28  16:16:51  img
 * operator decl. for "until" methodical;  utility for comp. sets.
 *
 * Revision 1.14  1995/10/24  14:52:09  img
 * clam_warning and clam_error added
 *
 * Revision 1.13  1995/10/18  12:15:22  img
 * ocunifiable/2 changed to matches/2;  code moved from libs.pl into
 * util.pl
 *
 * Revision 1.12  1995/10/03  13:15:52  img
 * revised benchmarking code;  utilities predicates for sets;
 * make_ground_term/2 added.
 *
 * Revision 1.11  1995/08/01  08:40:40  img
 * formatted printing of complementary_sets
 *
 * Revision 1.10  1995/05/17  02:19:22  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.9  1995/03/01  04:16:08  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.8  1995/03/01  03:45:02  img
 * 	* more detailed version of print plan for development purposes
 *
 * Revision 1.7  1995/01/31  10:56:54  dream
 * 	* added unify/2 for sound unification
 *
 * Revision 1.6  1994/09/30  14:05:25  dream
 * 	* changed all occurrences of copy/2 to copy_term/2
 *
 * Revision 1.5  1994/09/22  10:09:23  dream
 * 	* added some/2, somechk/2, maplist/[3,4,5], convlist/3;  added
 * 	  the beginings of a module header
 *
 * Revision 1.4  1994/09/20  14:18:40  dream
 * 	* fixed bug in make_ground/2: atoms were considered to be variables
 *
 * Revision 1.3  1994/09/16  10:53:46  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.2  1994/09/16  10:15:28  dream
 * 	* toggle_format/1 now toggles the correct predicates
 * 	* modified startoutputTeX/0 and stopoutputTeX/0 to correctly close
 * 	  the open trace file; write Clam version number to the trace file
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: util.pl,v 1.48 2008/05/21 14:14:15 smaill Exp $').

?- use_module(library(timeout)).

/* 
:- module(utility,[definition/1,
		   print_plan/1,
		   print_dplan/0,
		   print_idplan/0,
		   print_bplan/0,
		   trace_plan/2,
		   apply_ext/1,
		   apply_plan/0,
		   apply_plan/1,
		   apply_dplan/0,
		   apply_idplan/0,
		   apply_bplan/0,
		   apply_gdfplan/0,
		   erase_example/1,
		   lib_erase/1,
		   plan/1,
		   plan_all/1,
		   plan_all_with_normalize/0,
		   plan_all_with_normalize/1,
		   plan_all_without_normalize/1,
		   plan_from/1,
		   plan_from/2,
		   plan_to/1,
		   plan_to/2,
		   prove/1,
		   prove_all/0,
		   prove_all_with_normalize/0,
		   prove_all_with_normalize/1,
		   prove_all_without_normalize/0,
		   prove_all_without_normalize/1,
		   prove_and_save_all/0,
		   prove_and_save_all_without_normalize/1,
		   prove_and_save_all_with_normalize/1,
		   prove_from/1,
		   prove_from/2,
		   prove_to/1,
		   prove_to/2,
		   report_failures/0,
		   benchmark_plan/2,
		   some/2,
		   somechk/2,
		   maplist/3,
		   maplist/4,
		   maplist/5,
		   convlist/3]).
*/

/*
 * General utilities for the proof planner.
 * First planner-specific utilities, then more general utilities
 * Most of them too boring for comment.
 */

/*
 * All operator declarations of the whole system are done righ at top of
 * file, even though their definitions only follow later (or are
 * somewhere else alltoghether). This is to allow them to be used before
 * they are defined:
 */
:- op(1100,     xfy,    [v, orelse]).
:- op(990,      yfx,    [andpossibly]).
:- op(860,      fx,     [thereis, forall]).
:- op(850,      fx,     on_backtracking).
:- op(850,      fx,     [tryto]).
:- op(850,      fx,     [meta_try]).
:- op(825,      xfy,    [:=>]).
:- op(505,      fx,     make).
:- op(950,      xfy,    [until]).

        % following some postfix operators for the object-level logic a
        % la "list". Don't know where else to put the operator
        % declarations, so just put it here... 
:- op( 200,     xf,     [nestedlist,tree]).

        % definition(?L<==>?R) L is defined as R. First checks all local
        % definitions, then all global definitions. Almost like Jane's
        % get_definition/2, but more general, since L can be mode ?
        %
        % ALSO: works for L=F/N. This is useful since we often only
        % know the functor F of the definition, and not its arity. In
        % such a case we would end up writing in the calling code:
        %   definition(L<==>R), functorp(L,F,N)
        % which causes endless bactracking over definition/1.
        %
        % NOTE: Currently remove the code for local defs since this only costs
        % time and nobody uses them anymore. 
% definition(L<==>R) :- hypothesis(L<==>R).
definition(F/N<==>R) :-
    (var(F);atomic(F)), !,
    cdef(F) =: (L<==>R),
    (functor(L,F,N) orelse (N=0,L={F})).
definition(L<==>R) :- cdef(_) =: (L<==>R).

        % Very simple pretty-printer for plans.
        % Second argument is indentation from left margin.
        % Only the first clause is for human consumption.
        % Second clause allows printing of partial plans of the kind
        % generated by breadth-first planning (useful for debugging).
        % Third clause stripts of bogus [...]'s around single element lists.
        % Fourth clause deals with "then [....]" constructs.
        %  The trickery-pokery with the no_indent(Indent) term is to not indent
        %  the first line of the first element of the list after the "then",
        %  because that indentation is already done before printing the '['.
        % Fifth clause deals with "then" constructs without lists
        % Sixth clause deals with atomic plans
        % 
        % print_plan_list/2 just iterates print_plan over a list. Notice
        % that we don't terminate on [] but on [H], to avoid printing a ','
        % after the last element of the list.
print_plan(Plan) :- print_plan(Plan,0),nl.
print_plan(Plan,I) :- var(Plan), !, Plan='_', print_plan(Plan,I).

/* print_plan(FPlan, no_indent(I)) :-
    member(FPlan,[ripple(_,_,Plan),ripple(Plan),
		  base_case(Plan),step_case(Plan),sym_eval(Plan)]),!,
    FPlan =.. [F|_],
    print(F),write('('),nl,
    J is I + 2,
    print_plan(Plan,J),write(')').
print_plan(FPlan, I) :-
    \+I= no_indent(_),
    member(FPlan,[ripple(_,_,Plan),ripple(Plan),
		  base_case(Plan),step_case(Plan),sym_eval(Plan)]),!,
    FPlan =.. [F|_],
  print_plan(F,I),write('('),nl,
  J is I + 2,
  print_plan(Plan,J),write(')'). */
      

print_plan(P1 then Var, I) :- var(Var), !, print_plan(P1,I).
print_plan(P1 then [P2],I) :- !,print_plan(P1 then P2,I).
print_plan(P1 then [P2|P2s],I) :- !,
    print_plan(P1,I), (I=no_indent(II) orelse I=II),
    write(' then '), nl, J is II+2+1, tab(J-1),write('['),
    print_plan(P2,no_indent(J)), write(','),nl,
    print_plan_list(P2s,J), tab(J-1),write(']').
print_plan(P1 then P2,I) :- !,
    print_plan(P1,I), (I=no_indent(II) orelse I=II),
    write(' then '), nl,
    J is II+2, print_plan(P2,J).
print_plan(P,no_indent(_)) :- !,print(P).       % use print/1 to allow user
print_plan(P,I) :- !,tab(I), print(P).          % to portray.
print_plan_list([H],I) :- !, print_plan(H,I),nl.
print_plan_list([H|T],I) :-
    print_plan(H,I), write(','), nl, print_plan_list(T,I).

        % print_plan/0 prints the plan of the current proof tree under
        % the current node.
print_plan :- get_plan(P), print_plan(P).
get_plan(R then Rs) :- refinement(R), findall(R1, (down,get_plan(R1)),
Rs), Rs\=[],!.
get_plan(R) :- refinement(R).

        % print_dplan/0 prints the last plan constructed using dplan
        % print_idplan/0 prints the last plan constructed using dplan
        % print_bplan/0 prints the last plan constructed using dplan
print_dplan :- dplan=:P, print_plan(P).
print_idplan :- idplan=:P, print_plan(P).
print_bplan :- bplan=:P, print_plan(P).


print_nllist(L) :- print_nllist(L,0,'|').
print_nllist([],_,_).
print_nllist([H|T],C,Ch) :-
    writef('%r%t\n',[Ch,C,H]),
    print_nllist(T,C,Ch).

        % Simple utility for use in debugging tools etc.
        % Heavily relying on Oyster pretty-printing predicates.
print_seq(H==>G) :- write_hyp(0,1,_,H),write('==> '), writeterm(3,G).

        % Rudiments of a tracer for planners. A global tracing level is
        % set. Level 0 means no tracing. Higher numbers mean more and
        % more tracing.
        % - trace_plan(?Old,?New) inquires for current or sets new
        %   tracing level. 
        % - plantraced(+N,+Pred) execute Pred if current level >N
        %   (notice that plantraced never fails, so as not to interfere
        %    with embedding code).
trace_plan(Old,New) :- 
    \+ ((var(Old);integer(Old)),(var(New);integer(New))),
    writef('CLaM ERROR: Arguments must be integers or variables\n'),!,fail.
trace_plan(Old,New) :-
    var(Old),!,
    (recorded(plantrace,plantrace(Old),_) orelse Old=0),
    trace_plan(Old,New).
trace_plan(Old,New) :-
    var(New),!,
    (recorded(plantrace,plantrace(Old),_) orelse Old=0),
    New=Old.
trace_plan(Old,New) :-
    (recorded(plantrace,plantrace(Old),_) orelse Old=0),
    (Old=New
     orelse
     ((Old=0->OldOff=' (off)';OldOff=''),(New=0->NewOff=' (off)';NewOff=''),
      writef('[The plantracer switched from level %t%t to level %t%t]\n',
             [Old,OldOff,New,NewOff]),
      uniq_recorda(plantrace,plantrace(New),_))
    ).
plantraced(N,Pred) :- \+var(N),trace_plan(M,M),M>=N,call(Pred),!.
plantraced(_,_).

        % apply_ext(+Args) applies the extract from the current theorem
        % to the argument list Args.

apply_ext(Args) :-
     extract(E),
     \+ var(E),
     apply_ext(E,Args,Ans & _),
     pnat2natlist(Ans,NAns),
     cthm=:Thm,
     writef('(%t ',[Thm]),
     print_args(Args),
     writef('%t\n',[NAns]).

print_args([]):- write(') = ').
print_args([H|T]) :-
    writef(' %t',[H]),
    print_args(T).

apply_ext(E,[],E).
apply_ext(E,[Arg|Args],Ans):-
        integer(Arg),
        nat2pnat(Arg,NArg),
        eval(E of NArg,EE),
        apply_ext(EE,Args,Ans).
apply_ext(E,[Arg|Args],Ans):-
        pnat2natlist(NArg,Arg),
        eval(E of NArg,EE),
        apply_ext(EE,Args,Ans).

nat2pnat(0,0).
nat2pnat(N,s(M)) :- NN is N-1, nat2pnat(NN,M).
pnat2nat(0,0).
pnat2nat(s(X),M) :- pnat2nat(X,MM),M is MM+1.
pnat2natlist(nil,[]).
pnat2natlist(H::T,[HH|TT]) :- pnat2nat(H,HH),pnat2natlist(T,TT).

        % apply_plan(+P) executes plan P. If every method has a tactic
        % which is defined as a Prolog procedure, then the constructed
        % plans could be fed to the Oyster apply/1 predicate for
        % execution. However, if this is not the case, or if we don't
        % want the collapsed proof tree, with the plan as a single
        % refinement, than we can use this apply_plan/1 predicate.
        % apply_check_plan/1 is as apply_plan/1, but also has built-in
        % error-checking: it checks if 
        % the goal resulting from applying the tactic is indeed the goal
        % that the method specified. This is expensive (since it means
        % computing the Effects of a method), but worth while during
        % development stage. We also catch application-failure.
        %
        % apply_[..]plan picks up the plan from the global variable [..]plan
        % and executes it.
apply_dplan :- dplan=:P, apply_plan(P).
apply_idplan :- idplan=:P, apply_plan(P).
apply_bplan :- bplan=:P, apply_plan(P).
apply_gdfplan :- gdfplan=:P, apply_plan(P).
apply_plan :- dplan=:P, apply_plan(P).
apply_plan(P) :- var(P), !, fail.
apply_plan(P) :- apply_plan(P,nocheck,0).
apply_plan_check(P) :- apply_plan(P,check,0).
apply_plan(P then [P1|Ps],Check,D) :- 
    plantraced(1,writef('applying tactic at depth %t: %t\n',[D,P])),
    (method(P,_,_,_,_,T)->true),
    apply(T), !,
    (Check=nocheck
     orelse
     (applicable(P,_,Effects),
      map_list(Effects,(_==>E):=>EE,wave_fronts(EE,_,E),Es),
      % findall(E, (member(_==>E1,Effects),wave_fronts(E,_,E1)),Es),
      findall(G,(down,goal(G)),Gs),!,
      (Gs\=Es
      -> (pos(Pos),
          writef('CLaM ERROR: Error at position %t:\n', [Pos]),
          writef('method %t gives unexpected results:\n',[P]),
          writef('Expected results are: '), nl, prlist(Es),
          writef('Actual  results  are: '), nl, prlist(Gs), fail)
      ; true
      )
     )
    ),
    D1 is D+1,
    apply_plan_list([P1|Ps],1,Check,D1),!.
apply_plan(P,_,D) :- \+ functorp(P,then,2),
    plantraced(1,writef('applying tactic at depth %t: %t\n',[D,P])),
    (method(P,_,_,_,_,T)->true),
    apply(T), !.
apply_plan(PP,_,_) :-
    (functorp(PP,then,2) -> PP = (P then _) ; P=PP),
    pos(Pos),
    writef('Error at position %t:\n', [Pos]),
    writef('tactic %t failed to apply.\n',[P]),
    !,fail.
apply_plan_list([P1|Ps],N,Check,D) :- !,
    down(N), apply_plan(P1,Check,D), !, up, M is N+1, !,
    apply_plan_list(Ps,M,Check,D),!.
apply_plan_list([],_,_,_) :- !.

	% erase_example/1 deletes all objects which the
	% theorem Thm depends upon (the registry is untouched).
erase_example(Thm) :-
    erase_object(thm(Thm)).
erase_object(LO) :-
    LO =.. [Type,T],
    is_needed(LO,Dep),
    /* some objects depend on others; deleting such objects does not
	always delete the objects on which they depend--- so do it
	explicitly */  
    once(member(Type-Extra,[wave-thm(T),red-thm(T),_-[]])),
    erase_object_(Dep),
    if(lib_present(LO),lib_delete(LO)),
    if(lib_present(Extra),lib_delete(Extra)),!.
erase_object_([]).
erase_object_([O|Os]) :-
    erase_object(O),
    erase_object_(Os).

/* Fetch the plan P of theorem T */
proof_plan(T,P) :-
    recorded(proof_plan,proof_plan(_,T,_,P,_),_).    
plan(Thm):-
    lib_load(thm(Thm)),
    slct(Thm),
    dplan.
prove(Thm):-
    lib_load(thm(Thm)),
    slct(Thm),
    dplan,
    apply_plan.

plan_all :- plan_all(dplan).
plan_all(Planner) :-
    do_all(Planner,noapply, 1). 
prove_all :- prove_all(dplan).
prove_all(Planner) :-
    do_all(Planner,apply, 1). 

plan_from(F) :- plan_from(dplan,F).
plan_from(Planner,First) :-
    do_all(Planner,noapply, 1,_Type, First,_). 
plan_to(L) :- plan_to(dplan,L).
plan_to(Planner,Last) :-
    do_all(Planner,noapply, 1,_Type, _,Last). 
prove_from(F) :- prove_from(dplan,F).
prove_from(Planner,First) :-
    do_all(Planner,apply, 1,_Type, First,_). 
prove_to(L) :- prove_to(dplan,L).
prove_to(Planner,Last) :-
    do_all(Planner,apply, 1,_Type, _,Last). 

plan_all_without_normalize :- plan_all_without_normalize(dplan).
plan_all_without_normalize(Planner) :-
    do_all_without_normalize(Planner,noapply, 3). 

prove_all_without_normalize :- prove_all_without_normalize(dplan).
prove_all_without_normalize(Planner) :-
    do_all(Planner,apply, 3). 

do_all(Planner,Apply, N) :-			% default to start and last
    do_all(Planner,Apply, N, _Type, _First, _Last). 

/* run Planner on examples of Type, using induction plan number N */
do_all(Planner,Apply, N, Type, First, Last):-
    load_ind_plan(N),
    lib_dir(Path),
    lib_fname_exists(Path,'examples.pl',File),
    consult(File),
	     %% If the theorem requires normalization
             %% normalization methods are not loaded, skip
    do_all(Planner,Apply, Type, First, Last).
do_all(Planner,Apply, Type, First, Last) :-
    findall(Thm,example(_,Thm,_),AllThms),
    %% let's not assume much about append wrt First and Last
    (var(First) -> AllThms = [First|Rest]; 
     append(_,[First|Rest],AllThms)),		% drop early ones
    (var(Last) -> Thms = [First|Rest];
     (append(Start,[Last|_],[First|Rest]),	% drop late ones
      append(Start,[Last],Thms))),		% Last is included
    !,						% cut First and Last
    findall(T, 
	    (member(T,Thms),
	     example(Type,T,Status),
	     ((member(skip,Status) orelse
		   (member(needs_normalize,Status),
		    \+ lib_present(mthd(normalize/_))))
		  -> (writef('[Skipping benchmark on %t.]\n',[T]),fail)
	       ;  true)),ToDo),
    benchmark_plan(Planner,ToDo,Apply).

prove_and_save_all:-
    do_all(dplan,save,1),			% normalize
    do_all(dplan,save,3).			% no normalize

report_failures :- 
    failure(plan,Thm),
    writef('Planning for %t failed.\n', [Thm] ),
    fail.
report_failures :- 
    failure(proof,Thm),
    writef('Tactic execution for %t failed.\n', [Thm] ),
    fail.
report_failures.

/* benchmark_plan(+Planner,+ListofThms) generates plans for all Thms
 * using Planner.
 *  - If ListofThms is a list of theorem, generates plans for all
 *    theorems specified in the list
 *  - If ListofThms is the atom 'needs', we take all theorems
 *    specified as thm(_) in the needs/2 database.
 *  - If ListofThms is any other atom, it is taken to be a
 *    directory, and Planner is run on all previously proven
 *    theorems in files *.thm in that directory.
 *
 * benchmark_plan_apply/2 is as benchmark_plan/2, but also applies the
 * plan.
 * 
 * - First map all apply/non-apply cases into benchmark_plan/3.
 * - If ListofThms is 'needs', then find all thm(_)'s from the
 *   needs/2 database and try again.
 * - If ListofThms is any other atom, then find all *.thm files
 *   in Dir and try again.
 * - If theorem spec is (Dir,Thm), run benchmark and recurse.  
 * - If theorem spec is just Thm, take Dir to be lib_dir/1, then run
 *   benchmark and recurse. 
 * 
 * To do a single benchmark, first clean out database (dubious, but
 * otherwise things get horribly clogged up), then lib_load Thm from
 * Dir, select theorem, check if indeed provable, run planner, report
 * result, and possibly apply plan.
 */
benchmark_plan(_,[],_) :-
    !, writef('Benchmark completed.\n',[]).
benchmark_plan(Planner,needs,Apply) :- !,
    findall(Thm,(is_needed(thm(Thm),_),nonvar(Thm)),Thms),
    benchmark_plan(Planner,Thms,Apply).
benchmark_plan(Planner,needs(Name),Apply) :- !,
    findall(Thm,(is_needed(thm(Thm),_),nonvar(Thm)),Thms),
    append( _, [Name|RThms], Thms ),
    benchmark_plan(Planner,RThms,Apply).
benchmark_plan(Planner,[(Dir,Thm)|Thms],Apply) :- !,
    do_one_benchmark(Planner,Thm,Dir,Apply),
    benchmark_plan(Planner,Thms,Apply).
benchmark_plan(Planner,Thms,Apply) :-
    % We use a failure driven loop here to avoid building up a gigantic stack in
    % long benchmark runs on non-smart Prolog's.
    member( Thm, Thms ),
    ( atom(Thm), Thm1 = Thm, lib_dir(Dir) ;
      ( Thm1, Dir ) = Thm
    ),
    writef('Benchmarking thm(%t)\n',[Thm]),
    do_one_benchmark(Planner,Thm1,Dir,Apply),
    once((erase_example(Thm1),
    lib_delete_aux(and,1),
    lib_delete_aux(or,1),
    lib_delete_aux(imp,1),
    lib_delete_aux(iff,1),
    lib_delete_aux(equality,1),
    lib_delete(trs(default)),
    load_default_env)),
    fail.
benchmark_plan(_,_,_).   
benchmark_plan_apply(Planner,Thms) :- benchmark_plan(Planner,Thms,apply).

:- dynamic success/2.
:- dynamic failure/2.
:- dynamic complete_because/2.

do_one_benchmark(Planner,Thm,Path,Apply) :-
    lib_load(thm(Thm),Path),
    slct(Thm),
    ( status(complete) ;
      lib_writef(23,'Saved thm for %t incomplete.\n',[Thm])
    ),
    Planner =.. [PlannerName|Args],		%may be some args
    append(Args,[Plan],FullArgs),
    Command =.. [PlannerName|FullArgs],
    /* empty the cached wave-rules */
    empty_wave_rule_cache,
    !,
    ( call(Command) 
        -> ( writef('\nPLANNING for %t COMPLETE.\n', [Thm] ),
             print_plan(Plan),
	     lib_sdir(SDir),
	     meta_try lib_save(plan(Thm),SDir),	% may fail due to filespace problem
	     assert(success(plan,Thm)),!,
             ( (Apply=apply;Apply=save)
               -> ( apply_plan(Plan) ->
                    ((status(complete)
                      ->  (writef('PROOF for %t COMPLETE.\n', [Thm]),
			   assert(success(proof,Thm)),
                           (Apply=save 
                            -> meta_try lib_save(thm(Thm),SDir) % saves thm in buffer area
                            ; true 
                           ));
                      (status(complete(because))
                        -> (writef('PROOF for %t COMPLETE(because).\n', [Thm]),
                            assert(complete_because(proof,Thm)),
                            (Apply=save
                            -> meta_try lib_save(thm(Thm),SDir) % saves thm in buffer area
                            ; true
                           ));
                        (status(partial)
                         -> (writef('PROOF for %t PARTIAL.\n', [Thm]),
                             assert(partial(proof,Thm)),
                             (Apply=save
                              -> meta_try lib_save(thm(Thm),SDir) %saves thm in buffer area
                            ; true
                           ))
                      ; writef(
                         'Benchmark failed while executing plan on %t.\n',[Thm]),
		        assert(failure(proof,Thm))
                     ))));
		    writef('Tactic failure for %t.\n',[Thm])) ; nl))
        ; writef('Benchmark failed while constructing plan on %t.\n', [Thm]),
	  assert(failure(plan,Thm))
     ), !.


/* quantify(?TypedVarList,?T1,?T2): T2 is the same as T1, exept that
 * it is wrapped with universal quantifications of the variables
 * mentioned in TypedVarList (a list with elements Var:Type).  Due to
 * generous mode, this can be used both to quantify T1 and to
 * dequantify T2. Notice that T2 can also be partially
 * dequantified. For full dequantification, use matrix/3.  */
quantify([],T1,T1).
quantify([V:T|VsTs],T1,V:T=>T2) :- quantify(VsTs,T1, T2).

/* untype(?ListofTypedVars, ?ListofVars, ?ListofTypes) strips the
 * types of a list of variables, and collects the types and the vars
 * in separate lists.  untype(?ListofTypedVars, ?ListofVars) is as
 * untype/3 but does not return the ListofTypes.  Maintained only for
 * backward compatibility.  */
untype(Vars,Vs) :- untype(Vars,Vs,_).
untype([],[],[]).
untype([V:T|VsTs],[V|Vs],[T|Ts]) :- untype(VsTs,Vs,Ts).

/* decolon_preconds(?PreConds, ?DeCPreCOnds) turns each element of
 * PreConds Var:Term into Wit-Term and leaves the rest unchanged.
 * This mind-pummelingly useful when you want to replace variables a
 * list of pre-conditions for a lemma, a replace_universal_vars (etc)
 * will not touch V in terms of the form V:T.  */
decolon_preconds( [(A:B)|R], [A-B|DR] ) :-
     !,
     decolon_preconds(R,DR).
decolon_preconds( [H|R], [H|DR] ) :-
     decolon_preconds(R,DR).
decolon_preconds( [], [] ).

/* make_ground(+Term) succeeds when Term is ground. If Term is not
 * ground it will be made so by unifying all Prolog variables in it
 * with atomic terms of the form v0,v1,... We make sure that these
 * newly provided terms do not already appear in Term.  First clause
 * checks if Term is already ground. Second clause collects all atomic
 * sub-terms of Term, which are used by ground/2 to check while
 * traversing Term that newly provided vars do not already occur.
 * make_ground/2 is as above, and additionally returns the variables
 * v0, v1,...  which are used to ground Term (img) */
make_ground(Term) :-
    ground(Term),!.
make_ground(Term) :-
    findall(Atom,(exp_at(Term,[P1|_],Atom),P1\=0,atomic(Atom)),Atoms),
    ground(Term,Atoms).
make_ground(Term,Vars) :-
    findall(Atom,(exp_at(Term,[P1|_],Atom),P1\=0,atomic(Atom)),Atoms),
    ground(Term,Atoms,[],Vars).			%keep Vars and Atoms separate! (img)

make_ground_term(Term,Term2) :-
    findall(Atom,(exp_at(Term2,[P1|_],Atom),P1\=0,atomic(Atom)),Atoms),
    ground(Term,Atoms).

ground(Term,_Atoms,Vars,Vars) :-		%forth argument for result (img)
    ground(Term),!.
ground(Term,Atoms,Vars,VarsFinal) :-
    exp_at(Term,_,Var), var(Var),
    genvar(Var),
    \+ member(Var,Vars),			%dont reproduce variables or atoms (img)
    \+ member(Var,Atoms), !,
    ground(Term,Atoms,[Var|Vars],VarsFinal).

ground(Term,_) :-
    ground(Term),!.
ground(Term,Atoms) :-
    exp_at(Term,_,Var), var(Var),
    genvar(Var),\+ member(Var,Atoms), !,
    ground(Term,[Var|Atoms]).

        % Find out run-time of a predicate.
runtime(P,T) :- statistics(runtime,_), call(P), statistics(runtime,[_,T]).
        % Take average T of run-time of a predicate P over N number of runs.
runtime(P,N,T) :- runtime1(P,N,Ts), write(Ts),nl,average(Ts,T),!.
runtime1(_,0,[]).
runtime1(P,N,[T1|Ts]) :-
    N>0, copy_term(P,P1),runtime(P1,T1), N1 is N-1, runtime1(P,N1,Ts).

        % sum(+NumList,?Sum): Sum is the sum of the elements in NumList.
sum([], 0).
sum([N|Ns], S) :- sum(Ns, T), S is T+N.

        % average(+NumList,?Average): Average is the average of the
        % elements in NumList.
average(L,A) :- sum(L,S), length(L,N), A is S/N.

        % partition_c(?List, ?N, ?PreN, ?Nth, ?PostN): splits List up in 3 parts:
        % elements 0 to N-1, the Nth element, and elements N+1 to end.
        % Fail if N>=length(List).
        % Notice that all arguments can be uninstantiated (at the cost
        % of tail-recursion....who said more "declarative" algorithms are
        % also more efficient? Richard O'Keefe, where are you when we
        % could prove you wrong?)
partition_c([H|T], 0, [], H, T).
partition_c([H|T], N, [H|Pre], Nth, Post) :-
    partition_c(T, M, Pre, Nth, Post),
    N is M+1.

        % remove_pred(Spec) and remove_pred(Name,Arity) are exactly as
        % abolish/[1;2]. This is mainly to allow us to redefine this
        % under SICStus to shut up SICStus abolish/[1;2] spurious messages
        % (sigh...)
%remove_pred(Spec) :- \+ dialect(sic), !, abolish(Spec).
%remove_pred([]) :- !.
%remove_pred([H|T]) :- !, remove_pred(H), remove_pred(T).
%remove_pred(P/A) :- current_predicate(P,F),functor(F,P,A),!,abolish(P,A).
%remove_pred(P) :- atom(P), current_predicate(P,_),!,abolish(P),fail.
%remove_pred(_).
%remove_pred(Name,Arity) :- \+ dialect(sic), !, abolish(Name,Arity).
%remove_pred(Name,A) :- remove_pred(Name/A).

% sicstus4 does this better (I hope)

remove_pred(Spec) :- abolish(Spec).
remove_pred(Name,A) :- remove_pred(Name/A).

        % skeleton(+Term,?Skeleton) Skeleton is a term of same functor
        % and arity as Term, but with all Terms arguments replaced by
        % unique Prolog variables.
skeleton(Term,Skeleton) :- functor(Term,F,N),functor(Skeleton,F,N).

        % Coded slightly weird to allow bi-directional use:
list2conj([H,Ht|T],(H,T1)) :- !,list2conj([Ht|T],T1).
list2conj([H],H).

        % tryto +G: will try to perform G but will succeed anyway if G
        % fails. Can be used to backtrack through all solutions for G
        % and succeed at the end anyway.
tryto G :- G.
tryto _.

% like try/1 in Oyster, but for Clam
meta_try G :- G,!.
meta_try _.

        % on_backtracking +G will not do anything on first execution,
        % but will execute G on backtracking, and then fail (thereby not
        % affecting the behaviour of the calling program).
on_backtracking _.
on_backtracking G :- G, !, fail.


        % Simple routine for yes/no (y/n) prompting. Only gets activated
        % if trace-level is high enough (>=N).
        % Second clause is to force success when tracing level is too low.
yn(N,Prompt) :-
    trace_plan(M,M), M>=N, !,
    print(Prompt), writef('%f'),
    get(121), get0(_). % 121 = y and read away <cr>
yn(_,_).

        % max(+List,?Max) Max is maximum element of List. uses general
        % ordering on terms for comparing elements.
        % min(+List,?Min) similar for minimum.
max([H|T],M) :- max(T,H,M).
max([],S,S).
max([H|T],S,M) :- H@>S,  max(T,H,M).
max([H|T],S,M) :- H@=<S, max(T,S,M).

min([H|T],M) :- min(T,H,M).
min([],S,S).
min([H|T],S,M) :- H@<S,  min(T,H,M).
min([H|T],S,M) :- H@>=S, min(T,S,M).

genarg(1, Term, Arg, 1) :- !,
	arg(1, Term, Arg).
genarg(N, Term, Arg, N) :-
	arg(N, Term, Arg).
genarg(K, Term, Arg, N) :-
	K > 1, J is K-1,
	genarg(J, Term, Arg, N).

        % genint(?N,+Delta), generates integers N with interval Delta.
        % This is a generalisation of genint/1 from Oyster which fixes
        % Delta=1. 
genint(0,_).
genint(N,Delta) :- genint(M,Delta), N is M+Delta.

/* equal and of the same size */
set_equal(A,B) :-
    set_equal_(A,B),!.
set_equal_([],[]).
set_equal_([T1|IT1],IT2) :-
    select(T1,IT2,IT2rest),
    set_equal_(IT1,IT2rest).
    
/* lists of same length */
lengtheq([],[]).
lengtheq([_|A],[_|B]) :-
    lengtheq(A,B).
lengtheq([],[],[]).
lengtheq([_|A],[_|B],[_|C]) :-
    lengtheq(A,B,C).

count_member([],_,0).
count_member([H|T],HH,N) :-
    \+ \+ (H=HH),!,
    count_member(T,HH,M),
    N is M + 1.
count_member([_|T],HH,N) :-
    count_member(T,HH,N).

sum_of_list([],0).
sum_of_list([L|Ls],N) :-
    sum_of_list(Ls,M),
    N is M + L.

member_id(X,[XX|_]) :-
    X == XX.
member_id(X,[_|XXs]) :-
    member_id(X,XXs).

/* A does not contain duplicates */
no_duplicates([]).
no_duplicates([A|As]) :-
    \+ member(A,As),
    no_duplicates(As).

        % zip(?Pairs,?L1,?L2) Pairs is a list consisting of pairs of
        % elements from L1 and L2. L1 and L2 must be of equal length.
        % Can of course be used for zipping as well as unzipping to
        % lists. 
zip([],[],[]).
zip([H1-H2|Ps],[H1|T1],[H2|T2]) :- zip(Ps,T1,T2).

        % functorp(+Term,?F,?A) Term has functor F of arity A.
        % The difference between this and the built-in functor/3 is that
        % Term has to be given. In other words, this can only be used to
        % >*test*< if Term is F/A, and not to >*construct*< a term of F/A.
functorp(Term,_,_) :- var(Term),!,fail.
functorp(Term,Functor,Arity) :- functor(Term,Functor,Arity).

/*
 * Follow a couple of random predicates making live with Oyster a bit
 * more bearable:
 */

        % d/0 is a compacter version of display/0. Only shows goals of
        % current node and children, plus status of children. Forgets
        % about hyps.
d :- goal, fail.
d :- write('by '),refinement, fail.
d :- down, status, goal, fail.
d.

        % snap/{0,1} are compacter versions of snapshot/{0,1}. They
        % print the proof under the current node (as snapshot/{0,1}),
        % but only print goals and refinements, and don't mention
        % hypotheses (unlike snapshot/{0,1}). This makes for a better
        % overview of the proof tree. 
snap :- snap(user).
snap(File) :- tell_on_file(File), snap(File,0), told.
snap(File,I) :-
    tab(I), goal,
    tab(I), write('by '), refinement,
    I1 is I+4,
    down, snap(File,I1), fail.
snap(_,_).

        % search(Pred) does a depth first search for the first node
        % below the current one where Pred is true.
search(Pred) :- call(Pred).
search(Pred) :- down, search(Pred).

/* 
 * extenstions to provide LaTeX output while tracing plans
 * first argument is one of:
 *   pre            prints sequent and DEPTH
 *   postTermSubs   termination case, with substitutions
 *   postTerm       termination case, no substitutions
 *   selection[Subs]      selection of new method (w and w/o subs)
 *   failure        plan failure
 *
 * second argument is a tuple of things needed
 */
:- dynamic texoutput/1.
texoutput(no).					% no TeX is default

startoutputTeX :- 
    if(texoutput(yes),stopoutputTeX),
    retractall(texoutput(_)),
    asserta(texoutput(yes)),
    push_portray_type(tex),
    clam_version(Version),
    fwritef('clamtrace.tex',                    %implicit tell here
            '\documentclass{article}\n\\usepackage{clamtrace,dream}\n\\begin{document}\n',[]),
    fwritef('clamtrace.tex',
            '% TeX proof-plan trace (Clam version %t)\n',[Version]).
stopoutputTeX :-
    \+ texoutput(no),
    retractall(texoutput(_)),asserta(texoutput(no)),
    pop_portray_type,
    fwritef('clamtrace.tex','\\end{document}\n',[]),
    tell('clamtrace.tex'),                      %fwritef leaves it open
    told.                                       %close it

/* 
 * This is a cleaned up version of the code to print nodes
 * in the search space.
 *
 * print trace information twice in the case of TeX o/p:
 * once to a file and the second as usual to the terminal.
 * since portray is a hook, it is necessary (easier) to temporarily
 * toggle the texoutput flag for the latter to prevent TeXease on the 
 * terminal. 
 * In case of no TeX o/p, just go a regular o/p
 */
print_planning_info(Type,Args) :-
    texoutput(yes),
    print_planning_info_TeX(Type,Args),
    pop_portray_type,
    print_planning_info_noTeX(Type,Args),
    push_portray_type(tex).
print_planning_info(Type,Args) :-
    texoutput(no),
    print_planning_info_noTeX(Type,Args).  

%print_planning_info_TeX(boundinc,tuple(Bound)) :-
%    plantraced(10,fwritef('clamtrace.tex',
%      '\mbox{\\tt Increased max depth to %t}\\\\[15pt]\n',[Bound])).

%print_planning_info_TeX(pre,tuple(D,H,G)) :-
%    plantraced(22, (fwritef('clamtrace.tex',
%      '\mbox{\\tt %rDEPTH: %t}\\\\\n', ['|',D,D] ) ,
%      print_nllist_TeX(H,D,'|'),
%      fwritef('clamtrace.tex','$\mbox{\\tt %r}\vdash %t$\\\\\n',['|',D,G]) ) ).
%print_planning_info_TeX(postTermSubs,tuple(D,Method)) :-
%    plantraced(20,
%    fwritef('clamtrace.tex',
%      '$\mbox{\\tt %rTERMINATING METHOD (with Subs) at depth %t: }%t$\\\\[10pt]\n',
%           ['|',D,D,Method])).
%print_planning_info_TeX(postTerm,tuple(D,Method)) :-
%    plantraced(20,
%    fwritef('clamtrace.tex',
%    '$\mbox{\\tt %rTERMINATING METHOD at depth %t: }%t$\\\\[10pt]\n',
%    ['|',D,D,Method])).
%print_planning_info_TeX(selectionSubs,tuple(D,Method)) :-
%    plantraced(20,
%      fwritef('clamtrace.tex','$\mbox{\\tt %rSELECTED METHOD (with subs) at depth %t: }%t$\\\\\n',['|',
%         D,D,Method])).

%print_planning_info_TeX(selection,tuple(D,Method)) :-
%    plantraced(20,
%      fwritef('clamtrace.tex','$\mbox{\\tt %rSELECTED METHOD at depth %t: }%t$\\\\\n',['|',
%         D,D,Method])).
%print_planning_info_TeX(failure,tuple(D)) :-
%    plantraced(20, fwritef('clamtrace.tex','$\mbox{\\tt %rFAILED at depth %t}$\\\\[10pt]\n', ['|',D,D]) ).

%print_nllist_TeX(L) :- print_nllist_TeX(L,0,'|').
%print_nllist_TeX([],_,_).
%print_nllist_TeX([H|T],C,Ch) :-
%    fwritef('clamtrace.tex','$\mbox{\\tt %r}%t$\\\\\n',[Ch,C,H]),
%    print_nllist_TeX(T,C,Ch).

/* normal code for non-TeX case */
print_planning_info_noTeX(boundinc,tuple(Bound)) :-
    plantraced(10,writef('Increased max depth to %t\n',[Bound])).

print_planning_info_noTeX(pre,tuple(D,H,G)) :-
    plantraced(22, (writef('%rDEPTH: %t\n', ['|',D,D] ) ,
                    print_nllist(H,D,'|'),
                    writef('%r==>%t\n',['|',D,G]) ) ).
print_planning_info_noTeX(postTermSubs,tuple(D,Method)) :-
    plantraced(20,
    writef('%rTERMINATING METHOD (with Subs) at depth %t: %t\n',['|',
         D,D,Method])).
print_planning_info_noTeX(postTerm,tuple(D,Method)) :-
    plantraced(20,
    writef('%rTERMINATING METHOD at depth %t: %t\n',['|',
       D,D,Method])).
print_planning_info_noTeX(selectionSubs,tuple(D,Method)) :-
    plantraced(20,
      writef('%rSELECTED METHOD (with subs) at depth %t: %t\n',['|',
         D,D,Method])).

print_planning_info_noTeX(selection,tuple(D,Method)) :-
    plantraced(20,
      writef('%rSELECTED METHOD at depth %t: %t\n',['|',
         D,D,Method])).
print_planning_info_noTeX(failure,tuple(D)) :-
    plantraced(20, writef('%rFAILED at depth %t\n', ['|',D,D]) ).

/*
 * this is only supported in X11 version (see xutil.pl)
 */
write_colour_wave_rule(_,_).

/*
 * Some utilities from various libraries
 */

%somechk(Pred, [X|_]) :-
%        call(Pred, X), !.
%somechk(Pred, [_|Xs]) :-
%        somechk(Pred, Xs).

%some(Pred, [X|_]) :-
%        call(Pred, X).
%some(Pred, [_|Xs]) :-
%        some(Pred, Xs).
%convlist(Pred, Olds, News) :-
%        conv_list_(Olds, News, Pred).
%conv_list_([], [], _).
%conv_list_([Old|Olds], NewList, Pred) :-
%        call(Pred, Old, New),
%        !,
%        NewList = [New|News],
%        conv_list_(Olds, News, Pred).
%conv_list_([_|Olds], News, Pred) :-
%        conv_list_(Olds, News, Pred).

/* Y can be instantiated to X with a non-cyclic substitution */
matches(X, Y) :-
     \+ \+ (numbervars(X,0,_), X=Y).

unifiable(X,Y) :-
    \+ \+ unify(X,Y).

show_complementary_sets(Thms) :-
    recorded(comp_set,comp_set(Thms,C),_),
    print_complementary_sets(C).

print_complementary_sets(C) :-
    \+ \+ (numbervars(C,1,_), 
	  print_complementary_sets_(C)).
print_complementary_sets_([]).
print_complementary_sets_([Cs-LHS | Rest]) :-    
    print_complementary_sets_(Cs,LHS),nl,
    print_complementary_sets_(Rest).
print_complementary_sets_([],_LHS).
print_complementary_sets_([C-RHS-imp(_)-Rule|Cs],LHS) :-
    writef("(%t)\t%t -> %t => %t\\n",[Rule,C,LHS,RHS]),
    print_complementary_sets_(Cs,LHS).
print_complementary_sets_([C-RHS-equ(_,_)-Rule|Cs],LHS) :-
    writef("(%t)\t%t -> %t = %t\\n",[Rule,C,LHS,RHS]),
    print_complementary_sets_(Cs,LHS).

show_rule(def(D)) :-
    /* show all the eqns derived from D */
    reduction_rule(L,R,C,Dir,D,Thm,_),
    show_rule([Thm,Dir,C,L,R]).    

show_rule([Thm,TypeDir,C,Left,Right]) :-
    copy_term([Thm,TypeDir,C,Left,Right],[T,TD,Cc,L,R]),
    numbervars([T,TD,Cc,L,R],1,_),
    writef('%t/%t: %t => %t :=> %t\n', [T,TD,Cc,L,R]).

clam_warning(M) :-
    writef('Clam WARNING: %t\n',[M]).
clam_warning(M,A) :-
    write('Clam WARNING: '),
    writef(M,A).
clam_info(M,A) :-
    write('Clam INFO: '),
    writef(M,A).

/* intercept this with a debugger! */
clam_error(M) :-
    writef('Clam ERROR: %t\n',[M]),    
    gracefull_abort.
clam_error(M,A) :-
    nl,write('Clam ERROR: '),
    writef(M,A),    
    gracefull_abort.

clam_internal_error(M,A) :-
    nl,
    write('Clam INTERNAL ERROR (please report): '),
    writef(M,A),nl,
    gracefull_abort.
clam_internal_error(M) :-
    writef('\nClam INTERNAL ERROR (please report): %t\n',[M]),
    gracefull_abort.
clam_user_error(M,A) :-
    write('User ERROR: '),
    writef(M,A).

% use sicstus timeout routine
%?- recorded(timeoutvalue,_,Ref),erase(Ref), fail ; 
%   recorded(exception_label,_,Ref1), erase(Ref1) ;
%   true.

%?- recorda(exception_label,exception_label(0),_).

% Set a new timeout, Secs seconds into the future. The new timeout is
% labelled with the current exception label, which is subsequently
% incremented.
%
%timeout_in(Secs,NewTimerVal,E1) :-
%	recorded(exception_label,exception_label(E),Ref),
%	erase(Ref),
%	E1 is E+1,
%	recorda(exception_label,exception_label(E1),_),
%	statistics(runtime,[CurrentVal,_]),
%	NewTimerVal is CurrentVal+1000 * Secs,
%%	clam_info('Added timeout of %d seconds, id = %d.\n',[Secs,E1]),
%	recorda(timeoutvalue,timeoutvalue(E1,NewTimerVal),_),
%	!.

% checktimeout(?N)
%
% Check to see if any existing timeouts have been triggered. Check the
% most recently set timeouts first (or just test the specified timeout if
% N is instantiated on input). If a timeout triggers, then delete 
% all timeouts which were placed subsequent to the one which
% timed out, because they must have been set deeper in the execution 
% stack than the one which triggered, and will never be able to trigger
% once we unwind the execution stack back over them when the exception
% is raised.
%
%check_time_limit :-
%	recorded(timeoutvalue, timeoutvalue(N, Time), _Ref),
%	statistics(runtime,[Now, _]),
%	Now > Time,
%	!,
%	(recorded(timeoutvalue,timeoutvalue(N2, _),Ref2), N2 > N, erase(Ref2), fail ;
%         raise_exception(timedout(N))).

%check_time_limit.

%delete_timeout(Label) :-
%	recorded(timeoutvalue, timeoutvalue(Label,_), Ref),
%%	clam_info('Deleted timeout id = %d.\n',[Label]),
%	erase(Ref).

foldr([],_F,U,U).
foldr([X|Xs],F,U,Fold) :-
    Fold =.. [F,X,Rec],
    foldr(Xs,F,U,Rec).    

foldl([],_F,U,U).
foldl([X|Xs],F,U,Rec) :-
    Fold =.. [F,U,X],
    foldl(Xs,F,Fold,Rec).    

delete_all([],R,R).
delete_all([H|T],L,R) :-
    select(H,L,RR),
    delete_all(T,RR,R).

del( [H|T], H, T ).
del( [H|T], HH, [H|R] ) :-
    del( T, HH, R ).

delete_one([],_,[]).
delete_one([A|As],A,As) :- !.
delete_one([A|As],B,[A|Bs]) :-
    delete_one(As,B,Bs).

delete_one_id([],_,[]).
delete_one_id([A|As],AA,As) :- A==AA,!.
delete_one_id([A|As],B,[A|Bs]) :-
    delete_one_id(As,B,Bs).

flatten_one_level([],[]).
flatten_one_level([H|T],R) :-
    flatten_one_level(T,RR),
    append(H,RR,R).

equal_modulo_meta_variable_renaming2(L,LL) :-
    %% following rubbish is "modulo variable renaming".
    \+ \+ (make_ground(L), L=LL),
    \+ \+ (make_ground(LL),L=LL),
    unify(L,LL).
equal_modulo_meta_variable_renaming(L,LL) :-
    \+ \+ equal_modulo_meta_variable_renaming_(L,LL),
    unify(L,LL).
equal_modulo_meta_variable_renaming_(L,LL) :-
    (var(L);var(LL)),!,
    var(LL),var(L),
    gensym(c,L),L=LL.
equal_modulo_meta_variable_renaming_(L,LL) :-
    compound(L),compound(LL),!,
    L =.. [F|As],
    LL =.. [F|Bs],
    equal_modulo_meta_variable_renaming_map(As,Bs).
equal_modulo_meta_variable_renaming_(L,LL) :-
    L == LL.
equal_modulo_meta_variable_renaming_map([],[]).
equal_modulo_meta_variable_renaming_map([A|As],[B|Bs]) :-
    equal_modulo_meta_variable_renaming_(A,B),
    equal_modulo_meta_variable_renaming_map(As,Bs).

% ex(+Goal, ?Duration).
%
% Call a goal with a timeout of Duration, if Duration is instantiated,
% otherwise just call the goal.
%
ex(Goal,Duration) :-
    /* assumes that Goal does not interfere with end_time */
    \+ var(Duration),!,
     time_out(Goal, Duration, Result),
     ( Result = time_out
       -> (clam_info('Time limit exceeded.\n',[]), fail)
       ; true ).

ex(Goal, Duration) :-
	var(Duration),
	Goal.

list_tail([_|Z],Z).
list_head([Z|_],Z).


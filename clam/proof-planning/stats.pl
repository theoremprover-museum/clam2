/*
 * @(#)$Id: stats.pl,v 1.6 1997/01/14 10:45:41 img Exp $
 *
 * $Log: stats.pl,v $
 * Revision 1.6  1997/01/14 10:45:41  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.5  1996/07/09 14:57:02  img
 * THIS CODE IS UNSUPPORTED.
 *
 * Revision 1.4  1995/05/17  02:19:20  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.3  1995/03/01  04:16:05  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.2  1994/09/30  14:05:16  dream
 * 	* changed all occurrences of copy/2 to copy_term/2
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: stats.pl,v 1.6 1997/01/14 10:45:41 img Exp $').

/* THIS CODE IS UNSUPPORTED */

/*
 * This file contains code for collecting statistics about the planners.
 * All statistics are used via the predicate stats/3.
 * When taking branchfactor statistics for a planning predicate, its
 * recursive version must be declared dynamic, and reloaded. Similarly,
 * when taking nodesvisited statistics, the predicate applicable/4 must
 * be declared dynamic and reloaded... sigh... I hate Quintus for exactly 
 * this reason.
 *
 * When taking statistics about numbers of object-level rules applied,
 * the situation is worse: not only must rule/3 be dynamic, but the two
 * recursive clauses for rule/3 which insert new(_) or at(_) terms must
 * be modified (done automatically by the code below (yuck)).
 */

	% load advice.pl if not loaded yet.
:- current_predicate(advise,advise(_,_,_))
   orelse
   (source_dir =: D, concat_atom([D,'/advice.pl'],Advice), load(Advice)).

:- (\+ (dialect(swi) ; dialect(qui)))
   orelse
   writef('CLaM WARNING: Ignore subsequent WARNINGS about stats/[2,3]\n').

	% stats(+Statistic,+Mode,+Arg) or stats(+Statistic,+Mode)
	% For Mode={on,off} this switches the taking of Statistic on
	% or off on Arg.
	% For Mode=collect this collects in Arg the statistics taken sofar.
	% 
	% Currently implemented are:
	% stats(branchfactor,on/off,Planner/Arity)
	% stats(branchfactor,collect,B)
	% stats(nodesvisited,on/off)
	% stats(nodesvisited,collect,N)
	% stats(rules,on/off)
	% stats(rules,collect,[Rules,WffRules]).
stats(branchfactor,on,Planner/N) :-
    functor(Pred,Planner,N),
    advised(Pred),!,
    writef('CLaM ERROR: %t is already taking stats\n', [Planner/N]),fail.
	% We assume here that Input is the first argument to Planner/N
	% by convention.
stats(branchfactor,on,Planner/N) :-
    N1 is N-1, same_length(Args,_,N1),
    Pred =.. [Planner,Input|Args],
    advise(Pred,call, (findall(M,applicable(Input,M),Ms), Ms\=[], length(Ms,NrMs),
                          recorda(branchfactor,NrMs,_))).
stats(branchfactor,off,Planner/N) :-
    functor(Pred,Planner,N),
    unadvise(Pred).
stats(branchfactor,collect,B) :-
    findall(N,(recorded(branchfactor,N,Ref),erase(Ref)),Ns),
    Ns \= [],
    length(Ns,NrNs),sum(Ns,Sum), B is Sum/NrNs.

stats(nodesvisited,on) :-
    advised(applicable(_,_,_,_)),!,
    writef('CLaM ERROR: Already counting nodesvisited'),fail.
stats(nodesvisited,on) :-
    advise(applicable(_,_,_,_),exit,recorda(nodesvisited,nodesvisited,_)).
stats(nodesvisited,off) :-
    unadvise(applicable(_,_,_,_)).
stats(nodesvisited,collect,N) :-
    findall(Ref,(recorded(nodesvisited,nodesvisited,Ref),erase(Ref)),Refs),
    length(Refs,N).

	% the rules statistics keeps counters of how many object-level
	% inference rules are applied during the execution of a plan,
	% distinguishing between well-formedness rules and "real" rules.
	% The problem with this is that:
	% 1. The Oyster rule/3 predicate needs to be declared dynamic
	%    This typically means that a slightly modified version of
	%    Oyster needs to be reloaded.
	% 2. Two clauses of the rule/3 predicate need to be changed.
	%    These are the clauses that insert new(_) or at(_) terms in
	%    rules when needed. To achieve this effect, the code below
	%    which switches on the statistics goes around the rule/3
	%    predicates and possibly dynamically changes them if needed
	%    (yuck)... 
stats(rules,on) :-
    advised(rule(_,_,_)),!,
    writef('CLaM ERROR: already taking rule stats\n'),fail.
stats(rules,on) :-
    (massaged_rule_set orelse massage_rule_set(in)),
    advise_rule_set,
    reset_counter(rule),reset_counter(wff).
stats(rules,off) :-
    unadvise(rule(_,_,_)),
    massage_rule_set(out).
stats(rules,collect,[Rules,Wffs]) :-
    recorded(counter,[rule,Rules],_), reset_counter(rule),
    recorded(counter,[wff,Wffs],_),   reset_counter(wff),
    Total is Rules+Wffs,
    writef('(totalling %t)\n',[Total]).

	% size(+Plan,?Size) computes the size of a plan, using weigth as a
	% measure. Weight is one possible way of measuring the size of a
	% tree in general (and therefore of a plan), by counting the
	% number of nodes in the tree. An alternative measure would be
	% depth, which would count the length of the longest branch.
	%
	% Sometimes the code below should be rewritten to allow for mode ?Plan.
	%
	% Can't use predicate name weight/2 since it is already used in
	% Oyster. We use mass/2 instead. Who knows the value of g for
	% plans anyway...
size(P,S) :- mass(P,S).

mass(_ then Pl, W) :- mass(Pl,W1), W is W1+1.
mass([],0).
mass([H|T],W) :- mass(H,Wh), mass(T,Wt), W is Wh+Wt.
mass(_,1).

depth(_ then Pl,D) :- depth(Pl,Dl), D is Dl+1.
depth([H|T],D) :- findall(D1,(member(E,[H|T]),depth(E,D1)),Ds),max(Ds,D).
depth(_,1).

	% Support for rule-stats:
	% First a few simple predicates to maintain indexed counters
	% (increasing, decreasing and resetting to 0),
	% followed by two predicates used in the advise action for rule/3.
	% Finally, the dramatic hack to dynamically change two clauses
	% of the rule/3 predicate as needed.
increase_counter(C) :-
    recorded(counter,[C,N],Ref),!,
    N1 is N+1, erase(Ref),
    recorda(counter,[C,N1],_).

decrease_counter(C) :-
    recorded(counter,[C,N],Ref),
    (N>=0 orelse writef('CLaM Warning: Counter %t dropping below 0\n',[C])),
    N1 is N-1,
    erase(Ref),
    recorda(counter,[C,N1],_).

reset_counter(C) :-
    recorded(counter,[C,N],Ref),
    writef('reseting %t counter valued %t\n',[C,N]),
    erase(Ref),fail.
reset_counter(C) :-
    recorda(counter,[C,0],_).

wff_or_rule(_==>A in _,wff) :- A\=(_=_),!.
wff_or_rule(_==>A in _ ext _,wff) :- A\=(_=_),!.
wff_or_rule(_,rule).

decrease_conditions(rule(reduce(left,_),_,_)).
decrease_conditions(rule(reduce(right,_),_,_)).
decrease_conditions(rule(simplify_,_)).

advise_rule_set :- 
    advise(rule(R,P,S),
           exit,
	   (wff_or_rule(P,C),
	    increase_counter(C),
	    (decrease_conditions(rule(R,P,S)) -> decrease_counter(C)))).
	% Check if dynamic change to rule/3 clauses has already been done
	% (strictly speaking, this code only checks if some clauses look
	%  like they might have been changed, without checking if they
	%  were the right clauses, but I can't be bothered...)
massaged_rule_set :-
    clause(rule(_,_,_),(Body,(wff_or_rule(_,_),decrease_counter(_)))).
	% If the clause set has not been massaged already, massage it
	% here:
	% [1] delete the whole rule set
	% [2] change two members with specified bodies (the clauses that
	%     insert new(_) and at(_) terms)
	% [3] re-assert the newly constructed rule set.
	% (We have to retract/assert the whole rule-set since Prolog
	%  cannot retract/assert clauses at arbitrary positions in a set
	%  of clauses).
	% (To identify the clauses-to-be-changed, we need rely on the
	%  fact that they are the only two clause with all three
	%  arguments variables. This might of course change in the
	%  unforeseen future, in which case this code looses...)
massage_rule_set(InOut) :-
    writef('massaging rule set...%f'),
    retractall(rule(_,_,_),Clauses),
    Decrease=(wff_or_rule(P,C),decrease_counter(C)),
    (InOut=in
     -> (OldValue=(rule(R,P,S):-Body),NewValue=(rule(R,P,S):-(Body,Decrease)))
     ;  (NewValue=(rule(R,P,S):-Body),OldValue=(rule(R,P,S):-(Body,Decrease)))
    ),
    map_list(Clauses,Old:=>New,
            ((Old=OldValue,var(R),var(P),var(S))
	     ->New=NewValue
	     ; Old=New
	    ),
	    NewClauses),
    assertall(NewClauses),
    writef('done\n').

retractall(F,[]) :- \+ clause(F,_).
retractall(F,[(Fc:-B)|Cs]) :-
    copy_term(F,Fc),
    retract((Fc:-B)),
    retractall(F,Cs).
assertall([]).
assertall([C|Cs]) :- assertz(C),assertall(Cs).

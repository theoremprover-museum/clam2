/* X-based planning predicates, xdplan 
 * @(#)$Id: xplan.pl,v 1.1 1994/09/16 09:45:29 dream Exp $
 *
 * $Log: xplan.pl,v $
 * Revision 1.1  1994/09/16 09:45:29  dream
 * Initial revision
 *
 */

xidplan :- xidplan(Plan),xidplan:=Plan.
xidplan(Plan) :- genint(Bound),xidplan(Plan,Bound).
xidplan(Plan,Bound):-
	writef(dialog,'Planning to depth of %d%f\n',[Bound]),
	xdplan(Plan,[],Bound).

xdplan :- xdplan(Plan),xdplan:=Plan.
xdplan(Plan) :- xdplan(Plan,[],1000).
xdplan(Plan,Effects,Bound) :-
    ((Bound = 1000) ; (Bound = 0)),
    cthm=:Thm,!,
    writef(proof,'\n\nPlan construction for %t:\n\n',[Thm]),
    write('clrplan'),nl,
    goal(Input), hyp_list(H),
    xdplan(H==>Input,Plan,Effects,Bound).
xdplan(Plan,Effects,Bound) :-
    goal(Input), hyp_list(H),
    xdplan(H==>Input,Plan,Effects,Bound).

xdplan(Input,Plan,Effects,Bound) :-
    xdplan(Input,Plan,Effects,Bound,0,Ncnt).

xdplan(A,B,C,D,E,F) :- xdplan_(A,B,C,D,E,F).

/* Terminating/Non-terminating method identified. */
xdplan_(Input,Plan,Effects,Bound,Depth,1) :-
    Depth=<Bound,
    Input=(H==>G),
    print_proof_seq(H,G,Depth),
    applicable(Input,Method,_,RealEffects),
    ((Effects = RealEffects,
    	navigate(t,Depth,Str),
    	writef(plan,'%t%t\n',[Str,Method]),
	Plan = Method);
    ([E|Es] = RealEffects,
        navigate(t,Depth,Str),
        writef(plan,'%t%t THEN\n',[Str,Method]),
        Depth1 is Depth+1,  
        iterate_xdplan([E|Es],RestPlans,Effects,Bound,Depth1,N),
        Ncnt is N +1,
	Plan = (Method then RestPlans))).

/* Failure to find an applicable method. */
xdplan_(_, _, _, _, Depth, _) :-
    navigate(bk,1),
    writef(proof, '%rFAILED at depth %t\n', ['|',Depth,Depth]),
    !,
    fail.

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
iterate_xdplan([],[],[],_,_,0).
iterate_xdplan([Input|Inputs], [Plan|Plans], Effects, Bound, Depth, Ncnt) :-
        (Effects==[]->Effect=[];true),
    xdplan(Input,Plan,Effect,Bound,Depth,N1),
    (Effect=[]->! ; true ),
    append(Effect,OtherEffects,Effects),
    ((iterate_xdplan(Inputs,Plans,OtherEffects,Bound,Depth,N2),Ncnt is N1 + N2);
     (navigate(bk,N1),!,fail)).

navigate(t,X,String) :- tabs(X,String).
tabs(0,'') :- !.
tabs(X,S):- X1 is X-1 , tabs(X1,SS), concat_atom(['  ',SS],S).
navigate(b):- write('backup'),nl.
navigate(k):- write('killline'),nl.
navigate(bk,0).
navigate(bk,N):- 
	navigate(b),
	navigate(k),
	NN is N-1,
	navigate(bk,NN).
navigate(n):- nl.

wait(0).
wait(X):- X1 is X-1, wait(X1).

print_proof_seq(H,G,Depth):-
    			writef(proof, 'DEPTH: %t\n', [Depth] ) ,
    			print_nllist(proof,H),
    			annotations(_,_,GG,G),
    			writef(proof,'==>%t\n',[GG]),!.

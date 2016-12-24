/* Applicability of methods (with X)
 * @(#)$Id: xapplicable.pl,v 1.1 1994/09/16 09:45:29 dream Exp $
 *
 * $Log: xapplicable.pl,v $
 * Revision 1.1  1994/09/16 09:45:29  dream
 * Initial revision
 *
 */

/*
 * this code does not duplicate any in the standard proof-planning/applicable.pl
 * only that which changes for XCLaM; in this case, only applcble/5 changes
 */
applcble(Type,Input,Try_Method,Post,Effects) :-
    functorp(Try_Method,try,1), !,
    applicable_try(Type,Input,Try_Method,Post,Effects).
	% For the then/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of then/2 methodical.
applcble(Type,Input,Then_Method,Post,Effects) :-
    functorp(Then_Method,then,2), !,
    applicable_then(Type,Input,Then_Method,Post,Effects).
	% For the or/2 methodical we call special-case code defined in
	% methodical.pl. See there for semantics of or/2 methodical.
applcble(Type,Input,Or_Method,Post,Effects) :-
    functorp(Or_Method,or,2), !,
    applicable_or(Type,Input,Or_Method,Post,Effects).

/* this is the main change, the other 3 clauses are identical */
applcble(Type,Input,Method,Post,Effects) :-
    apply(Type,[Method,Input,Pre,Post,Effects,_Tactic]),
    call_conjunction(Pre),
    call_conjunction(Post),
    display_ripple(Method,Effects).		%and output some info in the ripple window

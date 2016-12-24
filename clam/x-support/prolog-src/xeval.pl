/* Oyster eval predicates wrapped up in pleasant interface 
 * @(#)$Id: xeval.pl,v 1.1 1994/09/16 09:45:29 dream Exp $
 *
 * $Log: xeval.pl,v $
 * Revision 1.1  1994/09/16 09:45:29  dream
 * Initial revision
 *
 */

xeval(Args) :-
    extract(E),
    \+ var(E),
    xeval(E,Args,Ans & _),
    pnat2natlist(Ans,NAns),
    cthm=:Thm,
    writef('(%t ',[Thm]),
    print_args(Args),
    writef('%t\n',[NAns]).

print_args([]):- write(') = ').
print_args([H|T]) :-
    writef(' %t',[H]),
    print_args(T).

xeval(E,[],E).
xeval(E,[Arg|Args],Ans):-
    integer(Arg),
    nat2pnat(Arg,NArg),
    eval(E of NArg,EE),
    xeval(EE,Args,Ans).
xeval(E,[Arg|Args],Ans):-
    pnat2natlist(NArg,Arg),
    eval(E of NArg,EE),
    xeval(EE,Args,Ans).


nat2pnat(0,0).
nat2pnat(N,s(M)) :- NN is N-1, nat2pnat(NN,M).
pnat2nat(0,0).
pnat2nat(s(X),M) :- pnat2nat(X,MM),M is MM+1.
pnat2natlist(nil,[]).
pnat2natlist(H::T,[HH|TT]) :- pnat2nat(H,HH),pnat2natlist(T,TT).


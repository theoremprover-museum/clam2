/*
 * @(#)$Id: wterm.pl,v 1.4 1997/01/14 10:45:48 img Exp $
 *
 * $Log: wterm.pl,v $
 * Revision 1.4  1997/01/14 10:45:48  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:28  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:16:19  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: wterm.pl,v 1.4 1997/01/14 10:45:48 img Exp $').

% \ulinv{wterm(}
wterm(_,X,_) :- portray(X),!.
wterm(S,C:A#B,W):-par(wdecl(S,C:A#B,W)).
wterm(S,C:A=>B,W):-par(wdecl(S,C:A=>B,W)).
wterm(S,C:A,W):-par(wdecl(S,C:A,W)).

wterm(S,X,w(_,W)):-cscreensize=:N,S+W<N-10,par(write(X)),!.
wterm(S,X,W):-cscreensize=:N,0.6*N<S,SS is S-N//2,wterm(SS,X,W),!.

wterm(S,X,w(XX,_)):-
    append(Y,[T],X),append(YY,[TT],XX), S1 is S+1,
    write('['),weight(Y,w(_,Yw)),
    ( cscreensize=:N,S+Yw+2>N,wterml(S1,Y,YY); wterml(Y) ),
    write(','),nl,tab(S1), wterm(S1,T,TT),write(']'),!.
wterm(S,lambda(X,F),w(lambda(_,FF),_)):-
    write('lambda('),write(X),write(','),
    S1 is S+2,nl,tab(S1),wterm(S1,F,FF),write(')'),!.
wterm(S,A#B,w(AA#BB,_)):-
    wterm(S,A,AA),write('#'),nl,tab(S), wterm(S,B,BB),!.
wterm(S,A=>B,w(AA=>BB,_)):-
    wterm(S,A,AA),write('=>'),S1 is S+2,nl,tab(S1), wterm(S1,B,BB),!.
wterm(S,A=B in T,w(w(AA=BB,_) in TT,_)):- 
    S1 is S+1,S2 is S+3,S3 is S+4,
    write('('),wterm(S1,A,AA),nl,tab(S),
    write(' = '),wterm(S2,B,BB),nl,tab(S),
    write(' in '),wterm(S3,T,TT),write(')'),!.
wterm(S,A in T,w(AA in TT,_)):- S1 is S+1,S2 is S+4,
    write('('),wterm(S1,A,AA),nl,tab(S),
    write(' in '),wterm(S2,T,TT),write(')'),!.
wterm(S,{X},w({XX},_)):-S1 is S+1,
    write('{'),wdecl(S1,X,XX),write('}'),!.

wterm(_,u(I),_):-write(u(I)),!.
wterm(_,X,_):-atom(X),write(X),!.
wterm(_,X,_):-integer(X),write(X),!.
wterm(S,X,w(XX,_)):- 
    standardform(X),X=..[F|A], write(F),write('('),nl,tab(S),
    XX=..[F|AA],wterml(S,A,AA),write(')'),!.
wterm(S,X,w(XX,_)):-
    X=..[F,A,B], XX=..[F,AA,BB],
    cshift=:N,weight(F,w(_,Fw)),S1 is S+1,S2 is S+N+Fw+1,
    write('('),wterm(S1,A,AA),nl,tab(S),
    tab(N),write(F),write(' '),wterm(S2,B,BB),write(')'),!.
wterm(_,X,_):-par(write(X)).

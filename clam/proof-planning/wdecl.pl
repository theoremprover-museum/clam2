/*
 * @(#)$Id: wdecl.pl,v 1.4 1997/01/14 10:45:45 img Exp $
 *
 * $Log: wdecl.pl,v $
 * Revision 1.4  1997/01/14 10:45:45  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:24  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:16:12  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: wdecl.pl,v 1.4 1997/01/14 10:45:45 img Exp $').

% \ulinv{wdecl(}
wdecl(S,X,w(_,W)):-cscreensize=:N,S+W<N-10,print(X),!.
wdecl(S,X,W):-cscreensize=:N,0.6*N<S,SS is S-N//2,wdecl(SS,X,W),!.

wdecl(S,C:A#B,w(w(_,CC):w(AA#BB,_),_)):- 
    cshift=:N,S1 is S+CC+1, S2 is S+N,
    print(C),write(':'),wterm(S1,A,AA),write('#'),nl,tab(S2), wdecl(S2,B,BB),!.
wdecl(S,C:A=>B,w(w(_,CC):w(AA=>BB,_),_)):-
    cshift=:N,S1 is S+CC+1, S2 is S+N,
    print(C),write(':'),wterm(S1,A,AA),write('=>'),nl,tab(S2),wdecl(S2,B,BB),!.
wdecl(S,C:A\B,w(w(_,CC):w(AA\BB,_),_)):-
    cshift=:N,S1 is S+CC+1, S2 is S+N,
    print(C),write(':'),wterm(S1,A,AA),write('\'),nl,tab(S2), wdecl(S2,B,BB),!.
wdecl(S,C:A,w(w(_,CC):AA,_)):-S1 is S+CC+1,
    print(C),write(':'),wterm(S1,A,AA),!.
wdecl(S,A#B,w(AA#BB,_)):-
    wterm(S,A,AA),write('#'),nl,tab(S), wdecl(S,B,BB),!.
wdecl(S,A=>B,w(AA=>BB,_)):-
    wterm(S,A,AA),write('=>'),S1 is S+2,nl,tab(S1), wdecl(S1,B,BB),!.
wdecl(S,X,W):-wterm(S,X,W).

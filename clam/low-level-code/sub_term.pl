/*
 * @(#)$Id: sub_term.pl,v 1.4 1997/01/14 10:50:12 img Exp $
 *
 * $Log: sub_term.pl,v $
 * Revision 1.4  1997/01/14 10:50:12  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:48  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:36  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: sub_term.pl,v 1.4 1997/01/14 10:50:12 img Exp $').

%***************
%*
%*	ttsub_terms -  Work out the subterms of nurprl term,
%*		  extended to allow unary sub terms.
%*
%*  ttsub_terms(+Tm,-Dterms) - Dterms are the subterms of Tm.
%*  ttsub_term(+Tm,?Dterm) - Dterm is a subterm of Tm.
%*
%***************

ttsub_terms( Tm, Dterms ) :-
    findall( Dterm, ttsub_term(Tm,Dterm), Dterms ),
    !.

ttsub_terms( _, [] ).


ttsub_term( V, _ ) :-
    var(V),
    !,
    fail.

ttsub_term( atom(A), atom(A) ) :-
    !.

ttsub_term( term_of(Name), term_of(Name) ) :-
    !.

ttsub_term( {Name}, {Name} ) :-
    atom(Name),
    !.

ttsub_term(Dterm,Dterm) :-
    atom(Dterm),
    !.

ttsub_term( T, T ).
ttsub_term( [H|T], Dterm ) :-
    append( _, [BTerm], [H|T] ),
    ttsub_term( BTerm, Dterm ).


ttsub_term( (_:T1#T2), Dterm ) :-		% *** Deal with binding types
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( (_:T1=>T2), Dterm ) :-
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( ({_:T1 \ T2}), Dterm ) :-
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( lambda(_,T), Dterm ) :-	% *** lambda term
    ttsub_term( T, Dterm ).


ttsub_term( Tm, Dterm ) :-		% *** Non-binding connectives etc
    Tm =.. [_|Args],
    member(Arg,Args),
    ttsub_term( Arg, Dterm ).



/*
 * @(#)$Id: portrayTeX.pl,v 1.23 2008/05/21 14:14:15 smaill Exp $
 *
 * $Log: portrayTeX.pl,v $
 * Revision 1.23  2008/05/21 14:14:15  smaill
 * update for sicstus4
 *
 * Revision 1.22  1999/04/30 15:30:49  img
 * avoid divergence in ind_strat
 *
 * Revision 1.21  1998/09/16 14:16:39  img
 * ind_strat(cases) case
 *
 * Revision 1.20  1998/06/10 09:38:54  img
 * *** empty log message ***
 *
 * Revision 1.19  1998/05/13 13:05:00  img
 * clause for generalize
 *
 * Revision 1.18  1997/11/12 15:16:56  img
 * Added clause for methods with two arguments
 *
 * Revision 1.17  1997/11/11 17:43:59  img
 * Minor typos
 *
 * Revision 1.16  1997/11/08 12:26:01  img
 * elide lemma information in induction tactic
 *
 * Revision 1.15  1997/10/08 15:16:27  img
 * portray_level_/3 bug
 *
 * Revision 1.14  1997/09/26 15:04:08  img
 * bug fixes
 *
 * Revision 1.13  1997/04/07 11:49:29  img
 * use lengtheq/2.
 *
 * Revision 1.12  1997/01/14 10:45:40  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.11  1996/12/06 14:38:10  img
 * portary direction tag in induction markers
 *
 * Revision 1.10  1996/12/04 13:01:14  img
 * Proto-code to allow a new type of portraying to be used inside Emacs
 * clam-mode.  push_portray_type/1 and pop_portray_type affect
 * portrayal.  Also portray_level/3 allows fine control on a
 * functor-by-functor basis.  (Also small change inside
 * config/methods.pl, for initialization.)
 *
 * Revision 1.9  1996/08/09 08:22:24  img
 * Use abstraction predicates for annotations.
 *
 * Revision 1.8  1996/07/05  10:25:12  img
 * Update portray/1 clauses for revised methods;  add clauses for wave/4
 * terms.
 *
 * Revision 1.7  1995/10/03  13:14:07  img
 * update for arity changes;  small bug in the portrayal of induction
 * markers.
 *
 * Revision 1.6  1995/09/13  17:44:34  img
 * fixed incorrect portray of ihmarker
 *
 * Revision 1.5  1995/05/17  02:19:18  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.4  1995/03/01  04:16:02  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.3  1994/09/16  10:53:45  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.2  1994/09/16  10:17:16  dream
 * 	* pretty print defined terms in TeX
 * 	* make portray_{normal,TeX}/1 dynamic
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: portrayTeX.pl,v 1.23 2008/05/21 14:14:15 smaill Exp $').

:- dynamic portray/1.				%needed by Quintus
:- dynamic portray_with_type/2.
:- dynamic portray_type_/1.
:- dynamic portray_type_old_/1.
:- dynamic portray_level_/2.
:- dynamic portray_in_nf_/1.

portray_level_(default,50).
portray_in_nf_(no).

portray_type_([normal]).
push_portray_type(Type) :-
    member(Type,[normal,tex,emacs]),!,
    portray_type_(Types),
    retractall(portray_type_(_)),
    assertz(portray_type_([Type|Types])).
push_portray_type(_Type) :-
    clam_warning('You supplied an illegal portray type.  Valid types'),
    clam_warning('are "normal", "tex" and "emacs"').
pop_portray_type :-
    portray_type_([_|Types]),
    retractall(portray_type_(_)),
    assertz(portray_type_(Types)).

portray_in_nf(yes) :-
    !, retractall(portray_in_nf_(_)),
    assert(portray_in_nf_(yes)).
portray_in_nf(no) :-
    !, retractall(portray_in_nf_(_)),
    assert(portray_in_nf_(no)).
portray_in_nf(_) :-
    clam_warning('The argument must be "yes" or "no".').

portray_type(Type) :-
    portray_type_([Type|_]).

portray_level(Term,O,N) :-
    Term =.. [F|Args], lengtheq(Args,SLA),
    Temp =.. [F|SLA],
    portray_level_(Temp,O,N).
portray_level_(Term,O,N) :-			% read current value
    var(N),!,
    var(O),
    once((portray_level_(Term,O);portray_level_(default,O))).
portray_level_(Term,O,N) :-			% write new value
    once((portray_level_(Term,O); true)),
    retractall(portray_level_(Term,_)),
    assertz(portray_level_(Term,N)).

portray(XX) :- 
    (portray_in_nf_(no) -> maximally_joined(XX,X) ; X=XX),
    portray(X,P),!,				% pick only one
    portray_type(Type),
    once((portray_level(X,Level,_);portray_level(default,Level,_))),
    member(Type:TypeInfo,P),
    member(L-LevelInfo,TypeInfo),
    /* If L is a var, assume the clause is a catch-all */
    once((var(L); Level =< L)),
    portray_items(LevelInfo),!.


portray_items([]).
portray_items([H|T]) :-
    print(H),portray_items(T).


/* Portray database */

:- dynamic portray/2.
portray(generalise(T), [_:[99-[generalise,'(',T,')']]]).
portray(fertilize(T,Ms), [tex:[99-[fertilize,'(',T,',\\ldots)']],
			   _  :[50-[fertilize,'(',T,',...)'],
				99-[fertilize,'(',T,',',Ms,')']]]).

portray(weak_fertilize(Dir,L), [tex:[99-[weakfertilize,'(',Dir,',\\ldots)']],
				 _  :[50-[weak_fertilize,'(',Dir,',...)'],
				      99-[weak_fertilize,'(',Dir,',',L,')']]]).

portray(ripple(A,P), [tex:[99-[ripple,'(\\ldots)']],
		       _  :[50-[ripple,'(...)'],
			    99-['ripple(',A,',',P,')']]]).

portray(wave(A,B,[C,D],E), [tex:[99-['wave(',(A,B,[C,D],E),')']],
			     _  :[50-['wave(', C, ')'],
				  99-['wave(',(A,B,[C,D],E),')']]]).

portray(ind_strat(cases(S)),
	[tex:[99-['\\mbox{\\sf cases(}', S, '\\mbox{\\sf )}']],
	 _  :[50-[cases,'(', S, ')'],
	      99-['ind_strat(cases(',S,'))']]]).
portray(ind_strat(induction(I-S) then CT),
	[tex:[99-['\\mbox{\\sf ind\\_strat(}', S, '\\mbox{\\sf )}']],
	 _  :[50-[ind_strat,'(', S, ')'],
	      99-['ind_strat(',induction(I-S) then CT,')']]]).
portray(unflawed_ind_strat(induction(I-S) then CT),
	[tex:[99-['\\mbox{\\sf unflawed\\_ind\\_strat(}', S, '\\mbox{\\sf )}']],
	 _  :[50-[unflawed_ind_strat,'(', S, ')'],
	      99-[unflawed_ind_strat(induction(I-S) then CT)]]]).

portray(ihmarker(raw,_), [tex:[_-['{\\tt RAW}']],_:[_-['RAW']]]).
portray(ihmarker(notraw(Ds),_), [tex:[_-['{\\tt NOTRAW}(',Ds,')']],
				 _:[_-['NOTRAW(',Ds,')']] ]).
portray(ihmarker(used(Ds),_), [tex:[_-['{\\tt USED}(',Ds,')']],
			       _:[_-['USED(',Ds,')']]]).

portray(Hole, [tex:[99-['\\wh{',Term,'}']],
	       normal:[99-['{', Term,'}']],
	       emacs:[99-['\\hole(', Term,')']]]) :-
    striphole(Hole,Term).

portray(Front, [tex:[99-['\\wfout{',Term,'}']],
		normal:[99-['``', Term,'''''','<',Dir,'>']],
		emacs:[99-['\\wfout(', Term,')']]]) :-
    stripfront(Front,hard,Dir,Term).

portray(Front, [tex:[99-['\\pwf{',Term,'}']],
		normal:[99-['"', Term,'"']],
		emacs:[99-['wfout(', Term,')']]]) :-
    stripfront(Front,soft,_,Term).
portray(Sink, [tex:[99-['sink{',Term,'}']],
	       normal:[99-['\\', Term,'/']],
	       emacs:[99-['sink(', Term,')']]]) :-
    stripsink(Sink,Term).

portray((T1 = T2 in Type)=>void, [tex:[99-[T1, '\\neq', T2, '\\:{\\bf in}\\:', Type]]]).
portray(V:T1=>T2, [tex:[99-['\\Pi ', V, '\\!:\\!', T1, '.', T2]]]).
portray(V:T1#T2, [tex:[99-['\\Sum ', V, '\\!:\\!', T1, '.', T2]]]).
portray({V:T1\T2}, [tex:[99-['\\{', V, '\\!:\\!', T1, '\\backslash ', T2, '\\}']]]).
portray(T1#T2, [tex:[99-[T1, '\\# ', T2]]]).
portray(T1 of T2, [tex:[99-[T1, '\\:{\bf of }\\: ', T2]]]).
portray(lambda(V,T), [tex:[99-['\\lambda ', V, '.', T]]]).
portray(T1&T2, [tex:[99-[T1, '\\& ', T2]]]).
portray(T1=>void, [tex:[99-['\\neg ',  T1]]]).
portray(T1=>T2, [tex:[99-[T1, '\\rightarrow ', T2]]]).
portray(Term in Type, [tex:[99-[Term, '\\:{\\rm in}\\: ', Type]]]).
portray(Type list, [tex:[99-[Type, '\\: {\\rm list} ']]]).
portray(V:T, [tex:[99-[V, '\\!:', T]]]).

/* Uniform treatment of methods with 1 argument */
portray(Term, [tex:[99-['\\sfbox{', F,'(\\ldots)}']],
		_  :[50-[F,'(...)'],
		     99-[F,'(', P, ')']]]) :-
    Term =.. [F,P],
    Temp =.. [F,_],
    once((method(Temp,_,_,_,_,_);submethod(Temp,_,_,_,_,_))).

portray(Term, [tex:[99-['\\sfbox{', F,'(\\ldots)}']],
		_  :[50-[F,'(...)'],
		     99-[F,'(', P, Q, ')']]]) :-
    Term =.. [F,P,Q],
    Temp =.. [F,_,_],
    once((method(Temp,_,_,_,_,_);submethod(Temp,_,_,_,_,_))).
	    

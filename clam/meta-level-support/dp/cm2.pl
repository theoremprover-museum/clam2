/*
 * @(#)$Id: cm2.pl,v 1.16 2005/05/06 19:25:57 smaill Exp $
 *
 * $Log: cm2.pl,v $
 * Revision 1.16  2005/05/06 19:25:57  smaill
 * take out check_time_limit (dealt with by sictus timing module);
 *
 * Revision 1.15  1997/06/05 10:46:00  img
 * Added support for <=>.
 *
 * Revision 1.14  1997/05/12 11:12:56  img
 * Revised implementation of true and false; now encoded via 0=0 and 0=1.  NB VOID is no longer an atomic proposition.
 *
 * Revision 1.13  1997/05/12 10:20:30  img
 * Extend syntax of PA with {true}
 *
 * Revision 1.12  1997/05/12 09:38:13  img
 * Allow equality over int and pnat
 *
 * Revision 1.11  1997/05/08 12:19:04  img
 * Extended Presburger
 *
 * Revision 1.10  1997/05/08 10:10:54  img
 * [revert back to v1.8]
 *
 * Revision 1.9  1997/05/08 10:03:12  img
 * Map pnat equality to int.
 *
 * Revision 1.8  1997/05/08 09:58:11  img
 * Equality may be in pnat or int.
 *
 * Revision 1.7  1997/05/07 18:31:32  img
 * Quantification over pnat and int supported.
 *
 * Revision 1.6  1997/05/06 15:22:27  img
 * Improved generality of syntax check; atomic_formula/1 now faster
 *
 * Revision 1.5  1997/05/06 13:19:39  img
 * atomic_formula/1 specific to Presburger
 *
 * Revision 1.4  1997/05/06 10:52:50  img
 * Tidied up code; normal/_ renamed to prenex_dnf (does not require
 * Presburger syntax)
 *
 * Revision 1.3  1997/02/20 14:57:46  img
 * faster code
 *
 * Revision 1.2  1997/01/14 10:36:57  img
 * Added headers, renamed substitute/4 to h_substitute/4.
 *
 * Revision 1.1  1997/01/14 10:23:49  img
 * Decision procedures.
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: cm2.pl,v 1.16 2005/05/06 19:25:57 smaill Exp $').

% ******************************************************************
%   Module 2 for communication between the proof planner CLaM and
%      decision procedure for Presburger Integer Arithmetic
%
%             Written by Predrag Janicic, 1996.
%         Mathematical Reasoning Group (DReaM Group)
%           Department of Artificial Intelligence 
%                 University of Edinburgh
% ****************************************************************

/* Decide whether F is a statement of Presburger Arithmetic.  */
presb_formula(F) :- 
    well_formed(F,[[greater, less, geq, leq],
		   [ /* defined functors go here */]]).
presb_formula_extended(F) :- 
    well_formed(F,[[greater, less, geq, leq],
		   [ minus, p /* defined functors go here */]]).

well_formed(A,P) :- atomic_formula_wf(A,P),!.	% atomic formulae
well_formed(_:_=>F2,P):- !,well_formed(F2,P).	% fol
well_formed(_:_#F2,P):- !,well_formed(F2,P).
well_formed(F1=>void,P) :- !,well_formed(F1,P).
/* NB.  <=> is translated away later (by to_basic_presburger/2) */
well_formed(F1<=>F2,P) :- !,well_formed(F1,P), well_formed(F2,P).
well_formed(F1=>F2,P) :- !,well_formed(F1,P), well_formed(F2,P).
well_formed(F1#F2,P) :- !,well_formed(F1,P), well_formed(F2,P).
well_formed(F1\F2,P) :- !,well_formed(F1,P), well_formed(F2,P).

/* atomic_formula_wf(+T,+P) if T is a well-formed atomic formula in
   context P.  The difference between this predicate and
   atomic_formula/1 is that the latter only examines propositional
   structure for efficiency.  */
atomic_formula_wf([_,_,_],_) :- !.
atomic_formula_wf(void,_) :- !.
atomic_formula_wf({true},_) :- !.
atomic_formula_wf(T1 = T2 in T, [_,Tms]) :-
    !, term(T1,Tms), term(T2,Tms), tip(T).
atomic_formula_wf(Formula,[P,Tms]) :-
    Formula =.. [F|Args],
    member(F,P),
    map_list(Args, A :=> _, term(A,Tms),_).

/* T is an atomic statement of PA (NB it need not be well-formed since
   the internal structure of atomic predicates is not examined.  NB
   VOID and {TRUE} are _not_ atomic here, since they are translated
   internally into 0=1 and 0=0.  */
/* atomic_formula([_,_,_]) :- !.
atomic_formula(_ = _ in _) :- !.
atomic_formula(Formula):- rel(Formula,_,_),!. */
/* atomic_formula(H) :- defined_rel(A,_),!. */

/* We do this by negation of not_atomic_formula since otherwise we
   need to examine the entire term.  */
atomic_formula(T) :- \+ not_atomic_formula(T).
not_atomic_formula(_:_=>_) :- !.
not_atomic_formula(_:_#_):- !.
not_atomic_formula(_=>void) :- !.
not_atomic_formula(_=>_) :- !.
not_atomic_formula(_#_) :- !.
not_atomic_formula(_\_) :- !.
not_atomic_formula(_<=>_) :- !.

literal(F1 => void):-
    !,atomic_formula(F1).
literal(F):-atomic_formula(F).

conective(\) :- !.
conective(#) :- !.
conective(=>) :- !.

rel(greater) :- !.
rel(less) :- !.
rel(geq) :- !.
rel(leq) :- !.

rel(greater(A,B),A,B).
rel(less(A,B),A,B).
rel(geq(A,B),A,B).
rel(leq(A,B),A,B).

neg0(greater,less).
neg0(less,greater).
neg0(geq,leq).
neg0(leq,geq).
neg0(=,=).

neg_rel(greater,leq).
neg_rel(geq,less).
neg_rel(less,geq).
neg_rel(leq,greater).
neg_rel(=,=).

conj_or_disj(\) :- !.
conj_or_disj(#) :- !.

quanti(=>) :- !.
quanti(#) :- !.

term(H,_):-atom(H),!.				% variables
term(H,_):-integer(H),!.
term(plus(C,D),Tms):-!,term(C,Tms),term(D,Tms).
term(s(C),Tms):-!,term(C,Tms).
term(times(C,D),Tms):-mconst(C,Tms),!,term(D,Tms).
term(times(C,D),Tms):-term(C,Tms),mconst(D,Tms).

term(H,Tms) :-					% defined functors
    H =.. [F|As], member(F,Tms),
    map_list(As,A :=> _,term(A,Tms),_).

mconst(C,_) :- integer(C),!.
mconst(plus(C,D),Tms):-!,mconst(C,Tms),mconst(D,Tms).
mconst(s(C),Tms):-!,mconst(C,Tms).
mconst(times(C,D),Tms):-!,mconst(C,Tms),mconst(D,Tms).
mconst(H,Tms) :-					% defined functors
    H =.. [F|As], member(F,Tms),
    map_list(As,A :=> _,mconst(A,Tms),_).

tip(int).
tip(pnat).

% ***********************************************************
%  This is a section for converting CLaM atomic formulae to
%    Presburger Arithmetic atomic formulae
% ***********************************************************

% convert(Input,Output) 
% Input=Presburger formula in a prenex normal form
% Output=correspoding formula in a specific format
% (see bellow explanation for convert_atomic_formula).  
convert(Formula,L_formula):-
    atomic_formula(Formula),!,
    convert_atomic_formula(Formula,L_formula).

convert(V:int=>F,V:int=>FF) :- !,convert(F,FF).
convert(V:int#F,V:int#FF) :- !,convert(F,FF).
convert(_:pnat=>_,_) :- !,clam_error('convert/2: quantification over pnat not permitted.').
convert(_:pnat#_,_) :- !,clam_error('convert/2: quantification over pnat not permitted.').

convert(Formula,L_formula):-functor(Formula,C,_),
	                    conj_or_disj(C),!,
                            arg(1,Formula,F1),
	                    arg(2,Formula,F2),
			    convert(F1,C1),
                            convert(F2,C2),
			    L_formula=..[C,C1,C2].

convert(Formula,L_formula):-functor(Formula,=>,_),
	                    arg(1,Formula,F1),
			    not(F1=pnat),
			    arg(2,Formula,void),
                            convert(F1,C1),
			    L_formula=..[=>,C1,void].



% convert_atomic_formula(Input,Output)
% Input=CLaM atomic formula (for example: greater(s(plus(x,x)),plus(x,y)) )
% Output=corresponding simplified Presburger atomic formula in a specific format
% We use specific structure for defining Presburger formulae.
% For example, the terms:
% plus(x,y), s(x),  x-y+1
% we write, respectivelly, as
% [[1,x],[1,y]], [[1,x],[1,1]], [[1,x],[-1,y],[1,1]]
% For example, the formulae
% greater(s(plus(x,x)),plus(x,y), plus(x,plus(y,z))=plus(plus(x,y),z)
% we write respectivelly as
% [greater,[[1,x],[-1,y],[1,1]],[]], [=,[],[]]
% First formula could be written in a different way as:
% [greater,[[1,x],[1,1]],[1,y]] ...
% 

convert_atomic_formula({true},[=,[],[]]) :- !.	% for the benfit of CLAM
convert_atomic_formula(void,[greater,[],[]]) :- !. % for the benfit of CLAM
convert_atomic_formula(Formula,L_formula):-functor(Formula,R,_),
	                                   rel(R),
			                   arg(1,Formula,T1),
					   arg(2,Formula,T2),
			                   convert_term(T1,Pt1),
			                   convert_term(T2,Pt2),
			                   negate(Pt1,Pt11),
			                   append(Pt11,Pt2,L1),
			                   simplify_term(L1,L2),
			                   L_formula=[R,[],L2].
convert_atomic_formula(T1 = T2 in Type,L_formula):-
    (Type = int ; Type = pnat),!,
    convert_term(T1,Pt1),
    convert_term(T2,Pt2),
    negate(Pt1,Pt11),
    append(Pt11,Pt2,L1),
    simplify_term(L1,L2),
    L_formula = [=,[],L2].

convert_term(Term,[[1,Term]]):-atom(Term).
convert_term(Term,[[Term,1]]):-integer(Term).
convert_term(Term,L_term):-functor(Term,Op,2),
	                   arg(1,Term,T1),
			   arg(2,Term,T2),
			   convert_term(T1,Ct1),
			   convert_term(T2,Ct2),
			   join(Op,Ct1,Ct2,L_term).

convert_term(Term,L_term):-functor(Term,s,1),
	                   arg(1,Term,T1),
			   convert_term(T1,Ct1),
			   join(plus,Ct1,[[1,1]],L_term).

convert_term(Term,L_term):-functor(Term,p,1),
	                   arg(1,Term,T1),
			   convert_term(T1,Ct1),
			   join(minus,Ct1,[[1,1]],L_term).

negate([],[]).
negate([A|B],[A1|B1]):-A=[M,V],M1 is -M, A1=[M1,V],negate(B,B1).


join(plus,T1,T2,L_term):- append(T1,T2,L1),simplify_term(L1,L_term).
join(minus,T1,T2,L_term):-negate(T1,T11),join(plus,T11,T2,L_term).

join(times,L,_,[]):-L=[].
join(times,L1,L,[]):-not(L1=[]),L=[].
join(times,L1,L2,L):-L1=[[M,1]],!,multi(M,L2,L).
join(times,L1,L2,L):-L2=[[M,1]],multi(M,L1,L). % not(L1=[[_,1]])

multi(_,[],[]) :- !.
multi(M,[A|B],[A1|B1]):- A=[M1,V],M2 is M1*M,A1=[M2,V],multi(M,B,B1).

simplify_term([],[]).
simplify_term([A|B],B1):-   A=[M,_], M=:=0, !, simplify_term(B,B1).
simplify_term([A|B],B1):-   A=[M,V], M=\=0,
    occ(V,B),!,add(M,V,B,B2),simplify_term(B2,B1).
simplify_term([A|B],[A|C]):-A=[M,_], M=\=0, simplify_term(B,C).


simplify_af([d,X,Y],[d,X,Y1]):- !,
    simplify_term(Y,Y1).
simplify_af([nd,X,Y],[nd,X,Y1]):- !,
    simplify_term(Y,Y1).

simplify_af([R,X,Y],[R,[],Y2]):-
    negate(X,X1),
    append(X1,Y,Y1),
    simplify_term(Y1,Y2).

add(M,V,[X|Y],[X1|Y]):-X=[M1,V],M2 is M1+M,M2=\=0,X1=[M2,V],!.
add(M,V,[X|Y],Y):-     X=[M1,V],M1+M =:= 0,!.
add(M,V,[X|Y],[X|Y1]):-add(M,V,Y,Y1).

occ(V,[[_,V]|_]):- !.
occ(V,[_|B]):- occ(V,B).


% **********************************************************
% This is a section for simplifying LA terms and formulae
%
% **********************************************************


simplify_formula(F,F1):-canonic(F,Ff),
 	                la_reduction(Ff,F1).


canonic(F,F1):-atomic_formula(F),!,
	       simplify_af(F,F1).

canonic(F,Fc):-functor(F,C,_),
	       conj_or_disj(C),!,
	       arg(1,F,F1),
	       arg(2,F,F2),
               canonic(F1,F11),
	       canonic(F2,F21),
	       Fc=..[C,F11,F21].


% la_reduction(_,_):-check_time_limit,fail.
la_reduction(Formula,Formula):-atomic_formula(Formula),!.
la_reduction(F1 # F2,Formula1):- 
    true_form(F1),!,
    la_reduction(F2,Formula1).
la_reduction(_ # F2,Formula1):- 
    false_form(F2),!,
    la_reduction(F2,Formula1).
la_reduction(F1 # _,Formula1):- 
    false_form(F1),!,
    la_reduction(F1,Formula1).
la_reduction(F1 # F2,Formula1):- 
    true_form(F2),!,
    la_reduction(F1,Formula1).
la_reduction(F1 \ _,Formula1):- 
    true_form(F1),!,
    la_reduction(F1,Formula1).
la_reduction(F1 \ F2,Formula1):- 
    false_form(F2),!,
    la_reduction(F1,Formula1).
la_reduction(F1 \ F2,Formula1):- 
    false_form(F1),!,
    la_reduction(F2,Formula1).
la_reduction(_ \ F2,Formula1):- 
    true_form(F2),!,
    la_reduction(F2,Formula1).
la_reduction(F1 # F2,Formula1):-
    F1=F2,!,
    la_reduction(F1,Formula1).
la_reduction(F1 # F2,Formula1):-
    la_reduction(F1,F11),
    la_reduction(F2,F21),
    ((F1=F11, F2=F21) -> Formula1 = (F11 # F21);
     la_reduction(F11 # F21,Formula1)),!.
la_reduction(F1 \ F2,Formula1):-
    F1=F2,!,
    la_reduction(F1,Formula1).

la_reduction(F1 \ F2,Formula1):-
    la_reduction(F1,F11),
    la_reduction(F2,F21),
    ((F1=F11, F2=F21) -> Formula1 = (F11 \ F21);
     la_reduction(F11 \ F21,Formula1)),!.

true_form([=,[],[]]) :- !.
true_form([less,[],[[M,1]]]):-M>0,!.
true_form([greater,[],[[M,1]]]):-M<0,!.
true_form([less,[[M,1]],[]]):-M<0,!.
true_form([gretaer,[[M,1]],[]]):-M>0,!.
true_form([d,[[A,1]],[[B,1]]]):-B mod A =:= 0,!.
true_form([d,[[A,1]],[]]):- A=\=0,!.
true_form([nd,[[A,1]],[[B,1]]]):-B mod A =\= 0,!.


false_form([=,[],[[_,1]]]) :- !.
false_form([=,[[_,1]],[]]) :- !.
false_form([less,[],[]]) :- !.
false_form([greater,[],[]]) :- !.
false_form([less,[],[[M,1]]]):-M<0,!.
false_form([greater,[],[[M,1]]]):-M>0,!.
false_form([less,[[M,1]],[]]):-M>0,!.
false_form([greater,[[M,1]],[]]):-M<0,!.
false_form([d,[[A,1]],[[B,1]]]):-B mod A =\= 0,!.
false_form([nd,[[A,1]],[[B,1]]]):-B mod A =:= 0,!.
false_form([nd,[[A,1]],[]]):- A=\=0,!.






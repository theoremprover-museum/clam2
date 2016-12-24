/*
 * @(#)$Id: cooper.pl,v 1.14 2005/05/06 19:26:07 smaill Exp $
 *
 * $Log: cooper.pl,v $
 * Revision 1.14  2005/05/06 19:26:07  smaill
 * take out check_time_limit (dealt with by sictus timing module);
 *
 * Revision 1.13  1998/07/27 12:13:52  img
 * Dialect support
 *
 * Revision 1.12  1997/05/12 11:12:59  img
 * Revised implementation of true and false; now encoded via 0=0 and 0=1.  NB VOID is no longer an atomic proposition.
 *
 * Revision 1.11  1997/05/12 10:06:38  img
 * Elimination of negation of false added to removed incompleteness
 *
 * Revision 1.10  1997/05/09 09:29:25  img
 * Abstract div/3 to dialect-support.
 *
 * Revision 1.9  1997/05/08 12:19:06  img
 * Extended Presburger
 *
 * Revision 1.8  1997/05/07 18:31:35  img
 * Quantification over pnat and int supported.
 *
 * Revision 1.7  1997/05/06 15:14:12  img
 * tidy up
 *
 * Revision 1.6  1997/05/06 15:10:59  img
 * drop append in favour of cons
 *
 * Revision 1.5  1997/05/06 15:07:59  img
 * eliminate =..
 *
 * Revision 1.4  1997/05/06 13:21:09  img
 * cooper/2 added.
 *
 * Revision 1.3  1997/05/06 10:52:51  img
 * Tidied up code; normal/_ renamed to prenex_dnf (does not require
 * Presburger syntax)
 *
 * Revision 1.14  1997/01/11 18:13:55  img
 * more improvements, cut choice points to save memort
 *
 * Revision 1.13  1997/01/10 11:39:36  img
 * Cooper restricted to NATURAL NUMBERS
 *
 * Revision 1.12  1997/01/10 01:20:28  img
 * better check_time_limit
 *
 * Revision 1.11  1997/01/10 00:29:59  img
 * fast and working; added LOOK ODD marker
 *
 * Revision 1.10  1997/01/10 00:26:42  img
 * fast and working (???)
 *
 * Revision 1.9  1997/01/10 00:12:16  img
 * big speedups putting cut in f_infty (???)
 *
 * Revision 1.8  1997/01/10 00:01:00  img
 * more improvements
 *
 * Revision 1.7  1997/01/09 23:48:44  img
 * c_isolate improvements
 *
 * Revision 1.6  1997/01/09 23:44:41  img
 * c_formulas_lcm improvements
 *
 * Revision 1.5  1997/01/09 23:41:55  img
 * cm_normalize improvements
 *
 * Revision 1.4  1997/01/09 23:29:56  img
 * redundant calls to atomic_formula/1 removed
 *
 * Revision 1.3  1997/01/09 23:23:26  img
 * simple speed-ups; remove specialization to naturals
 *
 * Revision 1.2  1997/01/09 23:20:31  img
 * added header
 */

% ***************************************************************
%  Cooper's decision procedure for Presburger Integer Arithmetic
%
%             Written by Predrag Janicic, 1996.
%         Mathematical Reasoning Group (DReaM Group)
%           Department of Artificial Intelligence 
%                 University of Edinburgh
% ***************************************************************

% cooper(Input,yes) iff Input is PA and true; cooper(Input,no) iff
% Input is PA and flase;  Otherwise, cooper/2 fails.  Assumes that the
% variables are standardized apart according to definition of
% renaming_variables/2.
cooper(Input,Flag) :-
    presb_formula(Input),			% Presburger
    to_basic_presburger(Input,F1),
    renaming_variables(F1,F2),
    integer_only_presburger(F2,F22),
    to_prenex(F22,F3),				% Prenex NF
    (cooper(F3) -> Flag = yes; Flag = no).
cooper_extended(Input,Flag) :-
    presb_formula_extended(Input),		% Presburger with minus,p
    to_basic_presburger(Input,F1),
    renaming_variables(F1,F2),
    integer_only_presburger(F2,F22),
    to_prenex(F22,F3),				% Prenex NF
    (cooper(F3) -> Flag = yes; Flag = no).

% cooper(+Input) succeds if Input is LPA theorem, and fails if not.
% Input has to be basic Presburger formula in prenex normal form.
% (NB.  VOID and {TRUE} are not atomic formulae of this syntax.)
cooper(Formula) :-
    impl_elim(Formula,F3),
    convert(F3,F4),
    move_neg(F4,F5),
    int_la_neg_elim(F5,F6),
    int_leq_geq_elim(F6,F7),
    dp_cooper(F7).

/* this operates over the integers */
dp_cooper(Formula) :-
    quant_free(Formula),!,
    move_neg(Formula,F1),
    int_la_neg_elim(F1,F2),
    simplify_formula(F2,F4),
    true_form(F4).
dp_cooper(Formula):-
    c_elim_quant(Formula,F1),
    dp_cooper(F1).
	

% ********************************************************
%  This is a section for elimination of innermost
%           quantifier of a formula
% 
% ********************************************************

c_elim_quant(Formula,Formula) :- quant_free(Formula),!.
c_elim_quant(Va:int#F2,Eformula):-
    quant_free(F2),!,
    move_neg(F2,F3),   			      
    int_la_neg_elim(F3,F66),
    simplify_formula(F66,F6),
    c_eliminate(Va,F6,F7),
    simplify_formula(F7,Eformula).
c_elim_quant(Va:int=>F2,F9=>void):-
    quant_free(F2),!,
    move_neg(F2=>void,F4),
    int_la_neg_elim(F4,F77),
    simplify_formula(F77,F7),
    c_eliminate(Va,F7,F8),
    simplify_formula(F8,F9).
c_elim_quant(Va:int=>F,Va:int=>E):-
    !,c_elim_quant(F,E).
c_elim_quant(Va:int#F,Va:int#E):-
    !,c_elim_quant(F,E).
c_elim_quant(_:pnat#_,_):-
    clam_internal_error('c_elim_quant/2: quantification over pnat not permitted.').
c_elim_quant(_:pnat=>_,_):-
    clam_internal_error('c_elim_quant/2: quantification over pnat not permitted.').
 
% ********************************************************
%  This is section for elimination of (existentialy
%       quantified) variable from formula
%     
% ********************************************************
c_eliminate(V,Formula,Vf_formula) :-
% inequation x>-1 could be added because we deal with Peano natural numbers,
% and this is a nice place to add this additional condition
%    F1=..[#,[greater,[[1,V]],[[-1,1]]],Formula],
    F1 = Formula,
    c_normalize(V,F1,L,F2),
    change_var(V,F2,F3),
    F4 = ([d,[[L,1]],[[1,V]]] # F3),
    f_infty(V,F4,F5),
    expand1(V,L,F5,F6),
    expand2(V,L,F4,F4,F7),
    la_reduction(F6 \ F7,Vf_formula).

%expand2(_,_,_,_,_) :-
%    check_time_limit,fail.
expand2(V,J,F0,F,Fe):- F0=[greater,[[1,V]],X],!,
		      make_disj(V,X,J,F,Fe).
expand2(V,_,F0,_,[less,[],[]]) :- atomic_formula(F0),
	                        not(F0=[greater,[[1,V]],_]),!.

expand2(V,J,F0,F,Fe):-functor(F0,C,_),
	              conj_or_disj(C),!,
		      arg(1,F0,F1),
		      arg(2,F0,F2),
		      expand2(V,J,F1,F,Fe1),
		      expand2(V,J,F2,F,Fe2),
		      la_reduction(Fe1 \ Fe2,Fe). /* LOOKS ODD, BUT I THINK ITS OK */

make_disj(V,X,1,F,Fe):-!,subst_var2(V,X,1,F,Fe).
make_disj(V,X,J,F,Fe):-J>1,
	               subst_var2(V,X,J,F,Fe1),
		       J1 is J-1,
		       make_disj(V,X,J1,F,Fe2),
		       Fe3=..[\,Fe1,Fe2],
		       la_reduction(Fe3,Fe).


subst_var2(V,X,J,[R,L1,L2],Fj):- !,
    subst_var3(V,X,J,L1,L3),
    subst_var3(V,X,J,L2,L4),
    simplify_af([R,L3,L4],Fj).
subst_var2(V,X,J,F1#F2,Fj):-
    subst_var2(V,X,J,F1,F1j),
    subst_var2(V,X,J,F2,F2j),
    la_reduction(F1j#F2j,Fj).
subst_var2(V,X,J,F1\F2,Fj):-
    subst_var2(V,X,J,F1,F1j),
    subst_var2(V,X,J,F2,F2j),
    la_reduction(F1j\F2j,Fj).



subst_var3(_,_,_,[],[]) :- !.
subst_var3(V,X,J,[[_,V]|L],L1):-
    !,append(X,[[J,1]],X1),
    subst_var3(V,X,J,L,L2),
    append(X1,L2,L1).
subst_var3(V,X,J,[[H,U]|L],[[H,U]|L1]):- subst_var3(V,X,J,L,L1).

expand1(V,1,F,Fe):-!,subst_var(V,1,F,Fe).
expand1(V,J,F,Fe):-J>1,
	           subst_var(V,J,F,F1),
		   J1 is J-1,
		   expand1(V,J1,F,F2),
		   la_reduction(F1 \ F2,Fe).


subst_var(V,J,[R,X,Y],Fj):-!,
		     subst_var1(V,J,X,X1),
		     subst_var1(V,J,Y,Y1),
		     Fj1=[R,X1,Y1],
		     simplify_af(Fj1,Fj).
subst_var(V,J,F,Fj):-functor(F,C,_),
                     conj_or_disj(C),!,
		     arg(1,F,F1),
		     arg(2,F,F2),
		     subst_var(V,J,F1,F1j),
		     subst_var(V,J,F2,F2j),
		     Fj1=..[C,F1j,F2j],
		     la_reduction(Fj1,Fj).



subst_var1(_,_,[],[]) :- !.
subst_var1(V,J,[[_,V]|L],[[J,1]|L1]):-!,subst_var1(V,J,L,L1).
subst_var1(V,J,[[H,U]|L],[[H,U]|L1]):-subst_var1(V,J,L,L1).



f_infty(V,F,Fi):-functor(F,C,_),
	         conj_or_disj(C),!,
		 arg(1,F,F1),
		 arg(2,F,F2),
		 f_infty(V,F1,F1i),
		 f_infty(V,F2,F2i),
		 Fi1=..[C,F1i,F2i],
		 la_reduction(Fi1,Fi).

f_infty(V,[less,[[_,V]],_],[=,[],[]]) :- !.   % [=,[],[]] == TRUE

f_infty(V,[greater,[[_,V]],_],[less,[],[]]) :- !. % FALSE

/* f_infty(_,F,F) :- F=[d,_,_];F=[nd,_,_],!.  ALREADY ATOMIC */

f_infty(_,F,F):-atomic_formula(F).


change_var(V,[R,X,Y],F1):- !,
		    change_var1(V,X,X1),
		    change_var1(V,Y,Y1),
		    F1=[R,X1,Y1].

change_var(V,F,F1):-functor(F,C,_),
	            conj_or_disj(C),!,
		    arg(1,F,Ff1),
		    arg(2,F,Ff2),
		    change_var(V,Ff1,Ff11),
		    change_var(V,Ff2,Ff21),
		    F1=..[C,Ff11,Ff21].

change_var1(_,[],[]) :- !.
change_var1(V,[[_,V]|L],[[1,V]|L1]):-!,change_var1(V,L,L1).
change_var1(V,[[H,U]|L],[[H,U]|L1]):-change_var1(V,L,L1).


c_take_value(V,[=,[[_,V]],X],X):-!.
c_take_value(V,Formula,X):-functor(Formula,C,_),
	                   conj_or_disj(C),
	                   arg(1,Formula,F1),
		           c_take_value(V,F1,X),!.

c_take_value(V,Formula,X):-functor(Formula,C,_),
	                   conj_or_disj(C),
		           arg(2,Formula,F2),
		           c_take_value(V,F2,X),!.


c_elim_by_eq(V,Formula,Vf_formula):-c_take_value(V,Formula,Vvalue),
	                            c_substitute(V,Vvalue,Formula,Vf_formula).


c_substitute(V,_,Formula,Vf):-
	                    Formula=[R,X,Y],
	                    c_subst(V,Vvalue,X,X1),
		            c_subst(V,Vvalue,Y,Y1),
		            simplify_term(X,X1),
		            simplify_term(Y,Y1),
			    Vf=[R,X1,Y1].

c_substitute(V,Vvalue,Formula,Vf_formula):-Formula=[R,[[_,V]],Y],
                                         negate(Vvalue,V1),
					 append(Y,V1,Y1),
					 simplify_term(Y1,Y2),
	                                 Vf_formula=[R,[],Y2].

c_substitute(V,Vvalue,F1 # F2,Vf_formula):-
    c_substitute(V,Vvalue,F1,V1),
    c_substitute(V,Vvalue,F2,V2),
    la_reduction(V1 # V2,Vf_formula).  

c_subst(_,_,[],[]) :- !.
c_subst(V,Vvalue,[[_,V]|L],L1):-append(Vvalue,L,Lv),
	                      simplify_term(Lv,L1).


c_normalize(V,Formula,L1,Nformula):-c_isolate(V,Formula,Vformula),
	                           c_formulas_lcm(Vformula,V,L),
				   cm_normalize(V,Vformula,L,Nformula),
				   abs(L,L1).
cm_normalize(_,Formula,_,Formula):- Formula=[_,[],_],!.
cm_normalize(V,Formula,L,Nformula):-
    Formula=[d,[[X,1]],Y],
    occ(V,Y),!,
    take_mc(V,Y,M),
    div(M1, L, M),
    abs(M1,M2),
    X1 is M2*X,
    multi(M1,Y,Y1),
    Nformula=[d,[[X1,1]],Y1].

cm_normalize(_,Formula,_,Formula):- Formula=[d,[[_,1]],_],!.
cm_normalize(V,Formula,L,Nformula):-
    Formula=[nd,[[X,1]],Y],
    occ(V,Y),!,
    take_mc(V,Y,M),
    div(M1, L, M),
    abs(M1,M2),
    X1 is M2*X,
    multi(M1,Y,Y1),
    Nformula=[nd,[[X1,1]],Y1].

cm_normalize(_,Formula,_,Formula):- Formula=[nd,[[_,1]],_],!.
cm_normalize(V,Formula,L,Nformula):-
    Formula=[R,[[M,V]],Y],!,
    div(M1, L, M),
    multi(M1,Y,Y1),
    Nformula=[R,[[L,V]],Y1].
cm_normalize(V,Formula,L,Nformula):-
    functor(Formula,C,_),
    conj_or_disj(C),
    arg(1,Formula,F1),
    arg(2,Formula,F2),
    cm_normalize(V,F1,L,N1),
    cm_normalize(V,F2,L,N2),
    Nformula=..[C,N1,N2].

c_formulas_lcm(Formula,_,1):- Formula=[_,[],_],!.
c_formulas_lcm(Formula,V,1):-
    Formula=[R,[[_,U]],_], not(V=U),not(R=d),not(R=nd),!.
c_formulas_lcm(Formula,V,L):-
    Formula=[_,[[L1,V]],_], abs(L1,L),!.
c_formulas_lcm(Formula,V,L):-
    Formula=[d,[[_,1]],I], occ(V,I),!,
    take_mc(V,I,L1), abs(L1,L).
c_formulas_lcm(Formula,_,1):- Formula=[d,[[_,1]],_],!.
c_formulas_lcm(Formula,V,L):-
    Formula=[nd,[[_,1]],I], occ(V,I),!,
    take_mc(V,I,L1), abs(L1,L).
c_formulas_lcm(Formula,_,1):- Formula=[nd,[[_,1]],_],!.
c_formulas_lcm(Formula,V,L):-
    functor(Formula,C,_), conj_or_disj(C),!,
    arg(1,Formula,F1), arg(2,Formula,F2),
    c_formulas_lcm(F1,V,L1),
    c_formulas_lcm(F2,V,L2),
    abs(L1,L1p),abs(L2,L2p),
    c_lcm(L1p,L2p,L).


take_mc(_,[],0) :- !.
take_mc(V,[H|_],C):-H=[C,V], !.
take_mc(V,[_H|L],C):-take_mc(V,L,C).


c_lcm(A,B,C):-c_gcd(A,B,D),div(C, A*B, D).

c_gcd(A,B,A):-A=B,!.
c_gcd(A,B,C):-A>B,!,D is A mod B, ((D=:=0,C=B);c_gcd(D,B,C)),!.
%c_gcd(A,B,C):-A>B,D is A mod B, D=\=0,c_gcd(D,B,C),!.
c_gcd(A,B,C):-A<B,!,D is B mod A, ((D=:=0,!,C=A);c_gcd(D,B,C)),!.
%c_gcd(A,B,C):-A<B,D is B mod A,D=\=0,c_gcd(D,B,C).

c_isolate(_,Formula,Formula):- Formula=[d,_,_],!.
c_isolate(_,Formula,Formula):- Formula=[nd,_,_],!.
c_isolate(V,[R,X,Y],If):- !,
    negate(X,X1),
    append(X1,Y,Y1),
    simplify_term(Y1,Y2),
    c_take(V,Y2,X2,Y3),
    negate(X2,X3),
    ((X3=[] -> If=[R,X3,Y3];
      ((X3=[[M,V]], M>0) -> If=[R,X3,Y3];
       ((X3=[[M,V]],
	 M<0,
	 negate(X3,X4),
	 negate(Y3,Y4),
	 neg0(R,R1)) -> If=[R1,X4,Y4])))).
c_isolate(V,Formula,If):-functor(Formula,C,_),
	                 conj_or_disj(C),!,
	                 arg(1,Formula,F1),
		         arg(2,Formula,F2),
		         c_isolate(V,F1,If1),
		         c_isolate(V,F2,If2),
		         If=..[C,If1,If2].

c_take(_,[],[],[]) :- !.
c_take(V,[H|L],X,L):-H=[_,V],!,X=[H].
c_take(V,[H|L],X,[H|L1]):-c_take(V,L,X,L1).



% ********************************************************
%  This is section for elimination of negations from
%      Presburger formulae written in LA syntax
% ********************************************************
int_la_neg_elim(Formula,Formula):-atomic_formula(Formula),!.
int_la_neg_elim([geq,X,Y]=>void,[less,X,Y]):- !.
int_la_neg_elim([leq,X,Y]=>void,[greater,X,Y]):- !.
int_la_neg_elim([greater,X,Y]=>void,[less,X,Y2]):- !,
    simplify_term([[1,1]|Y],Y2).
% ***** int_la_neg_elim([greater,X,Y]=>void) = [less,X,[[1,1]|Y]]

int_la_neg_elim([less,X,Y]=>void,[greater,X2,Y]):- !,
    simplify_term([[1,1]|X],X2).
% ***** int_la_neg_elim([less,X,Y]=>void) = [greater,[[1,1]|X],Y]

int_la_neg_elim([=,X,Y]=>void,[less,X,Y] \ [greater,X,Y]):- !.
% ***** int_la_neg_elim([=,X,Y]=>void) = [less,X,Y]\[greater,X,Y]

int_la_neg_elim([d,X,Y]=>void,[nd,X,Y]):- !.
% ***** int_la_neg_elim([d,X,Y]=>void) = [nd,X,Y]

int_la_neg_elim([nd,X,Y]=>void,[d,X,Y]):- !.
% ***** int_la_neg_elim([nd,X,Y]=>void) = [d,X,Y]

int_la_neg_elim(Va:Type#F,Va:Type#N):-
    !,int_la_neg_elim(F,N).
int_la_neg_elim(Va:Type=>F,Va:Type=>N):-
    !,int_la_neg_elim(F,N).
% ***** int_la_neg_elim(x:int=>F) = x:int=>int_la_neg_elim(F)
% ***** int_la_neg_elim(x:int#F)  = x:int#int_la_neg_elim(F)

int_la_neg_elim((F2=>void)=>void,La_neg_elim):- !,
    int_la_neg_elim(F2,La_neg_elim).
% ***** int_la_neg_elim((F=>void)=>void) = int_la_neg_elim(F).
int_la_neg_elim(F1=>void,N11 => void):-
    functor(F1,C,_),
    conj_or_disj(C),!,
    arg(1,F1,F11),
    arg(2,F1,F12),
    int_la_neg_elim(F11,N1),
    int_la_neg_elim(F12,N2),
    N11=..[C,N1,N2].
% ***** int_la_neg_elim((F1#F2)=>void) = int_la_neg_elim(F1)#la_neg_elim(F2).
% ***** int_la_neg_elim((F1\F2)=>void) = int_la_neg_elim(F1)\la_neg_elim(F2).

int_la_neg_elim(Formula,La_neg_elim):-functor(Formula,C,_),
	                              conj_or_disj(C),!,
                                      arg(1,Formula,F1),
	                              arg(2,Formula,F2),
                                      int_la_neg_elim(F1,N1),
			              int_la_neg_elim(F2,N2),
			              La_neg_elim=..[C,N1,N2].
% ***** int_la_neg_elim(F1\F2) = int_la_neg_elim(F1)\int_la_neg_elim(F2)
% ***** int_la_neg_elim(F1#F2) = int_la_neg_elim(F1)#int_la_neg_elim(F2)


    

% ********************************************************
%  This is a section for elimination of relations
% "leq" and "geq" in Presburger Integer Arithmetic
% ********************************************************

% ***** elimination of negations (la_neq_elim) should be executed before this
int_leq_geq_elim([greater,A,B],[greater,A,B]):- !.
int_leq_geq_elim([less,A,B],   [less,A,B]   ):- !.

int_leq_geq_elim([=,X,Y],[greater,X1,Y] # [less,X,Y1]):-!,
    append(X,[[1,1]],X1),
    append(Y,[[1,1]],Y1).
% there is a version of the algorithm that deals with
% equality, for that version this is unnesecary

int_leq_geq_elim([leq,X,Y],[less,X,Y2]):- !,
    simplify_term([[1,1]|Y],Y2).

int_leq_geq_elim([geq,X,Y],[greater,X,Y2]):- !,
    simplify_term([[-1,1]|Y],Y2).

int_leq_geq_elim(Va:Type#F,Va:Type#E):-
    !,int_leq_geq_elim(F,E).
int_leq_geq_elim(Va:Type=>F,Va:Type=>E):-
    !,int_leq_geq_elim(F,E).
% ***** leq_geq_elim(x:int=>F) = x:int=>leq_geq_elim(F)
% ***** leq_geq_elim(x:int#F)  = x:int#leq_geq_elim(F)


int_leq_geq_elim(Formula,Eformula):-functor(Formula,C,_),
	                            conj_or_disj(C),
                                    arg(1,Formula,F1),
	                            arg(2,Formula,F2),
                                    int_leq_geq_elim(F1,E1),
			            int_leq_geq_elim(F2,E2),
			            Eformula=..[C,E1,E2].
% ***** leq_geq_elim(F1\F2) = leq_geq_elim(F1)\leq_geq_elim(F2)
% ***** leq_geq_elim(F1#F2) = leq_geq_elim(F1)#leq_geq_elim(F2)










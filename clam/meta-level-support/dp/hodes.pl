% **********************************************************
%  Hodes' decision procedure for Presburger Real Arithmetic
%             (for non-negative real numbers?) 
%
%             Written by Predrag Janicic, 1996.
%         Mathematical Reasoning Group (DReaM Group)
%           Department of Artificial Intelligence 
%                 University of Edinburgh
% **********************************************************


% **************************************************************
%  This is a section for converting Presburger formula in CLaM 
%  to (prenex) disjunctive normal form in a specific format
%    (we will call it LA sintax (linear arithmetic syntax)
% **************************************************************

%lnormal(Formula,Lnormal):-presb_formula(Formula),
                %          renaming_variables(Formula,Rformula),
	        %          to_prenex(Rformula,Prenex),
		%	   impl_elim(Prenex,Impl_free),
		%	   move_neg(Impl_free,Moved_neg),
		%	   convert(Moved_neg,Lnormal1),
		%	   la_neg_elim(Lnormal1,Lnormal2),
		%	   leq_geq_elim(Lnormal2,Lnormal3),
		%	   to_dnf(Lnormal3,Lnormal).


% hodes(Input) succeds if Input is theorem of Presburger real arithmetic
% and fails if not
% Formula Input has to be in basic Presburger arithmetic and in a
% prenex normal form


hodes(Formula):-impl_elim(Formula,F1),
		move_neg(F1,F2),
		convert(F2,F3),
		la_neg_elim(F3,F4),
                dp_hodes(F4).

dp_hodes(Formula):-quant_free(Formula),!,
                   move_neg(Formula,F1),
                   la_neg_elim(F1,F2),
	           leq_geq_elim(F2,F3),
%	           nl,write('input quant-free formula: '),write(F3),
	           simplify_formula(F3,F4),
%	           nl,write('simplificated: '),write(F4),
	           true_form(F4).

dp_hodes(Formula):-
%	           nl,write('input quantified formula: '),write(Formula),
	           elim_quant(Formula,F1),
	           dp_hodes(F1).
	

% ********************************************************
%  This is a section for elimination of innermost
%           quantifier of a formula
% 
% ********************************************************

elim_quant(Formula,Formula):- quant_free(Formula),!.

elim_quant(Va:_#F2,Eformula):-
    quant_free(F2),!,
			% F2p=..[#,[geq,[[1,Va]],[]],F2],
			   % we deal just with non-negative real numbers
			      move_neg(F2,F3),
   		              la_neg_elim(F3,F4),
	   		      leq_geq_elim(F4,F5),
	                      to_dnf(F5,F6),
 			      eliminate(Va,F6,F7),
			      simplify_formula(F7,Eformula).


elim_quant(Va:_=>F2,Eformula):-
    quant_free(F2),!,
    F3=..[=>,F2,void],
			  % F3p=..[#,[geq,[[1,Va]],[]],F3],
			  % we deal just with non-negative real numbers 
           		      move_neg(F3,F4),
                              la_neg_elim(F4,F5),
			      leq_geq_elim(F5,F6),
			      to_dnf(F6,F7),
			      eliminate(Va,F7,F8),
			      simplify_formula(F8,F9),
			      Eformula=..[=>,F9,void].
	

elim_quant(Va:F1,Eformula):-
    quanti(Q),
    arg(2,F1,F2),
    elim_quant(F2,E1),                    
    E2=..[Q,pnat,E1],
    Eformula=..[:,Va,E2].


% ********************************************************
%  This is section for elimination of (existentialy
%       quantified) variable from formula
%     
% ********************************************************


eliminate(V,F1 \ F2,Vf_formula) :- !,
    eliminate(V,F1,Vf_f1),
    eliminate(V,F2,Vf_f2),
    la_reduction(Vf_f1 \ Vf_f2,Vf_formula).

eliminate(V,Formula,Vf_formula):-
    normalize(V,Formula,F2),
    solve(V,F2,Vf_formula1),
    la_reduction(Vf_formula1,Vf_formula).


solve(V,Formula,Formula):-not(v_occ(V,Formula)),!.

solve(V,Formula,Vf_formula):- eq_occ(V,Formula),!,
	                     elim_by_eq(V,Formula,Vf_formula).

solve(V,Formula,Vf_formula):-
	                     less_elim(V,Formula,Formula,Vf_formula1),
			     greater_elim(V,Vf_formula1,Vf_formula).


greater_elim(V,Formula,Formula):- atomic_formula(Formula),
	                          not(Formula=[greater,[[_,V]],_]).
	                 
greater_elim(V,Formula,Vf):-Formula=[greater,[[_,V]],_],!,
	         	    Vf=[=,[],[]].

greater_elim(V,Formula,Vf):-functor(Formula,#,_),
	                    arg(1,Formula,F1),
		            arg(2,Formula,F2),
	                    greater_elim(V,F1,Vf1),
	                    greater_elim(V,F2,Vf2),
                            Vf_formula1=..[#,Vf1,Vf2],
			    la_reduction(Vf_formula1,Vf).


less_elim(V,A,_,A):-atomic_formula(A),not(A=[less,[[_,V]],_]).
	                 
less_elim(V,A,Formula,B):-A=[less,[[_,V]],_],!,
	         	  pairing(V,A,Formula,B).

less_elim(V,A,Formula,Vf_formula):-functor(A,#,_),
	  	                   arg(1,A,F1),
			           arg(2,A,F2),
	                           less_elim(V,F1,Formula,Vf1),
				   less_elim(V,F2,Formula,Vf2),
			           Vf_formula1=..[#,Vf1,Vf2],
		                   la_reduction(Vf_formula1,Vf_formula).

pairing(V,A,Formula,[=,[],[]]):-A=[less,[[_,V]],_],
	                        atomic_formula(Formula),
	                        not(Formula=[greater,[[_,V]],_]).

pairing(V,A,Formula,Vf):-A=[less,[[M,V]],X],
	                 Formula=[greater,[[M,V]],Y],
                         Y2=Y,
			 Vf1=[less,Y2,X],
			 simplify_af(Vf1,Vf). 

pairing(V,A,Formula,Vf):-A=[less,[[_,V]],_],
                         functor(Formula,#,_),
			 arg(1,Formula,F1),
			 arg(2,Formula,F2),
			 pairing(V,A,F1,Vf1),
			 pairing(V,A,F2,Vf2),
			 Vf=..[#,Vf1,Vf2].

	               

v_occ(V,Formula):- Formula=[_,F1,_],
	          occ(V,F1),!.

v_occ(V,Formula):-
                  Formula=[_,_,F2],
		  occ(V,F2).

v_occ(V,Formula):-functor(Formula,#,_),
	          arg(1,Formula,F1),
		  v_occ(V,F1),!.
v_occ(V,Formula):-functor(Formula,#,_),
		  arg(2,Formula,F2),
                  v_occ(V,F2).


eq_occ(V,[=,[[_,V]],_]) :- !.
eq_occ(V,Formula):-functor(Formula,#,_),
	           arg(1,Formula,F1),
		   eq_occ(V,F1),!.

eq_occ(V,Formula):-functor(Formula,#,_),
		   arg(2,Formula,F2),
		   eq_occ(V,F2).

take_value(V,[=,[[_,V]],X],X):-!.
take_value(V,Formula,X):-functor(Formula,#,_),
	                 arg(1,Formula,F1),
		         take_value(V,F1,X),!.

take_value(V,Formula,X):-functor(Formula,#,_),
		         arg(2,Formula,F2),
		         take_value(V,F2,X),!.

elim_by_eq(V,Formula,Vf_formula):-take_value(V,Formula,Vvalue),
	                          substitute(V,Vvalue,Formula,Vf_formula).


substitute(V,_,Formula,Formula):-atomic_formula(Formula),
	                              not(Formula=[_,[[_,V]],_]).

substitute(V,Vvalue,Formula,Vf_formula):-Formula=[R,[[_,V]],Y],!,
                                         negate(Vvalue,V1),
					 append(Y,V1,Y1),
					 simplify_term(Y1,Y2),
	                                 Vf_formula=[R,[],Y2].

substitute(V,Vvalue,Formula,Vf_formula):-functor(Formula,#,_),
	                                 arg(1,Formula,F1),
				         arg(2,Formula,F2),
				         substitute(V,Vvalue,F1,V1),
				         substitute(V,Vvalue,F2,V2),
				         Vf_formula1=..[#,V1,V2],
					 la_reduction(Vf_formula1,Vf_formula).  


normalize(V,Formula,Nformula):-isolate(V,Formula,Vformula),
	                       formulas_lcm(Vformula,V,L),
	                       m_normalize(Vformula,L,Nformula).


m_normalize(Formula,_,Formula):-
	                        Formula=[_,[],_],!.

m_normalize(Formula,L,Nformula):-
    Formula=[R,[[M,V]],Y],!,
    div(M1, L, M),
    multi(M1,Y,Y1),
    Nformula=[R,[[L,V]],Y1].

m_normalize(Formula,L,Nformula):-functor(Formula,#,_),
	                         arg(1,Formula,F1),
			         arg(2,Formula,F2),
			         m_normalize(F1,L,N1),
			         m_normalize(F2,L,N2),
			         Nformula=..[#,N1,N2].


formulas_lcm(Formula,_,1):-
	                   Formula=[_,[],_],!.

formulas_lcm(Formula,V,1):- Formula=[_,[[_,U]],_],
			   not(V=U).

formulas_lcm(Formula,V,L):-
	                   Formula=[_,[[L,V]],_],!.

formulas_lcm(Formula,V,L):-functor(Formula,#,_),!,
	                   arg(1,Formula,F1),
			   arg(2,Formula,F2),
			   formulas_lcm(F1,V,L1),
			   formulas_lcm(F2,V,L2),
			   lcm(L1,L2,L).


lcm(A,B,C):-gcd(A,B,D),div(C, A*B, D).

gcd(A,B,A):-A=B,!.
gcd(A,B,C):-A>B,D is A mod B,D=:=0,C=B,!.
gcd(A,B,C):-A>B,D is A mod B,D=\=0,gcd(D,B,C),!.
gcd(A,B,C):-A<B,D is B mod A,D=:=0,C=A,!.
gcd(A,B,C):-A<B,D is B mod A,D=\=0,gcd(D,B,C),!.



isolate(V,Formula,If):-functor(Formula,#,_),!,
	               arg(1,Formula,F1),
		       arg(2,Formula,F2),
		       isolate(V,F1,If1),
		       isolate(V,F2,If2),
		       If=..[#,If1,If2].

isolate(V,Formula,If):-
    Formula=[R,X,Y],
    negate(X,X1),
    append(X1,Y,Y1),
    simplify_term(Y1,Y2),
    take(V,Y2,X2,Y3),
    negate(X2,X3),
    ( X3=[] -> If=[R,X3,Y3];
      ((X3=[[M,V]], M>0) -> If=[R,X3,Y3];
       ((X3=[[M,V]], M<0) ->
	(negate(X3,X4),
	 negate(Y3,Y4),
	 neg0(R,R1),
	 If=[R1,X4,Y4])))).


take(_,[],[],[]) :- !.
take(V,[H|L],X,L):-H=[_,V],!,X=[H].
take(V,[H|L],X,[H|L1]):-take(V,L,X,L1).



% ********************************************************
%  This is section for elimination of negations from
%      Presburger formulae written in LA syntax
% ********************************************************


la_neg_elim(Formula,Formula):-atomic_formula(Formula),!.

la_neg_elim([O,X,Y]=>void,La_neg_elim):-
    rel(O),!,
    neg_rel(O,O1),
    La_neg_elim=[O1,X,Y].
% ***** la_neg_elim([greater,X,Y]=>void) = [leq,X,Y]
% ***** la_neg_elim([less,X,Y]=>void)    = [geq,X,Y]
% ***** la_neg_elim([geq,X,Y]=>void)     = [less,X,Y]
% ***** la_neg_elim([leq,X,Y]=>void)     = [greater,X,Y]


la_neg_elim([=,X,Y]=>void,La_neg_elim):-
    !,
    La_neg_elim=..[\,[greater,X,Y],[less,X,Y]].
% ***** la_neg_elim([=,X,Y]=>void) = [greater,X,Y]\[less,X,Y]

la_neg_elim(void=>void,[=,[],[]]) :- !.

la_neg_elim(Va:F1,La_neg_elim):-
    functor(F1,Q,_),
    quanti(Q),!,
    arg(2,F1,F2),
    la_neg_elim(F2,N1),
    N2=..[Q,pnat,N1],
    La_neg_elim=..[:,Va,N2].
% ***** la_neg_elim(x:pnat=>F) = x:pnat=>la_neg_elim(F)
% ***** la_neg_elim(x:pnat#F)  = x:pnat#la_neg_elim(F)


la_neg_elim(Formula,La_neg_elim):-functor(Formula,C,_),
	                          conj_or_disj(C),!,
                                  arg(1,Formula,F1),
	                          arg(2,Formula,F2),
                                  la_neg_elim(F1,N1),
			          la_neg_elim(F2,N2),
			          La_neg_elim=..[C,N1,N2].
% ***** la_neg_elim(F1\F2) = la_neg_elim(F1)\la_neg_elim(F2)
% ***** la_neg_elim(F1#F2) = la_neg_elim(F1)#la_neg_elim(F2)


la_neg_elim(Formula,La_neg_elim):-functor(Formula,=>,_),
	                          arg(1,Formula,F1),
			          not(F1=pnat),
			          arg(2,Formula,void),
			          functor(F1,=>,_),
			          arg(1,F1,F2),
			          arg(2,F1,void),
			          la_neg_elim(F2,La_neg_elim).

% ***** la_neg_elim((F=>void)=>void) = la_neg_elim(F).


la_neg_elim(F1=>void,La_neg_elim):-
    functor(F1,C,_),
    conj_or_disj(C),
    arg(1,F1,F11),
    arg(2,F1,F12),
    la_neg_elim(F11,N1),
    la_neg_elim(F12,N2),
    N11=..[C,N1,N2],
    La_neg_elim=..[=>,N11,void].		     
% ***** la_neg_elim((F1#F2)=>void) = la_neg_elim(F1)#la_neg_elim(F2).
% ***** la_neg_elim((F1\F2)=>void) = la_neg_elim(F1)\la_neg_elim(F2).




% ********************************************************
%  This is a section for elimination of relations
%             "leq" and "geq"
% ********************************************************

% ***** elimination of negations (la_neq_elim) should be executed before this

leq_geq_elim(Formula,Formula):-
	                       Formula=[R,_,_],
			       (R='=';R='greater';R='less'),!.

leq_geq_elim(Formula,Eformula):-
	                        Formula=[leq,X,Y],!,
				A=[=,X,Y],
				B=[less,X,Y],
                                Eformula=..[\,A,B].

leq_geq_elim(Formula,Eformula):-
	                        Formula=[geq,X,Y],!,
                                A=[=,X,Y],
				B=[greater,X,Y],
				Eformula=..[\,A,B].

leq_geq_elim(Formula,Eformula):-functor(Formula,':',_),
                                arg(1,Formula,Va),
	                        arg(2,Formula,F1),
		                functor(F1,Q,_),
			        quanti(Q),!,
			        arg(2,F1,F2),
			        leq_geq_elim(F2,E1),
			        E2=..[Q,pnat,E1],
			        Eformula=..[:,Va,E2].
% ***** leq_geq_elim(x:pnat=>F) = x:pnat=>leq_geq_elim(F)
% ***** leq_geq_elim(x:pnat#F)  = x:pnat#leq_geq_elim(F)


leq_geq_elim(Formula,Eformula):-functor(Formula,C,_),
	                        conj_or_disj(C),!,
                                arg(1,Formula,F1),
	                        arg(2,Formula,F2),
                                leq_geq_elim(F1,E1),
			        leq_geq_elim(F2,E2),
			        Eformula=..[C,E1,E2].
% ***** leq_geq_elim(F1\F2) = leq_geq_elim(F1)\leq_geq_elim(F2)
% ***** leq_geq_elim(F1#F2) = leq_geq_elim(F1)#leq_geq_elim(F2)








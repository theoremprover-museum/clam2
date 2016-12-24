/*
 * @(#)$Id: dnf.pl,v 1.7 2005/05/06 19:26:21 smaill Exp $
 *
 * $Log: dnf.pl,v $
 * Revision 1.7  2005/05/06 19:26:21  smaill
 * take out check_time_limit (dealt with by sictus timing module);
 *
 * Revision 1.6  1997/05/06 15:24:12  img
 * Removed redundant calls to move_neg/2.
 *
 * Revision 1.5  1997/05/06 13:20:38  img
 * Specific to PA
 *
 * Revision 1.4  1997/05/06 10:52:53  img
 * Tidied up code; normal/_ renamed to prenex_dnf (does not require
 * Presburger syntax)
 *
 * Revision 1.3  1997/02/20 15:00:18  img
 * move_neg improved; cut choice points to reduce memory consumption
 *
 * Revision 1.2  1997/01/14 10:37:02  img
 * Added headers, renamed substitute/4 to h_substitute/4.
 *
 * Revision 1.1  1997/01/14 10:23:54  img
 * Decision procedures.
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: dnf.pl,v 1.7 2005/05/06 19:26:21 smaill Exp $').

% ****************************************************************
%   This is program for converting Presburger Arithmetic Formula
%       into the (prenex) disjunctive-normal form
%            (The CLaM sytax is used)
%
%           Written by Predrag Janicic/Ian Green, 1996/7.
%       Mathematical Reasoning Group (DReaM Group)
%         Department of Artificial Intelligence 
%               University of Edinburgh
% ****************************************************************


/* prenex_dnf(+Input,-Output). Input is a PA formula.  Output is a
   formula in prenex disjunctive normal form equivalent to Input.  */
prenex_dnf(Formula,Normal):-
    renaming_variables(Formula,Rformula),
    to_prenex(Rformula,Prenex),			% Prenex NF
    impl_elim(Prenex,Impl_free),		% Eliminate =>
    move_neg(Impl_free,Moved_neg),		% Literal NF
    to_dnf(Moved_neg,Normal).			% DNF

% we assume that there are not two quantified variables with a same name
renaming_variables(Formula,Formula).


% *****************************************************
%  This is a section for converting Presburger formula
%              to prenex normal form
% *****************************************************

% to_prenex(Input,Output)
% Input=PA Formula
% Output=prenex normal form of Formula
quant_free(Formula):-atomic_formula(Formula),!.
quant_free(F1#F2):- quant_free(F1), quant_free(F2),!.
quant_free(F1\F2):- quant_free(F1), quant_free(F2),!.
quant_free(F1=>F2):- quant_free(F1), quant_free(F2),!.

to_prenex(Formula,Formula) :-
    atomic_formula(Formula),!.

/* The following two rules (dealing with conjunction and disjunction)
   assume that we do not have two quantified variables with a same
   name.  in this stage we assume that we do not have formulae like
   this: (x:pnat=>F1)#(x:pnat=>F2), so we can use following
   equivalences and we don't have to make renaming and we can apply
   the following rules without restrictions to form of formula F2 in
   next rule, etc.  in case of adding restrictions, this predicate
   should be changed.  */
to_prenex((V:T=>A) # B,V:T=>AB) :- !,to_prenex(A # B,AB).
to_prenex((V:T#A) # B,V:T#AB)   :- !,to_prenex(A # B,AB).
to_prenex((V:T=>A) \ B,V:T=>AB) :- !,to_prenex(A \ B,AB).
to_prenex((V:T#A) \ B,V:T#AB)   :- !,to_prenex(A \ B,AB).
to_prenex(B # (V:T=>A),V:T=>AB) :- !,to_prenex(B # A,AB).
to_prenex(B # (V:T#A),V:T#AB)   :- !,to_prenex(B # A,AB).
to_prenex(B \ (V:T=>A),V:T=>AB) :- !,to_prenex(B \ A,AB).
to_prenex(B \ (V:T#A),V:T#AB)   :- !,to_prenex(B \ A,AB).
to_prenex(V:T=>A,V:T=>AP)       :- !,to_prenex(A,AP).
to_prenex(V:T#A,V:T#AP)         :- !,to_prenex(A,AP).
to_prenex((V:T#A)=>B,V:T=>AB)   :- !,to_prenex(A=>B,AB).
to_prenex(B=>(V:T#A),V:T#BA)    :- !,to_prenex(B=>A,BA).
to_prenex((V:T=>A)=>B,V:T#AB)   :- !,to_prenex(A=>B,AB).
to_prenex(B=>(V:T=>A),V:T=>BA)  :- !,to_prenex(B=>A,BA).

to_prenex(A # B,Prenex_form):-			% RECURSE
    to_prenex(A,AP), to_prenex(B,BP),
    ((AP # BP) == (A # B) -> Prenex_form = (A # B);
     to_prenex(AP # BP,Prenex_form)).
to_prenex(A \ B,Prenex_form):-
    to_prenex(A,AP), to_prenex(B,BP),
    ((AP \ BP) == (A \ B) -> Prenex_form = (A \ B);
     to_prenex(AP \ BP,Prenex_form)).
to_prenex(A => B,Prenex_form):-
    to_prenex(A,AP), to_prenex(B,BP),
    ((AP => BP) == (A => B) -> Prenex_form = (A => B);
     to_prenex(AP => BP,Prenex_form)).

	
% *******************************************************************
% This is a section for converting a formula in prenex-normal form to
% (prenex) disjunctive normal form.
% Implications are to eliminated (except those concerning
% universal quantification and negation)
% *******************************************************************

% impl_elim(Input,Output)
% Input=formula in prenex normal form
% Output=implication free form

impl_elim(Formula,Formula) :- atomic_formula(Formula),!.
impl_elim(V:T=>A,V:T=>AA):- !,impl_elim(A,AA).
impl_elim(V:T#A,V:T#AA):- !,impl_elim(A,AA).
impl_elim(A \ B,AA \ BB) :- !,impl_elim(A,AA), impl_elim(B,BB).
impl_elim(A # B,AA # BB) :- !,impl_elim(A,AA), impl_elim(B,BB).
impl_elim(A=>void,AA=>void) :- !,impl_elim(A,AA).
impl_elim(A=>B,(AA=>void) \ BB):-
    impl_elim(A,AA), impl_elim(B,BB).

% ****************************************************
% This is a section which move negations to literals
% (it is the next step in making DNF)
% ****************************************************

% move_neg(Input,Output)
% Input=P.I.A.formula in prenex normal form without implications
% Output=formula with at most one negation close to atomic
% formulae. (aka literal normal form).

move_neg(Formula,Formula) :- atomic_formula(Formula),!.
move_neg(F1=>void,F1=>void):- atomic_formula(F1),!.
% ***** moved_neg(F=>void) = F=>void  (F is atomic formula)

move_neg((F2=>void)=>void,Moved_neg):- !,move_neg(F2,Moved_neg). 
% ***** moved_neg((F=>void)=>void) = moved_neg(F).
% ***** despite this rule, elimination of double negations
% ***** (probably :) ) has to be applied after "moving negations"

move_neg((F1\F2)=>void,Mn11 # Mn21):- !,
    move_neg(F1=>void,Mn11),
    move_neg(F2=>void,Mn21).
% ***** moved_neg((F1\F2)=>void) = (moved_neg(F1=>void))#(moved_neg(F2=>void))

move_neg((F1 # F2)=>void,Mn11 \ Mn21):- !,
    move_neg(F1=>void,Mn11),
    move_neg(F2=>void,Mn21).
% ***** moved_neg((F1#F2)=>void) = (moved_neg(F1)=>void)\(moved_neg(F2)=>void)

move_neg(V:T=>A,V:T=>AA):- !,move_neg(A,AA).
move_neg(V:T#A,V:T#AA):- !,move_neg(A,AA).
move_neg(A#B,AA#BB) :- !,move_neg(A,AA), move_neg(B,BB).
move_neg(A\B,AA\BB) :- !,move_neg(A,AA), move_neg(B,BB).
			     

% *****************************************
% This section eliminate double negations
% *****************************************
neg_elim(Formula,Formula):-atomic_formula(Formula) ,!.
neg_elim(F1=>void,F1=>void):- !, atomic_formula(F1).
% ***** neg_elim(F=>void) = F=>void  (F is atomic formula)

neg_elim(Va:F1,Neg_elim):-
    functor(F1,Q,_),
    quanti(Q),!,
    arg(2,F1,F2),
    neg_elim(F2,N1),
    N2=..[Q,pnat,N1],
    Neg_elim=..[:,Va,N2].
% ***** neg_elim(x:pnat=>F) = x:pnat=>neg_elim(F)
% ***** neg_elim(x:pnat#F)  = x:pnat#neg_elim(F)

neg_elim((F2=>void)=>void,Neg_elim):- !,
    neg_elim(F2,Neg_elim).			     
% ***** neg_elim((F=>void)=>void) = neg_elim(F).

neg_elim(F1=>void,Neg_elim):-
    functor(F1,C,_),
    conj_or_disj(C),
    arg(1,F1,F11),
    arg(2,F1,F12),
    neg_elim(F11,N1),
    neg_elim(F12,N2),
    N11=..[C,N1,N2],
    Neg_elim=..[=>,N11,void].		     
% ***** neg_elim((F1#F2)=>void) = neg_elim(F1)#neg_elim(F2).
% ***** neg_elim((F1\F2)=>void) = neg_elim(F1)\neg_elim(F2).
% ***** if "move negation" is used before, this clause is unnecessery

neg_elim(Formula,Neg_elim):-functor(Formula,C,_),
	                    conj_or_disj(C),!,
                            arg(1,Formula,F1),
	                    arg(2,Formula,F2),
                            neg_elim(F1,N1),
			    neg_elim(F2,N2),
			    Neg_elim=..[C,N1,N2].

% ***** neg_elim(F1\F2) = neg_elim(F1)\neg_elim(F2)
% ***** neg_elim(F1#F2) = neg_elim(F1)#neg_elim(F2)


% ******************************************************************
% This section converts formula into the disjunctive-normal form
%  (it is assumed that input formula is in prenex normal form,
%      so the first step is to skip all quantifiers
% also it is assumed that there is no implications and negations
%               are moved close to literals)
% ******************************************************************

% to_dnf(Input,Output)
% Input=P.I.A.formula in prenex normal form, without implications and
% with at most one negation close to atomic formulae
% Output=DNF form


to_dnf(Va:F1,Dnf):- 	              
    !,
    functor(F1,Q,_),
    arg(2,F1,F2),
    to_dnf(F2,D2),
    Dnf1=..[Q,pnat,D2],
    Dnf=..[:,Va,Dnf1].
% ***** dnf(x:pnat=>F) = x:pnat=>dnf(F)
% ***** dnf(x:pnat#F)  = x:pnat=>dnf(F)
 
to_dnf(Formula,Dnf):-
    dnf(Formula,Dnf).

% dnf(_,_) :- check_time_limit, fail.

dnf(Form1 \ Form2,F1 \ F2):-!,
    dnf(Form1,F1),
    dnf(Form2,F2).
% ***** dnf(F1\F2) = dnf(F1)\dnf(F2)


dnf(Form1 # Form2,Dnf):-!,
    dnf(Form1,F1),
    dnf(Form2,F2),
    (F1 = (F11 \ F12) ->
     (dnf(F11#F2,D11),
      dnf(F12#F2,D21),
      Dnf = (D11 \ D21));
     (F2 = (F21 \ F22) ->
      (dnf(F1 # F21, D11),
       dnf(F1 # F22, D21),
       Dnf = (D11 \ D21));
      (Dnf = (F1 # F2)))).
% ***** dnf(F1#F2) = dnf(F1)#dnf(F2)  (dnf(F1)<>A\B, dnf(F2)<>A\B) 
% ***** dnf((F1\F2)#F3) = dnf(dnf(F1)#F3)\dnf(dnf(F2)#F3)
% ***** dnf(F1#(F2\F3)) = dnf(F1#dnf(F2))\dnf(F1#dnf(F3))

dnf(Formula,Formula):-literal(Formula).
		  

% ******************************************************************
% This section converts formula into the conjunctive-normal form
%  (it is assumed that input formula is in prenex normal form,
%      so the first step is to skip all quantifiers
% also it is assumed that there is no implications and negations
%               are moved close to literals)
% ******************************************************************

% to_cnf(Input,Output)
% Input=P.I.A.formula in prenex normal form, without implications and
% with at most one negation close to atomic formulae
% Output=CNF form


to_cnf(Va:F1,Va:Cnf1):- !,
    functor(F1,Q,_),
    arg(2,F1,F2),
    to_cnf(F2,D2),
    Cnf1=..[Q,pnat,D2].
% ***** cnf(x:pnat=>F) = x:pnat=>cnf(F)
% ***** cnf(x:pnat#F)  = x:pnat=>cnf(F)
 
to_cnf(Formula,Cnf):-
    cnf(Formula,Cnf).


cnf(Form1 # Form2,F1 # F2):-
    cnf(Form1,F1),
    cnf(Form2,F2).
% ***** cnf(F1#F2) = cnf(F1)#cnf(F2)

cnf(Form1 \ Form2,Cnf):-
    cnf(Form1,F1),
    cnf(Form2,F2),
    (F1 = (F11 # F12) ->
     (cnf(F11 \ F2, D11),
      cnf(F12 \ F2, D21),
      Cnf = (D11 # D21));
     (F2 = (F21 # F22) -> 
      (cnf(F1 \ F21, D11),
       cnf(F1 \ F22, D21),
       Cnf = (D11 # D21)));
     (Cnf = (F1 \ F2))).
% ***** cnf(F1\F2) = cnf(F1)\cnf(F2)  (cnf(F1)<>A#B, cnf(F2)<>A#B) 
% ***** cnf((F1#F2)\F3) = cnf(cnf(F1)\F3)#cnf(cnf(F2)\F3)
% ***** cnf(F1\(F2#F3)) = cnf(F1\cnf(F2))#cnf(F1\cnf(F3))


cnf(Formula,Formula):-literal(Formula).

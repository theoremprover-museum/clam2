/*
 * @(#)$Id: cm1.pl,v 1.7 1999/02/25 18:15:42 img Exp $
 *
 * $Log: cm1.pl,v $
 * Revision 1.7  1999/02/25 18:15:42  img
 * map to integer only
 *
 * Revision 1.6  1998/01/19 12:13:12  img
 * Fix lpa_dp/2
 *
 * Revision 1.5  1997/05/07 18:31:30  img
 * Quantification over pnat and int supported.
 *
 * Revision 1.4  1997/05/06 15:21:26  img
 * lpa_dp/2 added
 *
 * Revision 1.3  1997/05/06 10:52:48  img
 * Tidied up code; normal/_ renamed to prenex_dnf (does not require
 * Presburger syntax)
 *
 * Revision 1.2  1997/02/20 14:57:45  img
 * faster code
 *
 * Revision 1.1  1997/01/14 10:23:48  img
 * Decision procedures.
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: cm1.pl,v 1.7 1999/02/25 18:15:42 img Exp $').

% ******************************************************************
%   Module 1 for communication between the proof planner CLaM and
%      decision procedure for Presburger Integer Arithmetic
%
%             Written by Predrag Janicic, 1996.
%         Mathematical Reasoning Group (DReaM Group)
%           Department of Artificial Intelligence 
%                 University of Edinburgh
% ****************************************************************

lpa_dp(FF,A) :-
    integer_only_presburger(FF,F),
    presb_formula(F),
    (lpa_dp(F) -> A = yes; A= no).
lpa_dp(F) :- 
    to_basic_presburger(F,FF),
    integer_only_presburger(FF,F1),
    renaming_variables(F1,F2),
    to_prenex(F2,F3),				% Prenex NF
    not(instant_false(F3)),
    cooper(F3).

lpa_dpb(F):-presb_formula(F),
           to_basic_presburger(F,F1),
	   renaming_variables(F1,F2),
	   to_prenex(F2,F3),
	   not(instant_false(F3)),
	   la_dpb(F3).


la_dpb(F):-universal(F),hodes(F),!.
la_dpb(F):-cooper(F).

%la_dp3(F):-cooper(F).
%la_dp3(F):-universal(F),distr_cooper(F),write(' By:Mix           '),!.


universal(F):-quant_free(F),!.

universal(_:_=>F2):- universal(F2).


% ****************************************************


distr_cooper(F):- impl_elim(F,F1),
                  move_neg(F1,F2),
  	          to_cnf(F2,F4),
 	          skip_quants(F4,L,F5),
                  prove_conjucts(F5,L).


prove_conjucts(F,L):-not(functor(F,#,_)),
	             l_close(F,L,Fc),
		     cooper(Fc).

prove_conjucts(F,L):-functor(F,#,_),
	             arg(1,F,F1),
		     arg(2,F,F2),
		     prove_conjucts(F1,L),
		     prove_conjucts(F2,L).

l_close(F,[],F).
l_close(F,[V|L],Fc):-F1=..[=>,pnat,F],
	             F2=..[:,V,F1],
		     l_close(F2,L,Fc).

skip_quants(F,[],F):-quant_free(F).

skip_quants(F,L,Fq):-functor(F,:,_),
	             arg(1,F,V),
		     arg(2,F,F1),
		     functor(F1,=>,_),
		     arg(2,F1,F2),
		     skip_quants(F2,L1,Fq),
		     append(L1,[V],L).
	 

% ****************************************************


instant_false(F):-instant_formula(F,F1),
	          not(cooper(F1)),!.

instant_formula(F,Fi):-functor(F,:,_),
	               arg(1,F,V),
		       arg(2,F,F1),
		       functor(F1,=>,_),
		       arg(1,F1,pnat),
		       arg(2,F1,F2),
		       value(Val),
		       instant_var(V,Val,F2,F2i),
		       instant_formula(F2i,Fi).


instant_formula(F,Fi):-functor(F,:,_),
	               arg(1,F,V),
		       arg(2,F,F1),
		       functor(F1,#,_),
		       arg(1,F1,pnat),
		       arg(2,F1,F2),
		       instant_formula(F2,F2i),
		       F2i1=..[#,pnat,F2i],
		       Fi=..[:,V,F2i1].

instant_formula(F,F):-quant_free(F).

value(0).
value(1).
value(100).


instant_var(V,Val,F,Fi):-functor(F,R,2),
			 arg(1,F,T1),
		         arg(2,F,T2),
			 instant_var(V,Val,T1,Pt1),
			 instant_var(V,Val,T2,Pt2),
			 Fi=..[R,Pt1,Pt2].

instant_var(V,Val,F,Fi):-functor(F,R,1),
			 arg(1,F,T1),
			 instant_var(V,Val,T1,Pt1),
			 Fi=..[R,Pt1].

instant_var(V,_,F,F):-atom(F),not(F=V).
instant_var(_,_,F,F):-integer(F).
instant_var(V,Val,V,Val).








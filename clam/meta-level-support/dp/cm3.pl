/*
 * @(#)$Id: cm3.pl,v 1.11 1997/06/05 10:46:01 img Exp $
 *
 * $Log: cm3.pl,v $
 * Revision 1.11  1997/06/05 10:46:01  img
 * Added support for <=>.
 *
 * Revision 1.10  1997/05/12 11:12:58  img
 * Revised implementation of true and false; now encoded via 0=0 and 0=1.  NB VOID is no longer an atomic proposition.
 *
 * Revision 1.9  1997/05/12 10:20:32  img
 * Extend syntax of PA with {true}
 *
 * Revision 1.8  1997/05/08 12:16:50  img
 * Use gensym.
 *
 * Revision 1.7  1997/05/08 10:09:50  img
 * [revert back to v1.5]
 *
 * Revision 1.6  1997/05/08 10:04:01  img
 * Map pnat equality to int.
 *
 * Revision 1.5  1997/05/07 18:31:33  img
 * Quantification over pnat and int supported.
 *
 * Revision 1.4  1997/02/20 14:57:49  img
 * faster code
 *
 * Revision 1.3  1997/01/14 10:36:58  img
 * Added headers, renamed substitute/4 to h_substitute/4.
 *
 * Revision 1.2  1997/01/14 10:25:06  img
 * Added support for non-Presburger translations
 *
 * Revision 1.1  1997/01/14 10:23:51  img
 * Decision procedures.
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: cm3.pl,v 1.11 1997/06/05 10:46:01 img Exp $').

% ******************************************************************
%   Module 3 for eliminating some arithmetic defined functions
%              and relations from statements
%
%             Written by Predrag Janicic, 1996.
%         Mathematical Reasoning Group (DReaM Group)
%           Department of Artificial Intelligence 
%                 University of Edinburgh
% ****************************************************************

% ****************************************************************
% This is module for dealing with defined arithmetic functions
%  and relations that could be expressed in terms of
%              Presburger Arithmetic
% **************************************************************** 
  


to_basic_presburger(F,F1) :- presb_rewrite(F,F1).

defined_rel(even,1).
defined_rel(odd,1).

defined_fun(double,1).
defined_fun(half,1).
defined_fun(p,1).
defined_fun(minus,2).

presb_rewrite(Formula,Fp) :-
    atomic_formula(Formula),!,
    presb_rewrite_af(Formula,Fp).

presb_rewrite(Va:T=>F2,Va:T=>F2p):- !,presb_rewrite(F2,F2p).
presb_rewrite(Va:T#F2,Va:T#F2p):- !,presb_rewrite(F2,F2p).
presb_rewrite(F1<=>F2,(G1=>G2)#(G2=>G1)):- !,
    presb_rewrite(F1,G1), presb_rewrite(F2,G2).
presb_rewrite(F1#F2,F1p#F2p):- !,
    presb_rewrite(F1,F1p), presb_rewrite(F2,F2p).
presb_rewrite(F1=>void,F1p=>void):- !,
    presb_rewrite(F1,F1p).
presb_rewrite(F1=>F2,F1p=>F2p):- !,
    presb_rewrite(F1,F1p), presb_rewrite(F2,F2p).
presb_rewrite(F1\F2,F1p\F2p):- !,
    presb_rewrite(F1,F1p), presb_rewrite(F2,F2p).

presb_rewrite_af(Formula,Fp):-functor(Formula,R,_),
	                      rel(R),
			      arg(1,Formula,T1),			    
		              arg(2,Formula,T2),
			      presb_rewrite_term(T1,T1p,L1),
			      presb_rewrite_term(T2,T2p,L2),
			      F11=..[R,T1p,T2p],
			      append(L1,L2,L),
			      presb_make(F11,L,Fp).

presb_rewrite_af(T1 = T2 in T,Fp):-
    presb_rewrite_term(T1,Pt1,L1),
    presb_rewrite_term(T2,Pt2,L2),
    append(L1,L2,L),
    presb_make(Pt1 = Pt2 in T,L,Fp).

presb_rewrite_af(void,0=1 in int).
presb_rewrite_af({true},0=0 in int).

% next two clause should be generalized
presb_rewrite_af(even(Arg),Fp):-
    presb_rewrite_term(Arg,Parg,L),
    get_new_var(V),
    F1=..[=,Parg,times(2,V)],
    F2=..[in,F1,pnat],
    presb_make(F2,L,F3),
    F4=..[#,pnat,F3],
    Fp=..[:,V,F4].

presb_rewrite_af(odd(Arg),Fp):-
    presb_rewrite_term(Arg,Parg,L),
    get_new_var(V),
    F1=..[=,Parg,plus(times(2,V),1)],
    F2=..[in,F1,pnat],
    presb_make(F2,L,F3),
    F4=..[#,pnat,F3],
    Fp=..[:,V,F4].

presb_rewrite_term(T,T,[]):-atom(T),!.
presb_rewrite_term(T,T,[]):-integer(T),!.
presb_rewrite_term(plus(T1,T2),plus(P1,P2),L):-
    presb_rewrite_term(T1,P1,L1),
    presb_rewrite_term(T2,P2,L2),
    append(L1,L2,L).

presb_rewrite_term(times(T1,T2),times(P1,P2),L):-
    presb_rewrite_term(T1,P1,L1),
    presb_rewrite_term(T2,P2,L2),
    append(L1,L2,L).

presb_rewrite_term(s(T1),s(P1),L):-
    presb_rewrite_term(T1,P1,L).

% next two clause should be generalized
presb_rewrite_term(double(T1),V,L):-
    presb_rewrite_term(T1,P1,L1),
    get_new_var(V),
    append(L1,[V,times(2,P1)=V in pnat],L).

presb_rewrite_term(half(T1),V,L):-
    !,presb_rewrite_term(T1,P1,L1),
    get_new_var(V),
    F1=..[=,P1,times(2,V)],
    F2=..[in,F1,pnat],
    F3=..[plus,times(2,V),s(0)],
    F4=..[=,P1,F3],
    F5=..[in,F4,pnat],
    F=..[\,F2,F5],
    append(L1,[V,F],L).

presb_rewrite_term(T,Tp,L):-functor(T,p,1),
	                    arg(1,T,T1),
			    presb_rewrite_term(T1,P1,L1),
                            get_new_var(V),
			    Tp=V,
			    F1=..[=,P1,0],
			    F2=..[in,F1,pnat],
			    F3=..[=,V,0],
			    F4=..[in,F3,pnat],
			    F5=..[=>,F2,F4],
			    H1=..[=>,F2,void],
			    H2=..[s,V],
			    H3=..[=,P1,H2],
			    H4=..[in,H3,pnat],
			    H5=..[=>,H1,H4],
			    F=..[#,F5,H5],
			    append(L1,[V,F],L).



presb_rewrite_term(T,Tp,L):-functor(T,minus,2),
	                    arg(1,T,T1),
			    arg(2,T,T2),
			    presb_rewrite_term(T1,P1,L1),
			    presb_rewrite_term(T2,P2,L2),
                            get_new_var(V),
			    Tp=V,
			    F1=..[geq,P2,P1],
			    F2=..[=,V,0],
			    F3=..[in,F2,pnat],
			    F4=..[=>,F1,F3],
			    H1=..[greater,P1,P2],
			    H2=..[plus,P2,V],
			    H3=..[=,P1,H2],
			    H4=..[in,H3,pnat],
			    H5=..[=>,H1,H4],
			    F=..[#,F4,H5],
			    append(L1,[V,F],L0),
			    append(L2,L0,L).


presb_make(F,[],F).
presb_make(F,[X,Y|Z],F1):-presb_make(F,Z,Fp),
	                  F11=..[=>,Y,Fp],
	                  F12=..[=>,pnat,F11],
			  F1=..[:,X,F12].

get_new_var(V):- gensym(u,V).

/* Quantification over the natural numbers (pnat) is translated to
   equivalent quantification over the integers.  */  
integer_only_presburger(A,A) :- atomic_formula(A),!.
integer_only_presburger(V:pnat=>T,V:int=>(greater(V,-1)=>TT)) :-
    !,integer_only_presburger(T,TT).
integer_only_presburger(V:pnat#T,V:int#(greater(V,-1)#TT)) :-
    !,integer_only_presburger(T,TT).
integer_only_presburger(T,S) :-
    T =.. [P|As],
    map_list(As,A:=>AA,integer_only_presburger(A,AA),SAs),
    S =.. [P|SAs].

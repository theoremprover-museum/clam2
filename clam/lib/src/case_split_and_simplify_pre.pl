% $Id: case_split_and_simplify_pre.pl,v 1.2 1995/05/24 17:04:58 armando Exp $
%
% $Log: case_split_and_simplify_pre.pl,v $
% Revision 1.2  1995/05/24 17:04:58  armando
% Substantially upgraded (and simplified version).
% hyp2goal now deals correctly with "dummy" hypotheses.
%
% Revision 1.1  1995/05/20  11:12:39  armando
% Initial version
%

hyp2goal([],[]).
hyp2goal([G|Gs],[N|Ns]):- hyp2goal(G,N),
	                  hyp2goal(Gs,Ns).

hyp2goal(H==>G,NH==>NG) :-
	member(X:P,H),
	\+ (type(P) ; P=dummy), !,
	del_hyp(X:P,H,H1),
	hyp2goal([X:dummy|H1]==>P=>G,NH==>NG).
hyp2goal(H==>G,H==>G).

% Change with oyster_type?
type(C):-member(C,[int, pnat, atom, _ list, _ tree]).

repeat_seq([],[],[]).
repeat_seq([_==>SG|SGS],[SP|SPS],[(seq(SG) then[SP,propositional])|NP]) :-
	repeat_seq(SGS,SPS,NP).

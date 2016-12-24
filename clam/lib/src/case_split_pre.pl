% compl_conds(+CondsL,-CompCondsL)
%
% CompCondsL is the list of complemetary pairs of the form
% [[Exp],[Exp=>void]] occurring in CondsL.
% Complementary pairs of the form [Exp=>void,Exp] are normalized into
% [[Exp],[Exp=>void]] (see 2nd clause).

compl_conds([],[]):-!.
compl_conds([[[Exp],[Exp=>void]]|CondsL],[[[Exp],[Exp=>void]]|ComplCondsL]):-
	!,
	compl_conds(CondsL,ComplCondsL).
compl_conds([[[Exp=>void],[Exp]]|CondsL],[[[Exp],[Exp=>void]]|ComplCondsL]):-
	!,
	compl_conds(CondsL,ComplCondsL).
compl_conds([_|CondsL],ComplCondsL):-
	compl_conds(CondsL,ComplCondsL).

% compl_conds_sort(+CondsL,+Sorted)
%
% Sorted is a sorted version of CondsL according to the following
% (heuristic) ordering:
%  - equality of small types (i.e., pnat, atom, ...)
%  - others
compl_conds_sort(CondsL,Sorted):-
	compl_conds_split(CondsL,Equalities,Complex),
	append(Equalities, Complex, Sorted).

compl_conds_split([],[],[]):-!.
compl_conds_split([[[Exp],[CExp]]|CondsL],[[[Exp],[CExp]]|Equalities], Complex):-
	Exp=(_=_ in _), !,
	compl_conds_split(CondsL,Equalities,Complex).
compl_conds_split([[[Exp],[CExp]]|CondsL],Equalities, [[[Exp],[CExp]]|Complex]):-
	compl_conds_split(CondsL,Equalities,Complex).
	


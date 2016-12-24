/* -*- Mode: Prolog -*-
 * @(#)$Id: libs.pl,v 1.7 1998/07/27 12:16:44 img Exp $
 *
 * $Log: libs.pl,v $
 * Revision 1.7  1998/07/27 12:16:44  img
 * Dialect support adjustments
 *
 * Revision 1.6  1997/05/09 13:55:48  img
 * mods for SWI version 2
 *
 * Revision 1.5  1997/05/08 12:52:46  img
 * Update to version 2
 *
 * Revision 1.4  1995/10/18 13:22:32  img
 * library support
 *
 * Revision 1.3  1995/10/18  12:19:07  img
 * ocunifiable removed (now in util.pl)
 *
 * Revision 1.2  1995/04/25  10:08:10  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:21:46  dream
 * Initial revision
 *
 */
:- multifile file_version/1.
file_version('$Id: libs.pl,v 1.7 1998/07/27 12:16:44 img Exp $').

/* This file contains some patches to make SWI Prolog look more like
 * Quintus/NIP.
 * The size of this file is a tribute to the DEC10 compatibility of SWI
 * Prolog!
 *
 * This file assumes that the file nip.pl has already been loaded.
 *
 * At the end of the file are some patches/workarounds for bugs in SWI
 * Prolog. 
 */

lib_fname(File, File).
lib_fname( LibDir, Object, Kind, FN ) :-
          concatenate_atoms( [LibDir, '/', Kind, '/', Object ], FN ).
	   
ttywrite(X) :- write(user,X).
ttynl :- nl(user).
ask(X) :- get0(X), in_eoln(X).
in_eoln(10) :- !.
in_eoln(_) :- get0(X),in_eoln(X).

uniq_id( X ) :- gensym('',X).

nth(N, List, Element) :-
	integer(N), !,
	N >= 1,
	N1 is N-1,
	nth0i(N1, List, Element).
nth(N, List, Element) :-
	var(N),
	nth0v(List, Element, 1, N).

nth0v([Element|_], Element, Index, Index).
nth0v([_|Tail], Element, M, Index) :-
	N is M + 1,
	nth0v(Tail, Element, N, Index).

nth0i(0, [Head|_], Head) :- !.
nth0i(N, [_|Tail], Element) :-
        M is N - 1,
        nth0i(M, Tail, Element).

%   nth0(?N, +List, ?Element, ?Rest)
%   nth0/4 unifies Element with the nth element in List, counting the
%   first element as 0 and Rest with rest of the elements.

nth0(N, List, Element, Rest) :-
        integer(N), !,
        N >= 0,
        nth0i(N, List, Element, Rest).
nth0(N, List, Element, Rest) :-
        var(N),
        nth0v(List, Element, 0, N, Rest).

nth0v([Element|Tail], Element, Index, Index, Tail).
nth0v([Head|Tail], Element, M, Index, [Head|Rest]) :-
        N is M + 1,
        nth0v(Tail, Element, N, Index, Rest).

nth0i(0, [Head|Tail], Head, Tail) :- !.
nth0i(N, [Head|Tail], Element, [Head|Rest]) :-
        M is N - 1,
        nth0i(M, Tail, Element, Rest).

/* Defined in SWI 2.x
nth1(N,[H|T],Elem) :- nth0(N1,[H|T],Elem), N is N1+1.
nth1(N,[H|T],Elem,Rest) :- nth0(N1,[H|T],Elem,Rest), N is N1+1.
*/
	% must_be_integer(Int,ArgNr,Call)
	% Succeeds iff Int is integer, where Int appears as the ArgNr-th
	% argument to Call. Protests if Int not integer.
	% Simulates predicate from Quintus library types
must_be_integer(Int,_,_) :- integer(Int),!.
must_be_integer(Int,ArgNr,Call) :-
    functor(Call,F,N), nl,
    writef('! Type failure in argument %t of %t\n',[ArgNr,F/N]),
    writef('! integer expected, but found %t\n',[Int]),
    writef('! Goal: %t\n',[Call]),
    !,fail.

%   power_set(?Set, ?PowerSet)
%   is true when Set is a list and PowerSet is a list of lists which
%   represents the power set of the set that Set represents.  The
%   particular representation of the power set chosen has this defining
%   property: if A subset-of B subset-of Set, then B appears *BEFORE*
%   A in PowerSet.  In particular, the first element of PowerSet must
%   be Set itself, and the last element of PowerSet must be [].  As an
%   example, power_set([a,b], X) binds X=[[a,b],[a],[b],[]].
%   Note that length(PowerSet) = 2**length(Set), so that for Sets with
%   more than about 18 elements, this isn't a very practical operation.
power_set(Set, [Set|Rest]) :-
        ps(Set, [Set|Rest]).
ps([], [[]]).
ps([Head|Tail], ListPow) :-
        ps(Tail, TailPow),
        ps(TailPow, Head, TailPow, ListPow).
ps([], _, ListPow, ListPow).
ps([Subset|Subsets], Element, TailPow, [[Element|Subset]|ListPow]) :-
        ps(Subsets, Element, TailPow, ListPow).

%   contains_term(+Kernel, +Expression)
%   is true when the given Kernel occurs somewhere in the Expression.
%   It can only be used as a test; to generate sub-terms use sub_term/2.

contains_term(Kernel, Expression) :-
        \+ free_of_term(Kernel, Expression).

%   free_of_term(+Kernel, +Expression)
%   is true when the given Kernel does not occur anywhere in the
%   Expression.  NB: if the Expression contains an unbound variable,
%   this must fail, as the Kernel might occur there.  Since there are
%   infinitely many Kernels not contained in any Expression, and also
%   infinitely many Expressions not containing any Kernel, it doesn't
%   make sense to use this except as a test.

free_of_term(Kernel, Kernel) :- !,
        fail.
free_of_term(_Kernel, Expression) :-
        atomic(Expression),!.
free_of_term(Kernel, Expression) :-
        functor(Expression, _, Arity),          %  can't be a variable!
        free_of_term(Arity, Expression, Kernel).

free_of_term(0, _, _) :- !.
free_of_term(N, Expression, Kernel) :-
        arg(N, Expression, Argument),
        free_of_term(Kernel, Argument),
        M is N-1,
        free_of_term(M, Expression, Kernel).

%   sub_term(?Kernel, +Term)
%   is true when Kernel is a sub-term of Term.  It enumerates the
%   sub-terms of Term in an arbitrary order.  Well, it is defined
%   that a sub-term of Term will be enumerated before its own
%   sub-terms are (but of course some of those sub-terms might be
%   elsewhere in Term as well).

sub_term(Term, Term).
sub_term(SubTerm, Term) :-
        nonvar(Term),
        functor(Term, _, N),
        sub_term(N, Term, SubTerm).

sub_term(N, Term, SubTerm) :-
        arg(N, Term, Arg),
        sub_term(SubTerm, Arg).
sub_term(N, Term, SubTerm) :-
        N > 1,
        M is N-1,
        sub_term(M, Term, SubTerm).

%   append(+ListOfLists, ?List)
%   is true when ListOfLists is a list [L1,...,Ln] of lists, List is
%   a list, and appending L1, ..., Ln together yields List.  The
%   ListOfLists **must** be a proper list.  (Strictly speaking we
%   should produce an error message if it is not, but this version
%   fails.)  Additionally, either List should be a proper list, or
%   each of L1, ..., Ln should be a proper list.  The behaviour on
%   non-lists is undefined.  ListOfLists must be proper because for
%   any given solution, infinitely many more can be obtained by
%   inserted nils ([]) into ListOfList.

append(-, _) :- !, fail.        % reject partial lists.
append([], []).
append([L|Ls], List0) :-
        append(L, List1, List0),
        append(Ls, List1).

selectchk(X, [X|R],     Residue) :- !, Residue = R.
selectchk(X, [A,X|R],   Residue) :- !, Residue = [A|R].
selectchk(X, [A,B,X|R], Residue) :- !, Residue = [A,B|R].
selectchk(X, [A,B,C|L], [A,B,C|R]) :-
	selectchk(X, L, R).

/* Needed in 2.x because first two arguments  are swapped (!) */
:- redefine_system_predicate(select(_,_,_)).
select(X, [X|R],     R        ).
select(X, [A,X|R],   [A|R]    ).
select(X, [A,B,X|R], [A,B|R]  ).
select(X, [A,B,C|L], [A,B,C|R]) :-
    select(X, L, R).

intersect(Set1, Set2) :-
	member(Element, Set1),		%  generates Elements from Set1
	memberchk(Element, Set2),	%  tests them against Set2
	!.				%  if it succeeds once, is enough.

perm( A,B ) :- msort(A,C), msort(B,C).
seteq( A, B ) :- sort(A,C), sort(B,C).

intersection([Set|Sets], Intersection) :-
	intersection1(Set, Sets, Intersection).

intersection1([], _, []).
intersection1([Element|Elements], Sets, Intersection) :-
	memberchk_all(Sets, Element),
	!,
	Intersection = [Element|Rest],
	intersection1(Elements, Sets, Rest).
intersection1([_|Elements], Sets, Intersection) :-
	intersection1(Elements, Sets, Intersection).

memberchk_all([], _).
memberchk_all([Set|Sets], Element) :-
	memberchk(Element, Set),
	memberchk_all(Sets, Element).

%   subseq(Sequence, SubSequence, Complement)
%   is true when SubSequence and Complement are both subsequences of the
%   list Sequence (the order of corresponding elements being preserved)
%   and every element of Sequence which is not in SubSequence is in the
%   Complement and vice versa.  That is,
%   length(Sequence) = length(SubSequence)+length(Complement), e.g.
%   subseq([1,2,3,4], [1,3,4], [2]).  This was written to generate subsets
%   and their complements together, but can also be used to interleave two
%   lists in all possible ways.  Note that if S1 is a subset of S2, it will
%   be generated *before S2 as a SubSequence and *after it as a Complement.

subseq([], [], []).
subseq([Head|Tail], Sbsq, [Head|Cmpl]) :-
	subseq(Tail, Sbsq, Cmpl).
subseq([Head|Tail], [Head|Sbsq], Cmpl) :-
	subseq(Tail, Sbsq, Cmpl).

%   same_length(?List1, ?List2, ?Length)
%   is true when List1 and List2 are both lists, Length is a non-negative
%   integer, and both List1 and List2 have exactly Length elements.  No
%   relation between the elements of the lists is implied.  If Length
%   is instantiated, or if either List1 or List2 is bound to a proper
%   list, same_length is determinate and terminating.  library(length)
%   has more predicates with this structure.

same_length(List1, List2, Length) :-
	(   integer(Length) ->
	    Length >= 0,
	    'same length'(Length, List1, List2)
	;   nonvar(Length) ->
	    must_be_integer(Length, 3, same_length(List1,List2,Length))
	;   var(List1) ->		% swap List1 and List2 around to
	    'same length'(List2, List1, 0, Length)
	;
	    'same length'(List1, List2, 0, Length)
	).

'same length'(0, List1, List2) :- !,	% delay unification
	List1 = [],			% to block infinite loops
	List2 = [].
'same length'(N, [_|Rest1], [_|Rest2]) :-
	M is N-1,			% N > 0, M >= 0
	'same length'(M, Rest1, Rest2).


'same length'([], [], N, N).
'same length'([_|Rest1], [_|Rest2], I, N) :-
	J is I+1,
	'same length'(Rest1, Rest2, J, N).


/* Defined in SWI 2.x Quintus library
%   genarg(?N, +Term, ?Arg)
%   is true when arg(N, Term, Arg) is true, except that it can solve
%   for N.  Term, however, must be instantiated.

genarg(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        arg(N, Term, Arg).
genarg(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg(Arity, Term, Arg, N).

genarg(1, Term, Arg, 1) :- !,
	arg(1, Term, Arg).
genarg(N, Term, Arg, N) :-
	arg(N, Term, Arg).
genarg(K, Term, Arg, N) :-
	K > 1, J is K-1,
	genarg(J, Term, Arg, N).
*/

%   genarg0(?N, +Term, ?Arg)
%   succeeds when N > 0 and arg(N, Term, Arg) is true
%   or when N =:= 0 and functor(Term, Arg, _) is true.
genarg0(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        (   N =:= 0 -> functor(Term, Arg, _)
        ;   arg(N, Term, Arg)
        ).
genarg0(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg0(Arity, Term, Arg, N).
genarg0(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        (   N =:= 0 -> functor(Term, Arg, _)
        ;   arg(N, Term, Arg)
        ).
genarg0(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg0(Arity, Term, Arg, N).

genarg0(0, Term, Arg, 0) :- !,
	functor(Term, Arg, _).
genarg0(N, Term, Arg, N) :-
	arg(N, Term, Arg).
genarg0(K, Term, Arg, N) :-
	K > 0, J is K-1,
	genarg0(J, Term, Arg, N).


/* ******************* ENVIRONMENT *************** */

/* Defined in SWI 2.x
reconsult(F) :- consult(F).
*/

compile(F) :- consult(F).

file_exists(F) :- exists_file(F).

environ(Var,Val) :- getenv(Var,Val).

/* Defined in SWI 2.x Quintus library
numbervars(Term,Begin,End) :- numbervars(Term,'$VAR',Begin,End).
*/

datime(date(Year,Month1,Day,Hour,Min,Sec)) :-
    get_time(T),
    convert_time( T, Year, Month, Day, Hour, Min, Sec,_),
    % Emulate Quintus bug....:
    Month1 is Month-1.

version(Text) :- recordz(version,Text,_).

	% save_state(+String,+File) saves current program state in File. Next
	% time File is called, String will be printed as a banner,
	% followed by the time when the saved state was created.
        % third argument distinguishes between the differenet behaviours for
        % clam and clamlib, since clamlib does not load the needs file
save_state(String,File,clamlib) :-
    datime(date(Year,Month1,Day,Hour,Min,_)),
    Month is Month1+1,	% Quintus bug: Month is 1 down.
    name(Atom,String),
    (Hour<10->(Hc is Hour+48,H=[48,Hc]);H=Hour),
    (Min <10->(Mc is  Min+48,M=[48,Mc]);M=Min),
    concatenate_atoms([Atom,' (',Day,'/',Month,'/',Year,' ',H,':',M,')'],Banner),
    retractall(boot_pred),
    assert((boot_pred :- '$welcome', nl,write(Banner),nl,nl)),
    qsave_program(File, [ goal = boot_pred ]).


save_state(String,File,clam) :-
    datime(date(Year,Month1,Day,Hour,Min,_)),
    Month is Month1+1,	% Quintus bug: Month is 1 down.
    name(Atom,String),
    (Hour<10->(Hc is Hour+48,H=[48,Hc]);H=Hour),
    (Min <10->(Mc is  Min+48,M=[48,Mc]);M=Min),
    concatenate_atoms([Atom,' (',Day,'/',Month,'/',Year,' ',Hour,':',Min,')'],Banner),
    retractall(boot_pred),
    assert((boot_pred :- '$welcome', nl,write(Banner),nl,nl,
                      lib_dir_system(Dir),
		      concatenate_atoms([Dir,'/',needs],Needs),
		      reconsult(Needs))),
    qsave_program(File, [ goal = boot_pred ]).

save_clam(Name, Description, Type) :-
    clam_version(V),name(V,Vname), 
    append([Description, ", version ",Vname],Banner),
    dialect(D), concatenate_atoms([Name, '.v', V, '.' ,D],LibFile),
    save_state(Banner,LibFile,Type).

/* SWI does not support signals */
on_exception(_Exception, Goal, _Action) :-
    Goal.
raise_exception(_Signal).

%   Module : ordsets
%   Author : Richard A. O'Keefe
%   Updated: 1/3/90
%   Purpose: Ordered set manipulation utilities

%   Adapted from shared code written by the same author; all changes
%   Copyright (C) 1987, Quintus Computer Systems, Inc.  All rights reserved.

%   In this module, sets are represented by ordered lists with no
%   duplicates.  Thus {c,r,a,f,t} would be [a,c,f,r,t].  The ordering
%   is defined by the @< family of term comparison predicates, which
%   is the ordering used by sort/2 and setof/3.

%   The benefit of the ordered representation is that the elementary
%   set operations can be done in time proportional to the sum of the
%   argument sizes rather than their product.  You should use the
%   operations defined here in preference to those in library(sets)
%   unless there is a compelling reason why you can't.  Some of the
%   unordered set routines, such as member/2, length/2 and select/3 can
%   be used unchanged on ordered sets; feel free so to use them.

%   There is no ordset_to_list/2, as an ordered set is a list already.

%   is_ordset(List)
%   is true when List is a list of terms [T1,T2,...,Tn] and the
%   terms are strictly increasing: T1 @< T2 @< ... @< Tn.  The
%   output of sort/2 always satisfies this test.  Anything which
%   satisfies this test can be given to the predicates in this
%   file, regardless of where you got it.

is_ordset(-) :- !, fail.	% catch and reject variables.
is_ordset([]).
is_ordset([Head|Tail]) :-
	is_ordset(Tail, Head).

is_ordset(-, _) :- !, fail.	% catch and reject variables.
is_ordset([], _).
is_ordset([Head|Tail], Left) :-
	Head @> Left,
	is_ordset(Tail, Head).



%   list_to_ord_set(+List, ?Set)
%   is true when Set is the ordered representation of the set represented
%   by the unordered representation List.  The only reason for giving it
%   a name at all is that you may not have realised that sort/2 could be
%   used this way.

list_to_ord_set(List, Set) :-
	sort(List, Set).



%   ord_add_element(+Set1, +Element, ?Set2)
%   is the equivalent of add_element for ordered sets.  It should give
%   exactly the same result as merge(Set1, [Element], Set2), but a bit
%   faster, and certainly more clearly.

ord_add_element([], Element, [Element]).
ord_add_element([Head|Tail], Element, Set) :-
	compare(Order, Head, Element),
	ord_add_element(Order, Head, Tail, Element, Set).


ord_add_element(<, Head, Tail, Element, [Head|Set]) :-
	ord_add_element(Tail, Element, Set).
ord_add_element(=, Head, Tail, _, [Head|Tail]).
ord_add_element(>, Head, Tail, Element, [Element,Head|Tail]).



%   ord_del_element(+Set1, +Element, ?Set2)
%   is the equivalent of del_element for ordered sets.  Because it uses
%   ordering, it typically builds less structure, but is slower than
%   del_element.  I am beginning to wonder whether a predicate
%	set_plus(SmallSet, Element, LargeSet)
%   would be a better way of doing this, the idea being that
%   LargeSet = SmallSet U {Element} and Element is not in SmallSet.

ord_del_element([], _, []).
ord_del_element([Head|Tail], Element, Set) :-
	compare(Order, Head, Element),
	ord_del_element(Order, Element, Head, Tail, Set).

ord_del_element(<, Element, Head, Tail, [Head|Set]) :-
	ord_del_element(Tail, Element, Set).
ord_del_element(=, _, _, Set, Set).
ord_del_element(>, _, Head, Tail, [Head|Tail]).



%   ord_disjoint(+Set1, +Set2)
%   is true when the two ordered sets have no element in common.  If the
%   arguments are not ordered, I have no idea what happens.

ord_disjoint(Set1, Set2) :-
	\+ ord_intersect(Set1, Set2).



%   ord_intersect(+Set1, +Set2)
%   is true when the two ordered sets have at least one element in common.
%   Note that the test is == rather than = .
%   ord_intersect/2 has been unfolded in ord_intersect/5 to avoid
%   constructing anything.

ord_intersect([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_intersect(Order, Head1, Tail1, Head2, Tail2).

ord_intersect(=, _, _, _, _).
ord_intersect(<, _, [Head1|Tail1], Head2, Tail2) :-
	compare(Order, Head1, Head2),
	ord_intersect(Order, Head1, Tail1, Head2, Tail2).
ord_intersect(>, Head1, Tail1, _, [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_intersect(Order, Head1, Tail1, Head2, Tail2).



%   ord_intersect(+Set1, +Set2, ?Intersection)
%   is an obsolete synonym for ord_intersection/3.

ord_intersect(Set1, Set2, Intersection) :-
	ord_intersection(Set1, Set2, Intersection).



%   ord_intersection(+Set1, +Set2, ?Intersection)
%   is true when Intersection is the ordered representation of Set1
%   and Set2, provided that Set1 and Set2 are ordered sets.

ord_intersection([], _, []).
ord_intersection([Head1|Tail1], Set2, Intersection) :-
	ord_intersection_1(Set2, Head1, Tail1, Intersection).

ord_intersection_1([], _, _, []).
ord_intersection_1([Head2|Tail2], Head1, Tail1, Intersection) :-
	compare(Order, Head1, Head2),
	ord_intersection_1(Order, Head1, Tail1, Head2, Tail2, Intersection).

ord_intersection_1(=, Head, Tail1, _, Tail2, [Head|Intersection]) :-
	ord_intersection(Tail1, Tail2, Intersection).
ord_intersection_1(<, _, Tail1, Head2, Tail2, Intersection) :-
	ord_intersection_1(Tail1, Head2, Tail2, Intersection).
ord_intersection_1(>, Head1, Tail1, _, Tail2, Intersection) :-
	ord_intersection_1(Tail2, Head1, Tail1, Intersection).



%   ord_intersection(+ListOfSets, ?Intersection)
%   is true when ListOfSets is a nonempty proper list of ordered sets
%   and Intersection is their intersection.  Earlier versions of this
%   package used a "logarithmic" method for this, similar to the code
%   in ord_union/2.  However, experiments showed that intersection is
%   better done using a "linear" method (in the case of union, we are
%   faced with _growing_ intermediate results, but in intersection we
%   have a case of _shrinking_ intermediate results).  We cannot take
%   an empty ListOfSets because its intersection is the universe!

ord_intersection([Set|Sets], Intersection) :-
	ord_intersection_3(Sets, Set, Intersection).

ord_intersection_3([], Intersection, Intersection).
ord_intersection_3([Set|Sets], Intersection0, Intersection) :-
	ord_intersection(Set, Intersection0, Intersection1),
	ord_intersection_3(Sets, Intersection1, Intersection).



%   ord_seteq(+Set1, +Set2)
%   is true when the two arguments represent the same set.  Since they
%   are assumed to be ordered representations, they must be identical.

ord_seteq(Set1, Set2) :-
	Set1 == Set2.



%   ord_setproduct(+Set1, +Set2, ?Product)
%   is in fact identical to setproduct(Set1, Set2, Product).
%   If Set1 and Set2 are ordered sets, Product will be an ordered
%   set of x1-x2 pairs.  Note that we cannot solve for Set1 and
%   Set2, because there are infinitely many solutions when
%   Product is empty, and may be a large number in other cases.

ord_setproduct([], _, []).
ord_setproduct([H|T], L, Product) :-
	ord_setproduct(L, H, Product, Rest),
	ord_setproduct(T, L, Rest).

ord_setproduct([], _, L, L).
ord_setproduct([H|T], X, [X-H|TX], TL) :-
	ord_setproduct(T, X, TX, TL).



%   ord_subset(+Set1, +Set2)
%   is true when every element of the ordered set Set1 appears in the
%   ordered set Set2.

ord_subset([], _).
ord_subset([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_subset(Order, Head1, Tail1, Tail2).

ord_subset(=, _, Tail1, Tail2) :-
	ord_subset(Tail1, Tail2).
ord_subset(>, Head1, Tail1, [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	ord_subset(Order, Head1, Tail1, Tail2).



%   ord_subtract(+Set1, +Set2, ?Difference)
%   is true when Difference contains all and only the elements of Set1
%   which are not also in Set2.

ord_subtract([], _, []).
ord_subtract([Head1|Tail1], Set2, Difference) :-
	ord_subtract_1(Set2, Head1, Tail1, Difference).

ord_subtract_1([], Head1, Tail1, [Head1|Tail1]).
ord_subtract_1([Head2|Tail2], Head1, Tail1, Difference) :-
	compare(Order, Head1, Head2),
	ord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).

ord_subtract(<, Head1, Tail1, Head2, Tail2, [Head1|Difference]) :-
	ord_subtract_2(Tail1, Head2, Tail2, Difference).
ord_subtract(>, Head1, Tail1, _,     Tail2, Difference) :-
	ord_subtract_1(Tail2, Head1, Tail1, Difference).
ord_subtract(=, _,     Tail1, _,     Tail2, Difference) :-
	ord_subtract(Tail1, Tail2, Difference).

ord_subtract_2([], _, _, []).
ord_subtract_2([Head1|Tail1], Head2, Tail2, Difference) :-
	compare(Order, Head1, Head2),
	ord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).



%   ord_symdiff(+Set1, +Set2, ?Difference)
%   is true when Difference is the symmetric difference of Set1 and Set2.

ord_symdiff([], Set2, Set2).
ord_symdiff([Head1|Tail1], Set2, Difference) :-
	ord_symdiff(Set2, Head1, Tail1, Difference).

ord_symdiff([], Head1, Tail1, [Head1|Tail1]).
ord_symdiff([Head2|Tail2], Head1, Tail1, Difference) :-
	compare(Order, Head1, Head2),
	ord_symdiff(Order, Head1, Tail1, Head2, Tail2, Difference).

ord_symdiff(<, Head1, Tail1, Head2, Tail2, [Head1|Difference]) :-
	ord_symdiff(Tail1, Head2, Tail2, Difference).
ord_symdiff(>, Head1, Tail1, Head2, Tail2, [Head2|Difference]) :-
	ord_symdiff(Tail2, Head1, Tail1, Difference).
ord_symdiff(=, _,     Tail1, _,     Tail2, Difference) :-
	ord_symdiff(Tail1, Tail2, Difference).



%   ord_disjoint_union(+Set1, +Set2, ?Union)
%   is true when Set1 and Set2 (given to be ordered sets) have no element
%   in common, and Union is their union.  The meaning is the same as
%	ord_disjoint(Set1, Set2),
%	ord_union(Set1, Set2, Union)
%   but it is more efficient.

ord_disjoint_union([], Set2, Set2).
ord_disjoint_union([Head1|Tail1], Set2, Union) :-
	ord_disjoint_union_1(Set2, Head1, Tail1, Union).

ord_disjoint_union_1([], Head1, Tail1, [Head1|Tail1]).
ord_disjoint_union_1([Head2|Tail2], Head1, Tail1, Union) :-
	compare(Order, Head1, Head2),
	ord_disjoint_union_1(Order, Head1, Tail1, Head2, Tail2, Union).

ord_disjoint_union_1(<, Head1, Tail1, Head2, Tail2, [Head1|Union]) :-
	ord_disjoint_union_1(Tail1, Head2, Tail2, Union).
ord_disjoint_union_1(>, Head1, Tail1, Head2, Tail2, [Head2|Union]) :-
	ord_disjoint_union_1(Tail2, Head1, Tail1, Union).



%   ord_union(+Set1, +Set2, ?Union)
%   is true when Union is the union of Set1 and Set2.  Note that when
%   something occurs in both sets, we want to retain only one copy.
%   The previous version had some cuts, and was 10-20% slower.

ord_union([], Set2, Set2).
ord_union([Head1|Tail1], Set2, Union) :-
	ord_union_1(Set2, Head1, Tail1, Union).

ord_union_1([], Head1, Tail1, [Head1|Tail1]).
ord_union_1([Head2|Tail2], Head1, Tail1, Union) :-
	compare(Order, Head1, Head2),
	ord_union_1(Order, Head1, Tail1, Head2, Tail2, Union).

ord_union_1(<, Head1, Tail1, Head2, Tail2, [Head1|Union]) :-
	ord_union_1(Tail1, Head2, Tail2, Union).
ord_union_1(>, Head1, Tail1, Head2, Tail2, [Head2|Union]) :-
	ord_union_1(Tail2, Head1, Tail1, Union).
ord_union_1(=, Head1, Tail1, _,     Tail2, [Head1|Union]) :-
	ord_union(Tail1, Tail2, Union).



%   ord_union(+OldSet, +NewSet, ?Union, ?ReallyNew)
%   is true when Union is NewSet U OldSet and ReallyNew is NewSet \ OldSet.
%   This is useful when you have an iterative problem, and you're adding
%   some possibly new elements (NewSet) to a set (OldSet), and as well as
%   getting the updated set (Union) you would like to know which if any of
%   the "new" elements didn't already occur in the set (ReallyNew).

ord_union([], Set2, Set2, Set2).
ord_union([Head1|Tail1], Set2, Union, New) :-
	ord_union_1(Set2, Head1, Tail1, Union, New).

ord_union_1([], Head1, Tail1, [Head1|Tail1], []).
ord_union_1([Head2|Tail2], Head1, Tail1, Union, New) :-
	compare(Order, Head1, Head2),
	ord_union(Order, Head1, Tail1, Head2, Tail2, Union, New).

ord_union(<, Head1, Tail1, Head2, Tail2, [Head1|Union], New) :-
	ord_union_2(Tail1, Head2, Tail2, Union, New).
ord_union(>, Head1, Tail1, Head2, Tail2, [Head2|Union], [Head2|New]) :-
	ord_union_1(Tail2, Head1, Tail1, Union, New).
ord_union(=, Head1, Tail1, _,     Tail2, [Head1|Union], New) :-
	ord_union(Tail1, Tail2, Union, New).

ord_union_2([], Head2, Tail2, [Head2|Tail2], [Head2|Tail2]).
ord_union_2([Head1|Tail1], Head2, Tail2, Union, New) :-
	compare(Order, Head1, Head2),
	ord_union(Order, Head1, Tail1, Head2, Tail2, Union, New).



%   ord_union(+ListOfSets, ?Union)
%   is true when ListOfSets is given as a proper list of ordered sets
%   and Union is their union.  Letting K be the length of ListOfSets,
%   and N the sum of the sizes of its elements, the cost is of order
%   N.lg(K).  The auxiliary routine
%   ord_union(N, L, U, R)
%   is true when the union of the first N sets in L is U and
%   R is the remaining elements of L.

ord_union(ListOfSets, Union) :-
	length(ListOfSets, NumberOfSets),
	ord_union_3(NumberOfSets, ListOfSets, Union, []).

ord_union_3(0, R, [], R) :- !.
ord_union_3(1, [U|R], U, R) :- !.
ord_union_3(2, [A,B|R], U, R) :- !,
	ord_union(A, B, U).
ord_union_3(N, R0, U, R) :-
	P is N>>1,	% |first  half of list|
	Q is N- P,	% |second half of list|
	ord_union_3(P, R0, A, R1),
	ord_union_3(Q, R1, B, R),
	ord_union(A, B, U).

/*  You will notice that ord_union/2 and ord_intersection/2 have
    the same structure.  This is no accident.  Suppose we want to
    compute <F>([X1,...,Xn]) = <G>(X1) <H> ... <H> <G>(Xn),
    where <G> is any function, and <H> is associative with left
    identity <E> (it does not need to be commutative or to have
    a right identity) we can perform the calculation in at least
    the following ways:

    <F>_lin(List, Answer) :-
	<F>_lin(List, <E>, Answer).

    <F>_lin([], Answer, Answer).
    <F>_lin([X|Xs], SoFar, Answer) :-
	<G>(X, Xg),
	<H>(SoFar, Xg, Next),
	<F>_lin(Xs, Next, Answer).


    <F>_log(List, Answer) :-
	length(List, Length),
	<F>_log(Length, List, Answer, []

    <F>_log(0, R, <E>, R) :- !.
    <F>_log(1, [X|R], Answer, R) :- !,
	<G>(X Answer).
    <F>_log(2, [X1,X2|R], Answer, R) :- !,
	<G>(X1, G1),
	<G>(X2, G2),
	<H>(G1, G2, Answer).
    <F>_log(N, R0, Answer, R) :-
	P is N>>1,	% |first  half of list|
	Q is N- P,	% |second half of list|
	<F>_log(P, R0, A, R1),
	<F>_log(Q, R1, B, R),
	<H>(A, B, Answer).

    You will note that the third clause of <F>_log/4 is actually
    redundant.  If you partially evaluate the fourth clause with
    N=2 that is the answer you get.  The optimisation is usually
    a good idea.  You will further note that the first clause of
    <F>_log/4 is only used when <F>_log([], X) is called, so it
    could be moved up into that procedure.

    The <F>_lin schema is easy to grasp.  However, the <F>_log
    schema can be considerably more efficient.  Consider sorting.
    Here <E> = [], <G>(X,[X]), and <H>(X,Y,Z) = merge(X,Y,Z).
    Merging a single element into a list of length N costs O(N)
    time, so <sort>_lin would take O(N**2) time to sort a list
    of length N, whereas <sort>_log would take O(N.lgN) time.
    Hence the names.  <F>_log is a real win when the cost of the
    <H> operation is non-trivial and increases with bigger
    operands.  Numerical analysts know that <sum>_log is often
    the best way to sum a list of floating point numbers, that is,
    that it gives a more accurate answer (because there are only
    O(lgN) roundoffs in it, as opposed to O(N) in <sum>_lin), but
    that is a rather marginal case.  sumlist/3 in library(lists)
    is <sum>_lin because it was originally intended for integers.
*/

%   concatenate_atoms(+ListOfTextObjects, -Combined)
%   concatenates the names of all the text objects in the list
%   and returns an atom whose name is the combined characters.
%   Valid text objects are either character lists, atoms or numbers.
concatenate_atoms(List,Atom) :-
    concatenate_atoms1(List, ListTmp), name(Atom,ListTmp).
% concatenate_atoms1([],'').
concatenate_atoms1([],[]).
concatenate_atoms1([H|T], Out) :-
    atomic(H), !, name(H,HH), concatenate_atoms1(T,TT), append(HH,TT,Out).
concatenate_atoms1([H|T], Out) :-
    H =.. [.|_], concatenate_atoms1(T,TT), append(H,TT, Out).

%   rev(+List, ?Reversed)
%   is a version of reverse/2 which only works one way around.
%   Its List argument must be a proper list whatever Reversed is.
%   You should use reverse/2 in new programs, though rev/2 is
%   faster when it is safe to use it.
rev(List, Reversed) :-
        rev(List, [], Reversed).
rev([], Reversed, Reversed).
rev([Head|Tail], Sofar, Reversed) :-
        rev(Tail, [Head|Sofar], Reversed).

%   permutation(?List, ?Perm)
%   is true when Perm is a permutation of List.

permutation([], []).
permutation(List, [First|Perm]) :- 
	select(First, List, Rest),
	permutation(Rest, Perm).

maplist(Pred, Xs, Ys, Zs) :-
        map_list_(Xs, Ys, Zs, Pred).

map_list_([], [], [], _).
map_list_([X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, X, Y, Z),
        map_list_(Xs, Ys, Zs, Pred).

maplist(Pred, Ws, Xs, Ys, Zs) :-
        map_list_(Ws, Xs, Ys, Zs, Pred).

map_list_([], [], [], [], _).
map_list_([W|Ws], [X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, W, X, Y, Z),
        map_list_(Ws, Xs, Ys, Zs, Pred).

div(A,B,C) :- A is (B // C).

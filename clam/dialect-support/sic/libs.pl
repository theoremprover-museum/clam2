/* -*- Mode: Prolog -*-
 * @(#)$Id: libs.pl,v 1.23 2008/05/22 16:55:07 smaill Exp $
 *
 * $Log: libs.pl,v $
 * Revision 1.23  2008/05/22 16:55:07  smaill
 * move tab code to oyster
 *
 * Revision 1.22  2008/05/22 16:48:04  smaill
 * stop tabbing from backtracking
 *
 * Revision 1.21  2008/05/21 16:07:38  smaill
 * debug sicstus4 version;; small benchmark works now
 *
 * Revision 1.20  2008/05/21 14:13:52  smaill
 * update for sicstus4
 *
 * Revision 1.19  2003/01/22 18:51:43  smaill
 * for DICE
 *
 * Revision 1.18  2003/01/22 15:58:36  smaill
 * for dice
 *
 * Revision 1.17  1998/07/27 12:16:42  img
 * Dialect support adjustments
 *
 * Revision 1.16  1998/03/04 15:06:30  img
 * disjoint/2 added
 *
 * Revision 1.15  1997/11/06 15:59:19  img
 * lib_fname/4: treat * as special
 *
 * Revision 1.14  1997/10/09 17:02:35  img
 * lib_fname/2 added
 *
 * Revision 1.13  1997/05/09 09:29:22  img
 * Abstract div/3 to dialect-support.
 *
 * Revision 1.12  1997/05/08 12:55:14  img
 * Update to version 3
 *
 * Revision 1.11  1997/01/14 10:48:16  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.10  1996/12/11 14:22:00  img
 * gracefull_abort/0 added.
 *
 * Revision 1.9  1996/07/09 15:39:29  img
 * load ordsets (was in so.pl)
 *
 * Revision 1.8  1996/06/19  12:53:18  img
 * gensym/2 added.
 *
 * Revision 1.7  1996/06/19  11:22:47  img
 * clam_patchlevel_info/0: removed.
 *
 * Revision 1.6  1995/10/18  12:15:43  img
 * ocunifiable/2 changed to matches/2;  code moved from libs.pl into
 * util.pl
 *
 * Revision 1.5  1995/10/03  13:38:43  img
 * lib_dir_system/1 rather than lib_dir/1
 *
 * Revision 1.4  1995/07/18  14:17:12  img
 * print helpful message on startup
 *
 * Revision 1.3  1995/05/18  13:14:19  img
 * 	* Added stuff for Quintus compatibility
 *
 * Revision 1.2  1995/04/25  10:08:07  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:22:00  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: libs.pl,v 1.23 2008/05/22 16:55:07 smaill Exp $').

/*
 * This file contains all the definitions for predicates from the
 * Quintus library to make CLaM run under SICStus Prolog
 * Load this file before loading anything else if you want to run under
 * SICStus.
 */
lib_fname(File, File).
lib_fname( '*', Object, Kind, FN ) :-		% system directory
    lib_dir_system(Dir),
    concatenate_atoms( [Dir, '/', Kind, '/', Object ], FN ).
lib_fname( LibDir, Object, Kind, FN ) :-
           concatenate_atoms( [LibDir, '/', Kind, '/', Object ], FN ).
ttywrite(X) :- write(user,X).
ask(X) :- get0(X), in_eoln(X).
in_eoln(10) :- !.
in_eoln(_) :- get0(X),in_eoln(X).

:- op(900,      fy,     [not]).

not Goal :- \+ Goal.
do_subcall :-
    read(X),
    !,
    call(X),
    !,
    fail.    


/*
 * this is a bit of a pain, but since we cannot remove stuff from the
 * initialization list in sicstus, we make the first message conditional on
 * a flag (clam_lib_only) which is set to false when building clam proper
 */
save_state(String,File) :-
%    name(Atom,String),
%    concatenate_atoms(['
%', Atom],_Banner),
    save_program(File).

:- dynamic clam_lib_only/1 .
:- dynamic description/1 .

save_clam(Name, Description, clamlib) :-
    asserta(clam_lib_only(true)),
    asserta(description(Description)),
    clam_version(V),
    dialect(D), concatenate_atoms([Name, '.v', V, '.' ,D],LibFile),
    save_program(LibFile).

save_clam(Name, Description, clam) :-
    retractall(clam_lib_only(_)),
    asserta(clam_lib_only(false)),
    retractall(description(_)),
    asserta(description(Description)),
    clam_version(V),
    dialect(D), concatenate_atoms([Name, '.v', V, '.' ,D],LibFile),
    save_program(LibFile).

:- initialization do_init.

do_init :- clam_lib_only(true), !,
	   clam_version(V),name(V,Vname),
	   description(Description),
           append([Description,", version ", Vname],Banner),
           name(BannerAtom,Banner),
	   nl,write(BannerAtom),nl,nl.

do_init :- clam_lib_only(false), !,
	clam_version(V),name(V,Vname),
	description(Description),
	append([Description,", version ", Vname],Banner),
	name(BannerAtom,Banner),
        nl,write(BannerAtom),nl,nl,
	lib_dir_system(Dir),
	concatenate_atoms([Dir,'/',needs],Needs),
	consult(Needs).

do_init :- write( 'Initialisation check.' ), nl, nl.

	% Dummy code for a number of predicates to shut up make and edit
	% package.  In SWI we don't need it (it has its own make and
	% edit commands), and in NIP the make/0 predicate just won't
	% work. Tough shit. For the edit package, only hardwired editors
	% are used in NIP.
datime(date(0,0,0,0,0,0)).
file_property(_,modify_time,Datime) :- datime(Datime).
environ(_) :- fail.

uniq_id( X ) :-
     recorded( '@id_ctr@',X, Ref ),
     SX is X + 1,
     erase(Ref),
     recorda( '@id_ctr@', SX, _ ),
     !.
uniq_id( 1 ) :-
     recorda( '@id_ctr@', 1, _ ).

	% Provide naive implementation instead of Quintus library one.
	% Can't be bothered to include 2 pages of code just to get this
	% running more efficiently.

% nth0(N,[H|T],Elem) :-
%     append(First,[Elem|_],[H|T]),
%     same_length(First,_,N).

%nth1(N,[H|T],Elem) :- nth0(N1,[H|T],Elem), N is N1+1.
%nth1(N,[H|T],Elem,Rest) :- nth0(N1,[H|T],Elem,Rest), N is N1+1.

% use sicstus nth1

nth(X,Y,Z) :- nth1(X,Y,Z).

	% same comment:
apply(Functor,Args) :- Call =.. [Functor|Args], call(Call).

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

% The following are copied from the Quintus library.
% All are trivial, nevertheless:
% Copyright (C) 1987, Quintus Computer Systems, Inc.  All rights reserved.
% 
% 	contains_term/2
% 	free_of_term/2
%	sub_term/2
%	append/3             Included in sicstus2 list library
%	append/2             
%	genarg/3
%	genarg0/3
%	reverse/2            Included in sicstus2 list library
%       last/2               Included in sicstus2 list library
% 	subseq/3
% 	same_length/3        Included in sicstus2 list library

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
%
% ground/1 is a primitive of sicstus2 
% (but not sicstus0.7).
%
% ground(T) :- \+ \+ numbervars(T,0,0).

concat(A,B,C) :-
    name(A,AA),name(B,BB),
    append(AA,BB,CC),
    name(C,CC).

% concatenate_atom  (used to be in Sicstus ??)

concatenate_atoms( [X], X ).
concatenate_atoms( [H|T], Y ) :-
  concatenate_atoms( T, YY ), concat( H, YY, Y).

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

%append(-, _) :- !, fail.        % reject partial lists.
%append([], []).
%append([L|Ls], List0) :-
%       append(L, List1, List0),
%       append(Ls, List1).

%   flatten(Tree, List)
%   flattens a Tree of cons cells, yielding a List.  This is just
%       binary_to_list(Tree, ., [], List, []).
%   but it is more efficient.  You may find it helpful to see the
%   special case as a guide to the general case.
        
flatten(Tree, List) :-
        flatten(Tree, List, []).

flatten([], List0, List) :- !,
        List0 = List.
flatten([Head|Tail], List0, List) :- !,
        flatten(Head, List0, List1),
        flatten(Tail, List1, List).
flatten(Other, [Other|List], List).

%selectchk(X, [X|R],     Residue) :- !, Residue = R.
%selectchk(X, [A,X|R],   Residue) :- !, Residue = [A|R].
%selectchk(X, [A,B,X|R], Residue) :- !, Residue = [A,B|R].
%selectchk(X, [A,B,C|L], [A,B,C|R]) :-
%	selectchk(X, L, R).

% Included in sicstus2 list library.
% select(X, [X|R],     R        ).
% select(X, [A,X|R],   [A|R]    ).
% select(X, [A,B,X|R], [A,B|R]  ).
% select(X, [A,B,C|L], [A,B,C|R]) :-
%	select(X, L, R).


%   intersect(+Set1, +Set2)
%   is true when the two sets have a member in common.  It assumes
%   that both sets are known, and that you don't care which element
%   it is that they share.  If either argument is partial, intersect/2
%   will succeed: this isn't always right.  You should ensure that the
%   arguments are proper lists.

intersect(Set1, Set2) :-
	member(Element, Set1),		%  generates Elements from Set1
	memberchk(Element, Set2),	%  tests them against Set2
	!.				%  if it succeeds once, is enough.


/*  TRY the following faster code

%perm( [H|T], L ) :-
%      selectchk( L, H, R ),
%      perm(T,R).
%perm([],[]).

seteq( [H|T], S ) :-
      selectchk( S,H, RS),
      seteq( T, RS ).
seteq( [], [] ).*/

%perm( A,B ) :- sort(A,C), sort(B,C).
%seteq( A, B ) :- sort(A,C), sort(B,C).


%   intersection(+Set1, +Set2, ?Intersection)
%   is true when all three arguments are lists representing sets,
%   and Intersection contains every element of Set1 which is also
%   an element of Set2, the order of elements in Intersection
%   being the same as in Set1.  That is, Intersection represents
%   the intersection of the sets represented by Set1 and Set2.
%   If Set2 is a partial list, Intersection will be empty, which
%   is not, of course, correct.  If Set1 is a partial list, this
%   predicate will run away on backtracking.  Set1 and Set2 should
%   both be proper lists, but this is not checked.  Duplicates in
%   Set1 may survive in Intersection.  It is worthy of note that
%   if Set1 is an ordset, Intersection is an ordset, despite Set2.

intersection([], _, []).
intersection([Element|Elements], Set, Intersection) :-
	memberchk(Element, Set),
	!,
	Intersection = [Element|Rest],
	intersection(Elements, Set, Rest).
intersection([_|Elements], Set, Intersection) :-
	intersection(Elements, Set, Intersection).

%   intersection(+ListOfSets, ?Intersection)
%   is true when Intersection is the intersection of all the sets in
%   ListOfSets.  The order of elements in Intersection is taken from
%   the first set in ListOfSets.  This has been turned inside out to
%   minimise the storage turnover.

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

%   reverse(?List, ?Reversed)
%   is true when List and Reversed are lists with the same elements
%   but in opposite orders.  Either List or Reversed should be a
%   proper list: given either argument the other can be found.  If
%   both are incomplete reverse/2 can backtrack forever trying ever
%   longer lists.

% reverse(List, Reversed) :-
%         reverse(List, Reversed, [], Reversed).

reverse([], [], Reversed, Reversed).
reverse([Head|Tail], [_|Bound], Sofar, Reversed) :-
        reverse(Tail, Bound, [Head|Sofar], Reversed).

%   rev(+List, ?Reversed)
%   is a version of reverse/2 which only works one way around.
%   Its List argument must be a proper list whatever Reversed is.
%   You should use reverse/2 in new programs, though rev/2 is
%   faster when it is safe to use it.
%rev(List, Reversed) :-
%        rev(List, [], Reversed).

%rev([], Reversed, Reversed).
%rev([Head|Tail], Sofar, Reversed) :-
%        rev(Tail, [Head|Sofar], Reversed).

%   last(?Last, +List)
%   is true when List is a List and Last is its last element.
%   THE ARGUMENT ORDER IS WRONG:  it should be last(List -> Last).
%   This could be defined as last(X,L) :- append(_, [X], L).

% last(Last, [Head|Tail]) :-
%	last(Tail, Head, Last).		

%last([], Last, Last).
%last([Head|Tail], _, Last) :-
%	last(Tail, Head, Last).

/* Lists and A and B have no members in common */
disjoint([],_).
disjoint([A|As],B) :-
    \+ member(A,B),
    disjoint(As,B).


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

%subseq([], [], []).
%subseq([Head|Tail], Sbsq, [Head|Cmpl]) :-
%	subseq(Tail, Sbsq, Cmpl).
%subseq([Head|Tail], [Head|Sbsq], Cmpl) :-
%	subseq(Tail, Sbsq, Cmpl).

subset( [H|T], S ) :-
        memberchk( H, S ),
        subset( T, S ).
subset([],_).

/*  Present in v3 
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
*/
%   file_exists(+File)
%   is true when File is a well formed file name of an existing file.
file_exists(File) :-
    seeing(Curr),
    ( set_prolog_flag(fileerrors,off) ; set_prolog_flag(fileerrors,on), fail ),
    see(File),
    ( seen ; true ),
    see(Curr),
    !.


% Construct banner, construct file name to save in, and save: 
save_it( N ) :- clam_version(V),name(V,Vname), 
   append(["CLaM Proof Planner Version ",Vname," (libraries only)"],Banner),
   dialect(_D), 
   save_state(Banner, N).

/*
 * This file loads libraries required for building a SICStus version
 * of CLaM.
 */

?- ensure_loaded(library(lists)),
   ensure_loaded(library(ordsets)).

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


/* Gensym support */
:- dynamic
        gensym_counter/2.
gensym(Prefix, V) :-
        var(V),
        atomic(Prefix),
        (   retract(gensym_counter(Prefix, M))
        ;   M = 0
        ),
        N is M+1,
        asserta(gensym_counter(Prefix, N)),
        concat(Prefix, N, V),
        !.

append_term(Term, MoreArgs, FullTerm) :-
        functor(Term, Symbol, Arity),
        atom(Symbol),           % must test as MoreArgs=[] is ok.
        len(MoreArgs, Arity, FullArity),
        functor(FullTerm, Symbol, FullArity),
        append_term1(MoreArgs, Arity, FullTerm),
        append_term2(Arity, Term, FullTerm).

len(0, _, _) :- !, fail.        % catch partial lists
len([], N, N).
len([_|L], N0, N) :-
        N1 is N0+1,
        len(L, N1, N).
append_term1([A1,A2|Args], M, FullTerm) :- !,
        N1 is M+1, arg(N1, FullTerm, A1),
        N2 is M+2, arg(N2, FullTerm, A2),
        append_term1(Args, N2, FullTerm).
append_term1([A1], M, FullTerm) :- !,
        N1 is M+1, arg(N1, FullTerm, A1).
append_term1([], _, _).

%%  append_term2(N, OldTerm, NewTerm)
%   is true when the Ith argument of OldTerm unifies with the
%   Ith argument of NewTerm, for 1 <= I <= N.  It has been
%   hacked for speed rather than clarity.

append_term2(N, OldTerm, NewTerm) :-
        (   N > 1 ->
            arg(N, OldTerm, ArgN),
            arg(N, NewTerm, ArgN),
            M is N-1,
            arg(M, OldTerm, ArgM),
            arg(M, NewTerm, ArgM),
            L is M-1,
            append_term2(L, OldTerm, NewTerm)
        ;   N > 0 ->
            arg(1, OldTerm, Arg1),
            arg(1, NewTerm, Arg1)
        ;   true
        ).

strip_module_prefix(0, _, _, _) :- !,
        fail.
strip_module_prefix(Prefix:Term, _, Goal, Module) :- !,
        strip_module_prefix(Term, Prefix, Goal, Module).
strip_module_prefix(Goal, Module, Goal, Module) :-
        nonvar(Goal),           % should be callable(Goal)
        atom(Module).

%%  append_term(+Term, +Nextra, -Arity, -FullTerm)
%   is given a Term and the number of extra arguments (>=1) to be
%   added.  It returns the Arity of Term, and a new FullTerm which
%   has the same function Symbol and first Arity arguments as Term
%   and whose last Nextra arguments are uninstantiated.  Note that
%   we do not need to explicitly test for atom(Symbol), as the
%   functor(FullTerm, Symbol, FullArity /* > 0 */) construction
%   will implicitly make this test.

append_term(Term, Nextra, Arity, FullTerm) :-
        functor(Term, Symbol, Arity),           % we know nonvar(Term)
        FullArity is Arity+Nextra,              % FullArity > 0
        functor(FullTerm, Symbol, FullArity),   % tests atom(Symbol)
        append_term2(Arity, Term, FullTerm).
  


%call(Term, Y1) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 1, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        Module:Full.
%call(Term, Y1) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [2, call(Term,Y1)]),
%        fail.


%%   call(+pred(X1,...,Xm), ?Y1, ?Y2)
%%   calls pred(X1, ..., Xm, Y1, Y2))

%call(Term, Y1, Y2) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 2, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        N2 is N+2, arg(N2, Full, Y2),
%        Module:Full.
%call(Term, Y1, Y2) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [3, call(Term,Y1,Y2)]),
%        fail.


%%   call(+pred(X1,...,Xm), ?Y1, ?Y2, ?Y3)
%%   calls pred(X1, ..., Xm, Y1, Y2, Y3))

%call(Term, Y1, Y2, Y3) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 3, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        N2 is N+2, arg(N2, Full, Y2),
%        N3 is N+3, arg(N3, Full, Y3),
%        Module:Full.
%call(Term, Y1, Y2, Y3) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [4, call(Term,Y1,Y2,Y3)]),
%        fail.


%   call(+pred(X1,...,Xm), ?Y1, ?Y2, ?Y3, ?Y4)
%   calls pred(X1, ..., Xm, Y1, Y2, Y3, Y4))

%call(Term, Y1, Y2, Y3, Y4) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 4, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        N2 is N+2, arg(N2, Full, Y2),
%        N3 is N+3, arg(N3, Full, Y3),
%        N4 is N+4, arg(N4, Full, Y4),
%        Module:Full.
%call(Term, Y1, Y2, Y3, Y4) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [5, call(Term,Y1,Y2,Y3,Y4)]),
%        fail.



%%   call(+pred(X1,...,Xm), ?Y1, ?Y2, ?Y3, ?Y4, ?Y5)
%%   calls pred(X1, ..., Xm, Y1, Y2, Y3, Y4, Y5))

%call(Term, Y1, Y2, Y3, Y4, Y5) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 5, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        N2 is N+2, arg(N2, Full, Y2),
%        N3 is N+3, arg(N3, Full, Y3),
%        N4 is N+4, arg(N4, Full, Y4),
%        N5 is N+5, arg(N5, Full, Y5),
%        Module:Full.
%call(Term, Y1, Y2, Y3, Y4, Y5) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [6, call(Term,Y1,Y2,Y3,Y4,Y5)]),
%        fail.



%%   call(+pred(X1,...,Xm), ?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6)
%%   calls pred(X1, ..., Xm, Y1, Y2, Y3, Y4, Y5, Y6))

%call(Term, Y1, Y2, Y3, Y4, Y5, Y6) :-
%        strip_module_prefix(Term, user, Form, Module),
%        append_term(Form, 6, N, Full),
%        !,
%        N1 is N+1, arg(N1, Full, Y1),
%        N2 is N+2, arg(N2, Full, Y2),
%        N3 is N+3, arg(N3, Full, Y3),
%        N4 is N+4, arg(N4, Full, Y4),
%        N5 is N+5, arg(N5, Full, Y5),
%        N6 is N+6, arg(N6, Full, Y6),
%        Module:Full.

%call(Term, Y1, Y2, Y3, Y4, Y5, Y6) :-
%        format(user_error,
%            '~N! 1st argument of call/~q is not callable~n! Goal: ~q~n',
%            [7, call(Term,Y1,Y2,Y3,Y4,Y5,Y6)]),
%        fail.

gracefull_abort :-
    abort.

        %   between(+Lower, +Upper, ?Number)
        %   is true when Lower, Upper, and Number are integers,
        %   and Lower =< Number =< Upper.  If Lower and Upper are given,
        %   Number can be tested or enumerated.  If either Lower or Upper
        %   is absent, there is not enough information to find it, and an
        %   error will be reported.
        %
        % This predicate is lifted from the Quintus library between,
        % since it contains syntax errors and redefines repeat (sigh...).
between(Lower, Upper, Point) :-
        integer(Lower),
        integer(Upper),
        (   integer(Point), !,          %  These cuts must be cuts;
            Lower =< Point, Point =< Upper
        ;   var(Point), !,              %  they can't be arrows.
            Lower =< Upper,
            between1(Lower, Upper, Point)
        ).
between(Lower, Upper, Point) :-
        Goal = between(Lower,Upper,Point),
        must_be_integer(Lower, 1, Goal),
        must_be_integer(Upper, 2, Goal),
        must_be_integer(Point, 3, Goal).

        %%  between1(Lower, Upper, Point)
        %   enumerates values of Point satisfying Lower =< Point =< Upper,
        %   where it is already known that Lower =< Upper and Point was a
        %   variable.  A purer version of this is left as a comment.
between1(L, L, L) :- !.
between1(L, _, L).              % between1(L, U, L) :- L =< U.
between1(L, U, N) :-            % between1(L, U, N) :- L < U,
        M is L+1,               %       M is L+1,
        between1(M, U, N).      %       between1(M, U, N).


/*
 * The following predicates implement a "make" predicate: when files are
 * (re)consulted used (re)load, the system will store a time-stamp to
 * record the time when the file was loaded. The make/0 predicate will
 * compare the load-time time-stamp of each loaded file with the current
 * modification date of the file, and if the later is newer, reload the
 * file.
 * NOTE: this only works for files that have been loaded using the
 * (re)load/1 predicates (and not for files that have just been
 * (re)consulted.
 *
 * load/1, reload/1 and time_stamp/1 are defined in boot.pl
 */

        % make -Flag: make -i reloads files (interpreted) (the default).
        %             make -c recompiles files
        %             make -n finds out which files are to be reloaded,
        %                     but doesn't actually remake them.
        %             make    is shorthand for make -i.
        % Long live failure driven loops!
'make' :- make -i.
make(-n) :-
    recorded(time_stamp,(File,WhenLoaded),_),
    file_property(File,modify_time,WhenModified),
    WhenModified @> WhenLoaded,
    write(File),nl,
    fail.
make(Flag) :-
    (Flag == -i ; Flag == -c), 
    recorded(time_stamp,(File,WhenLoaded),_),
    file_property(File,modify_time,WhenModified),
    WhenModified @> WhenLoaded,
    (Flag = -i
     -> reload(File)
     ;  (/* Flag = -c, */ loadc(File))
    ),
    fail.
make(_).



%maplist(Pred, Olds, News) :-
%        map_list_(Olds, News, Pred).

%map_list_([], [], _).
%map_list_([Old|Olds], [New|News], Pred) :-
%        call(Pred, Old, New),
%        map_list_(Olds, News, Pred).

%maplist(Pred, Xs, Ys, Zs) :-
%        map_list_(Xs, Ys, Zs, Pred).

%map_list_([], [], [], _).
%map_list_([X|Xs], [Y|Ys], [Z|Zs], Pred) :-
%        call(Pred, X, Y, Z),
%        map_list_(Xs, Ys, Zs, Pred).

maplist(Pred, Ws, Xs, Ys, Zs) :-
        map_list_(Ws, Xs, Ys, Zs, Pred).

map_list_([], [], [], [], _).
map_list_([W|Ws], [X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, W, X, Y, Z),
        map_list_(Ws, Xs, Ys, Zs, Pred).

div(A,B,C) :- A is (B // C).
abs(A,A):-A>0,!.
abs(A,B):-B is -A.

list_to_set(A,B) :-
    remove_dups(A,B).

% tab/1 is non-ISO; simulate it here

% (this code moved to oyster to keep it self-contained)

% tab(N) :- on_exception( E   , M is N,
%			    (   print( "bad argument to tab/1" ),
%				throw(E) )
%		      ),
%	( N >= 0 ->
%	      ttab(N)
%          ; (print( 'negative argument to tab/1'),
%	     throw(neg_arg)
%	    )
%	).
	  

% ttab(0).
% ttab(N) :- N > 0, put_char( ' ' ), M is N-1, ttab(M).

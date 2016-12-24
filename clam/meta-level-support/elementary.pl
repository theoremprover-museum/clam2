/*
 * @(#)$Id: elementary.pl,v 1.12 1999/02/02 09:39:58 img Exp $
 *
 * $Log: elementary.pl,v $
 * Revision 1.12  1999/02/02 09:39:58  img
 * prule/3: added clause
 *
 * Revision 1.11  1998/05/13 12:49:37  img
 * is_elementary/1 added
 *
 * Revision 1.10  1997/09/26 14:50:31  img
 * Do not filter annotations (should be done outside elementary/_
 *
 * Revision 1.9  1997/06/05 10:28:02  img
 * Intro/elim rules for <=>; detect trivial contradictions in hypotheses.
 *
 * Revision 1.8  1997/05/08 16:20:41  img
 * Removed strange convention of calling hyp_list/1 in case of empty hypotheses.
 *
 * Revision 1.7  1997/01/14 10:44:07  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.6  1996/12/04 12:19:07  img
 * elementary0: lift strip_meta_annotations outside main recursion
 * prule: possible place for arithmetic extensions (no tactic support yet)
 *
 * Revision 1.5  1996/07/05  10:19:12  img
 * Small support for <*.
 *
 * Revision 1.4  1996/06/18  16:57:46  img
 * typo: allow use of prolog variables
 *
 * Revision 1.3  1995/05/17  02:17:24  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:05  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: elementary.pl,v 1.12 1999/02/02 09:39:58 img Exp $').

/*
 * This file contains a procedure to detect simple theorems.
 * It uses some (ie not exhaustive) propositional reasoning,
 * knows that equality is reflexive, can strip off universal
 * quantifiers, realises that 0 =/= s(X), nil =/= H::T,
 * tries to deal with existential goals.
 * It is intended to be a cheap test (compared to "propositional").
 * 
 * Stolen/borrowed/gratefully received from AlanS. Renamed some of the
 * predicates and variables, and re-ordered some of the code. 
 *
 * The crucial predicates are elementary/2 for the calculation of a
 * tactic that will prove a goal, and elementary/1 for the execution of it.
 */

is_elementary(P) :- elementary(P,_).

/* elementary(+Sequent,?Tactic) will compute Tactic that 
   proves Sequent.  The proof method uses limited propositional
   reasoning and some knowledge of constructors and equality.  NB It
   is not complete for intuitinistic propositional logic (for that,
   use propositional/2.)  */
elementary( H==>[G|Gs],[Tactic|Tactics]) :- !,
    elementary0( H==>G, Tactic), elementary( H==>Gs,Tactics ).
    elementary( _==>[], [] ) :- !.

elementary(H==>G,Tactic) :-
    elementary0(H==>G,Tactic).

        % elementary/3 looks for simplified rule that is applicable,
        % checks that it has not been used before, adds it to list of
        % hyps elim'd, finds recursively tactics for each of the
        % subgoals, and combines tactics to form overall tactic.
elementary0(H==>G,Tactic) :- 
    prule(H==>G,Rule,Sublist),    %   (should get done elsewhere).
    elementarylist(H,Sublist,Tacticlist),
    newelementary(Tactic,Rule,Tacticlist).

        % elementarylist/4 finds tactics for each of list of sequents, in
        % presence of hypothesis list H (these lists are stored
        % incrementally in rules, so we have to use update/3 to find
        % full hyp list for subgoals). 
elementarylist(_,[],[]):- !.
elementarylist(H,[Subseq|SSL],[Subtactic|STL]) :- !,
    update(H,Subseq,Subgoal),
    elementary0(Subgoal,Subtactic),!,
    elementarylist(H,SSL,STL).

newelementary(Rule,Rule,[]) :- !.
newelementary(intro(left) then [Subtact,wfftacs],intro(left),[Subtact]):-
    !.
newelementary(intro(right)then [Subtact,wfftacs],intro(right),[Subtact]):-
    !.
newelementary(intro then [Subtact,wfftacs],intro(a),[Subtact]) :- !.
newelementary(intro(new N) then [Subtact,wfftacs],intro(new N),[Subtact]) :- !.
newelementary(Rule then Subtact,Rule,[Subtact]) :- !.
newelementary(Rule then Tacticlist,Rule,Tacticlist).

update(H,(HH==>GG),(K==>GG)) :- !,
    append(H,HH,K).
update(H,(==> GG),(H==>GG)).

        %  prule/3 is simplified version of NurPRL rule/3 with arguments
        %  (Rule,Sequent,Subgoal).  Special rule (wfftacs) for wf-goals.
prule(H==>X in T,hyp(X), []) :-
    ( atom(X); var(X) ),
    hyp(X:TT,H),
    convertible(T,TT).
prule(H==>A in T, hyp(X),  []) :-
    \+ A = ( _ = _ ),
    hyp(X:HT,H),
    ( HT = (AA=_ in TT); HT =(_=AA in TT)),
    convertible(T,TT),
    convertible(A,AA).
prule( H==>T, hyp(X),[]) :-
    functor( T,F, A ),
    functor( P,F, A ),
    hyp(X:P,H),
    convertible(T,P).
prule(_==>G in u(_),wfftacs,[] ) :- \+ functor(G,=,2).

        % to avoid needing identity method as well:
prule(_==>T in _,identity,[]) :-
      nonvar(T), T = (X=X),!.
        % to avoid needing identity method as well:
prule(_==>T,identity_equiv,[]) :-
      nonvar(T), T = (X<=>X),!.
        % to avoid needing identity method as well:
prule(H==>_,contradiction(V),[]) :-
    hyp(V: C1 = C2 in T, H),
    \+ C1 == C2,
    constant(C1,T),
    constant(C2,T),!.
        % I know this is supposed to be a >*propositional*< decider, but
        % it's useful to just strip off the universal vars, and see if
        % we are left with a propositional elementary:
prule(_==>{true},istrue,[]) :- !.
prule(_==>j({true}),istrue,[]) :- !.
prule(H==>j(B),jwittac(W),[]) :- jdecide(B,H,W).
prule(H==>nj(B),njwittac(W),[]) :- njdecide( B, H, W).

prule(_==>X<*s(X),clam_arith(_:X<*s(X)),[]) :- !.
prule(_==>X<*s(s(X)),clam_arith(_:X<*s(s(X))),[]) :- !.

        % We have to compensate for Oyster's braindamaged arithmetic
        % somewhere. These are the bare bones of what one would expect...:
prule(H==>_,clam_arith(N:L=R in pnat) ,[] ) :- 
     hyp( N:L=R in pnat, H ), 
     ground(L-R),
     memberchk(L-R,[s(_)-0,0-s(_),s(X)-X,X-s(X)]),
     !.
prule(H==>G,clam_arith(N:s(L)=s(R) in pnat) ,[[M:L=R in pnat]==>G] ) :- 
     hyp( N:s(L)=s(R) in pnat, H ),
     ground(L-R),
     \+ hyp(_:L=R in pnat,H),
     hfree([M],H),
     !.
/* 
prule(H==>_,clam_arith(N:L<*R) ,[] ) :- 
     hyp( N:L<*R, H ), 
     ground(L-R),
     memberchk(L-R,[X-X,X-0]),
     !.
prule(H==>_,clam_arith(N:L<R) ,[] ) :- 
     hyp( N:L<R, H ), 
     ground(L-R),
     memberchk(L-R,[X-X]),
     !.
*/
	% A.Ireland: hard-wired uniqueness property 
        % for list constructors. 
prule(H==>_,clam_arith( N:L=R in T list),[] ) :-
     hyp( N:L=R in T list, H ),
     ground(L-R),
     memberchk(L-R,[(_::_)-nil,nil-(_::_)]),
     !.

prule(H==>_ ,elim(X),[]):- hyp(X:void,H),!.
prule(H==>_, isfalse(X),[]):- hyp(X:j({false}),H),!.

prule(H==>V:T=>G,intro(new[Y]),[[Y:T]==>G] ):- 
        (free([V],H) -> Y=V; hfree([Y],H)), !.
        % int is used as "true" in definitions (e.g. even, leq, etc):
prule(H==>A=>B,intro(new [Y]),[[Y:A]==>B] ):- hfree([Y],H),!.
prule(_==>A#B, intro, [==>A, ==>B] ) :- !.
prule(_==>A<=>B, intro_iff, [==>A=>B, ==>B=>A] ) :- !.
prule(H==>T,elim_iff(Z),[[U:A=>B,V:B=>A,W:dummy,elim_iff(Z)]==>T] ):-
    hyp(Z:A<=>B,H),\+ hyp(elim_iff(Z),H),hfree([U,V,W],H),!.
prule(H==>T,elim(Z),[[U:A,V:B,W:dummy,elim(Z)]==>T] ):-
    hyp(Z:A#B,H),\+ hyp(elim(Z),H),hfree([U,V,W],H),!.
prule(H==>T,elim(Z),[[U:A,V:BU,W:dummy,elim(Z)]==>T] ):-
    hyp(Z:(VV:A#B),H),
    \+ hyp( elim(Z), H ),
    s(B,[VV],[U],BU),
    hfree([U,V,W],H),
    !.
prule(H==>T, elim(V),
    [ [X:A ,N1:dummy, elim(V)]==>T,
      [Y:B ,N2:dummy, elim(V)]==>T ] ):-
          hyp(V:A\B,H),
          \+ hyp(elim(V),H),
          hfree([X,Y,N1,N2],H),
   !.
prule(_==>A\_ ,intro(left), [==>A] ).
prule(_==>_\B ,intro(right),[==>B] ).

prule(H==>G,elim(F),[[elim(F)]==>A, 
                      [Y:void]==>G ] ):-
    hyp(F:A=>void,H),
    \+ hyp(elim(F),H),
    hfree([Y],H).
prule(H==>_, contradiction(X,Y), [] ) :- 
     hyp( X : j(A), H), 
     hyp(Y:nj(A),H),
     !.

jdecide( Bool, Hyps, X ) :- hyp(X:j(Bool), Hyps ),!.

jdecide(and(Bool1,Bool2), Hyps, jand_i(W1,W2) ) :-
     !,
     jdecide(Bool1, Hyps, W1 ),
     jdecide(Bool2, Hyps, W2 ),
     !.
jdecide(not(Bool), Hyps, jnot_i(W) ) :-
     !,
     njdecide(Bool,Hyps,  W ),
     !.
jdecide(or(Bool,_), Hyps, jor_il(W) ) :-
     !,
     jdecide(Bool,Hyps, W ),
     !.
jdecide(or(_,Bool), Hyps,  jor_ir(W) ) :-
     !,
     jdecide(Bool,Hyps,  W ),
     !.
/*
 * The following two clauses are required 
 * for Andrew Stevens datatype shell mechanism.
 * 
jdecide(Recog,_, unit ) :-
     Recog =.. [RName|Args],
     last(Arg,Args),
     functor(Arg,CName,_),
     tuple( shell_constructor, [CName, RName|_] ),
     !.

jdecide(Recog,Hyps, mutex( WitList ) ) :-
     tuple( shell, [Type,_,_,_,_,_,Recogs] ),
     select(Recog, Recogs, RestRecogs ),
     !,
     \+ member( mutex(Type), Hyps ),
     njdecide_list( RestRecogs, [mutex(Type)|Hyps], WitList ). 
 *
 */

jdecide_list( [H|T], Hyps, [HW|TW] ) :-
    jdecide( H, Hyps, HW ),
    jdecide_list( T, Hyps, TW ).
jdecide_list( [], _, [] ).

njdecide( Bool, Hyps, X ) :- hyp(X:nj(Bool), Hyps ),!.
     
njdecide(or(Bool1,Bool2), Hyps,  nor_i(W1,W2) ) :-
     !,
     njdecide(Bool1, Hyps, W1 ),
     njdecide(Bool2, Hyps, W2 ),
     !.
njdecide(not(Bool), Hyps, nnot_i(W) ) :-
     !,
     jdecide(Bool,Hyps, W ),
     !.
njdecide(and(Bool,_), Hyps, nand_il(W) ) :-
     !,
     njdecide(Bool,Hyps, W ),
     !.
njdecide(and(_,Bool), Hyps, nand_ir(W) ) :-
     !,
     njdecide(Bool,Hyps, W ),
     !.
/*
 * The following two clauses are required 
 * for Andrew Stevens datatype shell mechanism.
 * 
njdecide(Recog,_,unit ) :-
     Recog =.. [RName|Args],
     last(Arg,Args),
     functor(Arg,AF,_),
     tuple( shell_constructor, [CName, RName|_] ),
     AF \= CName,
     tuple( shell_constructor, [AF|_] ),
     !.

njdecide(Recog,Hyps, mutex(WitList) ) :-
     tuple( shell, [Type,_,_,_,_,_,Recogs] ),
     select(Recog, Recogs, RestRecogs ),
     !,
     \+ member( mutex(Type), Hyps ),
     jdecide_list( RestRecogs, [mutex(Type)|Hyps], WitList ).
 *
 */

njdecide_list( [H|T], Hyps, [HW|TW] ) :-
    njdecide( H, Hyps, HW ),
    njdecide_list( T, Hyps, TW ).
njdecide_list( [], _, [] ).

% next to ensure that  def of true is present
?- add_def({true}<==>int).


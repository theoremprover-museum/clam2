/* -*- Mode: prolog -*-
 * @(#)$Id: method_pre.pl,v 1.88 2008/05/21 14:14:13 smaill Exp $
 */

/* INCOMPLETE 
:- module(method_pre, [
		      ]).
*/

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: method_pre.pl,v 1.88 2008/05/21 14:14:13 smaill Exp $').

/* Definitions of predicates/functions used in the method-specification
 * language, mostly based on AlanB's DAI Research Paper 349, shorter
 * version in CADE-9 (1988), long version in JAR.
 *
 * I don't like a lot of the conventions and nomenclature[*], but I've stuck
 * to the note fairly closely to avoid confusion. Main difference is that
 * all n-ary functions had to be changed into n+1-ary predicates in the
 * usual way.
 *
 * [*] main objections are:
 *     - inconsistent names (eg. replace_all versus rewrite)
 *     - input-args do not always precede output args 
 *
 * NOTE: These predicates DON'T do any object-level proof steps, eg.
 * replace_all does not do the corresponding proof steps in Oyster.
 * These predicates are NOT the tactics. They should only be used in
 * the pre- and post-conditions of methods to set up the stage for
 * execution or simulate the effects of execution during planning
 * However, some predicates DO use some of the "background" knowledge
 * that can be used during the planning stage (eg. function definition
 * and base- and step-equation) which is stored as Oyster hypotheses.  */


/* exp_at(+Exp, ?Pos, ?SubExp) 
 * Expression Exp contains SubExp at position Pos. Positions are lists of
 * integers representing tree-coordinates in the syntax-tree of the
 * expression, but in reverse order. Furthermore, coordinate 0
 * represents the function symbol of an expression, thus:
 * exp_at(f(g(2,x),3), [2,1], x) and exp_at(f(g(2,x),3), [0,1], g).
 * The definition from note 349 is extended by defining [] as the
 * position of Exp in Exp.  Fails if Pos is an invalid position in
 * Exp.
 
 * NOTE: the tree-coordinates are transparent to wave-fronts which are
 * implemented using special function symbols. Thus, positions in
 * formula are the same whether or not the formula contains
 * wave-fronts. Unfortunately, this means that the "abstract datatype"
 * for wave fronts as defined in the file wave-rules.pl has "leaked"
 * out of that file, and into this predicate.
 
 * It would maybe have been possible to implement exp_at/3 using the
 * abstract datatype for wave-fronts from wave-rules.pl (using the
 * wavefronts/3 predicate), but this would have been very inefficient:
 * we would end up searching for wave fronts, and deleting and
 * inserting them every time exp_at/3 gets called, even in cases where
 * there ain't no wave fronts at all.  Thus, the "leaking" of the
 * abstract datatype is partly a concession to efficiency.
 
 * The rules for the behaviour of exp_at/3 with respect to wave-fronts
 * are as follows (see wave-rule.pl for an explanation of the
 * pretty-printing convention):
 
 * - a \t/ subterm will always be reported as \t/ and never as t.
 * - a ``T'' subterm will always be reported as ``T'' and never as T.
 * - A {T} subterm will always be reported as T and never as {T}.
 * - In both cases the positions are reported as if the ``...'' or
 *  {...} terms were not present. 

 * r_exp_at/3 does the real work. Its specs are the same as exp_at/3,
 * but it computes the pos-list in the natural order.  The final
 * result is reversed before delivered.
 
 * We do some special case coding for +Pos. In that case we first do
 * the reverse, and only then plough into the expression, rather than
 * the (in this case silly) generate-and-test behaviour.  The test
 * numbervars(Pos,0,0) is the fastest way of checking if a term is
 * ground. Proving commutativity of addition without the ind_strat
 * speeds up by 25% using this special case trick.
 *
 * The semantics of exp_at/3 is very close to the Quintus library
 * predicate path_arg/3, except that that does not deal with functors
 * as position 0, and it uses the natural rather than reverse order,
 * so we don't bother to use that.

 * In fact, we implement exp_at/3 in terms of a slightly more general
 * exp_at/4: exp_at(Exp,[N|P],SubExp,SupSubExp) succeeds if SubExp
 * appears in Exp at position [N|P], and SupSubExp appears in Exp at
 * position P, that is: SupSubExp is the expression immediately
 * surrounding SubExp. This is useful since we often find sequences
 * like: exp_at(Goal,[N|P],Var),exp_at(Goal,P,F) to find the
 * immediately surrounding expression of an occurence of Var. Rather
 * than descending into Goal twice (once to find Var, and once to
 * re-find F), we keep track of the two of them at the same time at no
 * cost. Of course, exp_at/3 can be trivially expressed in terms of
 * exp_at/3. Finally, note that exp_at(_,[],_,_) will always fail
 * (since what would the value of SupSubExp be?), and we therefore
 * need a special clause for exp_at/3 for this case.

 * This predicate is a very elementary ingredient of not only the set
 * of predicates allowed in methods, but also used a lot in
 * implementing other code, and therefore its efficiency is crucial.

 * A possible optimization would be to make a separate version which
 * behaved as path_arg/3 (ie. one that didn't return functors as
 * position 0). Sometimes (often), when we call exp_at/3, we know that
 * we are not interested in such solutions, and we could save a lot of
 * time by not having them generated by exp_at/3.

 * And finally, the code: exp_at/3 succeeds for [] path-expressions
 * (take special action to ignore annotations). For non-[]
 * path-expressions, hand over to exp_at/4.    */
exp_at(Var,[],Var) :- var(Var),!.
exp_at(Hole,[],Exp) :- striphole(Hole,Exp),!.
exp_at(Exp,[],Exp).
exp_at(Exp,[N|P],SubExp) :- exp_at(Exp,[N|P],SubExp,_).

/* exp_at/4 fails on [] path-expressions (see comments above),
 * and does special case coding for +Pos (see comments above),
 * before handing over to r_exp_at/4.   */
exp_at(_,[],_,_) :- fail.
exp_at(Exp, Pos, SubExp, SupSubExp) :-
    numbervars(Pos,0,0),!,
    reverse(Pos,RPos),
    r_exp_at(Exp,RPos,SubExp,SupSubExp).
exp_at(Exp, Pos, SubExp, SupSubExp) :- 
    r_exp_at(Exp, RPos, SubExp, SupSubExp),
    reverse(RPos, Pos).

/* r_exp_at/4 does the real work, and comes in three groups of
 * clauses:
 *   [1] fail for vars or atoms
 *   [2] deal with Pos of length 1
 *   [3] deal with Pos of length >=2 (remember that the case Pos=[] has
 *       already been caught by exp_at/4 above).

 * Group [1] is trivial. Groups [2] and [3] are very similar: two
 * special case clauses to deal with wave holes and
 * wave-fronts terms, and one case that does the "real work". For
 * group [2] the real work consists of enumerating all the arguments,
 * for group [3] the real work consists of enumerating all the
 * arguments and recursing on them.  */

/* Group [1]: trivial */
r_exp_at(Exp,_,_,_) :- var(Exp),!,fail.
r_exp_at(Exp,_,_,_) :- atomic(Exp), !, fail.
/* Subsequently explot the fact that Exp is not a variable */

/* Group [2]: unfortunately the two special case clauses cannot start
 * with !, since this would not only cut out the third clause of this
 * group (as intended), but also all the clauses in group [3], which
 * is fatal for mode -Pos. Thus, we need the explicit negations in the
 * 3rd clause of this group.  Notice the special action we may have to
 * take at the end of clause 3 in case a generated argument is a
 * wave_var term, which then needs to be skipped.  */

r_exp_at(Hole,[N],SubExp,SupExp) :-		%ignore holes
    iswh2(Hole,Exp),
    r_exp_at(Exp,[N],SubExp,SupExp).
r_exp_at(Sink,[N],SubExp,SupExp) :-		%ignore sinks
    issink2(Sink,Exp),
    r_exp_at(Exp,[N],SubExp,SupExp).
r_exp_at(WF,[N],SubExp,WF) :-			%ignore fronts
    iswf2(WF,_,_,Exp),
    r_exp_at(Exp,[N],SubExp,Exp).
r_exp_at(SupExp, [N], Exp, SupExp) :-
    \+ iswf(SupExp),
    \+ iswh(SupExp),
    \+ issink(SupExp),
    genarg0(N,SupExp,Exp1),
    (striphole(Exp1,Exp)->true; Exp1=Exp).

/* Group [3]: This time, the two special case clauses can be cut out
 * with ! since this is the last group in the procedure.  Thus, we can
 * avoid the negated functor checks in the last clause of this group.  */
r_exp_at(Hole,[N1,N2|Ns], SubExp, SupExp) :-
    iswh2(Hole,Exp),!,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at(Sink,[N1,N2|Ns], SubExp, SupExp) :- 
    issink(Sink,Exp), !,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at(WF,[N1,N2|Ns], SubExp, SupExp) :- 
    iswf(WF,_,_,Exp),!,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at(Exp, [N1,N2|Ns], SubExp, SupExp) :-
    genarg0(N1,Exp,Arg),
    r_exp_at(Arg, [N2|Ns], SubExp, SupExp).

/* foldr replace down a list with a constant replacement term */

replace_foldr([],_,U,U).
replace_foldr([P|Ps],T,U,W) :-
    replace(P,T,U,V),
    replace_foldr(Ps,T,V,W).
    

/* replace(+Pos, ?NewSub, +OldExp, ?NewExp): NewExp is the result of
 * replacing the subexpression in OldExp at position Pos with NewSub.
 * Either NewSub or NewExp must be instantiated.  TODO: It'd be nice
 * if Pos could also be uninstantiated, allowing for:
 * replace(?Pos,?NewSub,+OldExp,+NewExp) This predicate just does what
 * it's told, and doesn't worry at all about captured variables etc.
 * It is even possible to replace predicate/function symbols....
 * Fails if Pos is an invalid position in OldExp

 * Again, as with exp_at/4, it's easier to deal with the position-list
 * in natural rather than reversed order, so we first reverse it and
 * hand over to r_replace to do the work.

 * Again, as with exp_at/4, the position specifiers are transparent to
 * wave-fronts, and thus this predicate needs to know about the
 * implementation of the wave front terms, resulting in yet another
 * "leak" of the abstract datatype for wave fronts implemented in
 * wave-rule.pl This new leak could of course have been prevented if
 * we only could implement replace/4 in terms of exp_at/4, but I don't
 * think this can be done...

 * Similar rules for the treatment of wave front terms apply for
 * replace/4 as for exp_at/4:
 *   - Subterms ``T'' are always replaced including the ``...''
 *   - Subterms {T} are always replaced excluding the {...}
 *   - Positions are specified as if without wave fronts.   */
replace(Pos, NewSub, OldExp, NewExp) :-
        reverse(Pos,RPos), r_replace(RPos, NewSub, OldExp, NewExp).
replace_multiple( [Pos1|PosR], [Sub1|SubR], OldExp, NewExp ) :-
         replace( Pos1, Sub1, OldExp, IntExp ),
         replace_multiple( PosR, SubR, IntExp, NewExp ).
replace_multiple( [], [], Exp, Exp ).

/* We recursively descend the expression according to the coordinate
   list. First two clauses are base cases of the descend, taking
   special action for holes and sinks. The third and fourth clauses
   just skip wave front terms. The last clause takes arglist apart,
   descends Nth argument, and puts arglist back together again.  */
r_replace([], NewSub, Hole,HoleNewSub) :-
    iswh(Hole),
    iswh(HoleNewSub,NewSub),!.
/* Don't want a special case for sinks (?)
r_replace([], NewSub, Sink,SinkNewSub) :- 
    issink(Sink),
    issink(SinkNewSub,NewSub),!.
*/
r_replace([], NewSub, _, NewSub).
r_replace([N|Ns], NewSub, HoleVarExp, HoleNewExp) :- 
    iswh2(HoleVarExp,VarExp),
    iswh(HoleNewExp,NewExp),!,
    r_replace([N|Ns], NewSub, VarExp, NewExp).
r_replace([N|Ns], NewSub, SinkVarExp, SinkNewExp) :- 
    issink2(SinkVarExp,VarExp),
    issink(SinkNewExp,NewExp),!,
    r_replace([N|Ns], NewSub, VarExp, NewExp).
r_replace([N|Ns],NewSub, WFFE, WFNE) :- 
    iswf2(WFFE,Typ,Dir,FrontExp),
    iswf(WFNE,Typ,Dir,NewExp),!,
    r_replace([N|Ns], NewSub, FrontExp, NewExp).
r_replace([N|Ns], NewSub, OldExp, NewExp) :-
    compound(OldExp),
    OldExp =.. [F|OldArgs],
    partition_c([F|OldArgs], N, PreNth, Nth, PostNth),
    r_replace(Ns, NewSub, Nth, NewNth),
    append(PreNth, [NewNth|PostNth], [NewF|NewArgs]),
    NewExp =.. [NewF|NewArgs].

/* object_level_term(+X) succeeds iff X is ground and does not contain
   wave-fronts or sink notations.  NB.  X must be a well-annotated term.  */
object_level_term(X) :-
    groundp(X),					% this is inefficient
    unannotated(X).

        % nr_of_occ(?SubExp, +SupExp, ?N): SubExp occurs exactly N times
        % in SupExp. 
        % NOTE: failure indicates that SupExp does not occur in SupExp,
        %       thus: N is never bound to 0.
nr_of_occ(Exp, Exp, 1).
nr_of_occ(SubExp, SupExp, N) :-
    SupExp =.. [_|Args],
    findall(M, (member(Arg, Args),nr_of_occ(SubExp,Arg,M)), Ms),
    Ms \= [],
    sum(Ms, N).

        % replace_all(+OldSub,+NewSub,+Exp,?NewExp): NewExp is the
        % result of replacing all occurrences of OldSub with NewSub in
        % Exp.  We just use the Oyster object-level substitution, since
        % this already deals with capture of variables etc.
        %
        % Sometimes the Oyster predicates s/4 fails, so we catch this
        % failure below. Notice that this is only allowed because we
        % never backtrack over s/4 (because of the mode of replace_all/4).
replace_all(OldSub,NewSub,Exp,NewExp) :- s(Exp,[NewSub],[OldSub],NewExp),!.
replace_all(_,_,Exp,Exp).

% replace_alleqeq(+Old, +New, +OldExp, ?NewExp)
%
% Like Clam's replace_all/4, but does not unify meta-level 
% variables in the old subexpression.
%
replace_alleqeq(OldSub, NewSub, OldExp, NewExp) :-
	OldExp == OldSub, !,
	NewExp = NewSub.

replace_alleqeq(OldSub, NewSub, OldExp, NewExp) :-
	compound(OldExp),
	!,
	OldExp =.. [F | Args], 
	replace_alleqeq_(OldSub, NewSub, Args, NewArgs),
	NewExp =.. [F | NewArgs].

replace_alleqeq(_OldSub, _NewSub, OldExp, OldExp).

replace_alleqeq_(Old, New, [A | Arguments], [NewA | NewArgs]) :-
	replace_alleqeq(Old, New, A, NewA),
	!,
	replace_alleqeq_(Old, New, Arguments, NewArgs).

replace_alleqeq_(_,_,[],[]).

/* cancel_rule(?Exp,?RuleName:?Rule).  RuleName is the name of an
 * equation which allows us to replace Exp with some term that is an
 * instance of one of its proper subterms.  I.e. to wholely or partly
 * cancel Exp.  These things are stored at load time, so all we have
 * to do is to access the cached representation.  */
cancel_rule(Exp, RuleName:Rule) :-
    recorded( cancel, cancel( Exp, RuleName:Rule ), _ ).

/* subsumes(+S1,+S2): induction scheme S1 subsumes induction scheme
 * S2. The proper definition of subsumption is unclear at the moment.
 * Currently, subsumption just stands at being instantiation (ie. term
 * equality or term subsumption between the induction schemes).  */
subsumes(S1,S2) :-
    member(S,S1),
    instantiation(S,S2).

/* mininal(+Schemes,?Scheme): Scheme is an induction scheme which is a
 * minimal member of Schemes, that is: no other member of Schemes is
 * subsumed by Scheme.
 * 
 * For example:
 * :- minimal([s(x),times(x,y)],S).
 *    S = s(x) ;
 *    S = times(x,y) ;
 * :- minimal([s(x),s(s(x)),times(x,y)],S).
 *    S = s(x) ;
 *    S = times(x,y) ;  */
minimal(Schemes1,Scheme) :-
    remove_dups(Schemes1,Schemes),
    member(Scheme,Schemes),
    \+ (member(S,Schemes),
	S\=Scheme,
	subsumes(Scheme,S)).

/* minimally_subsumes(?Scheme,+Schemes): Scheme is the minimal Scheme
 * which subsumes all members of Schemes. That is: there is no other
 * scheme which also subsumes all members of Schemes but is itself
 * subsumed by Scheme.  */
minimally_subsumes(Scheme,Schemes) :-
    forall {S\Schemes}:subsumes(Scheme,S),
    \+ (scheme(_,S2),
        Scheme\=S2,
        subsumes(Scheme,S2),
        forall {S\Schemes}:subsumes(S2,S)
       ).

/* type_of/2 has moved to oyster-theory.pl */
/* transitive_pred/4 has moved to oyster-theory.pl */
/* canonical/1 has moved to oyster-theory.pl */
/* polarity/5 has moved to oyster-theory.pl */

	 % theorem(?Theorem,?Goal) checks if there exists a known theorem
	 % or lemma of name Theorem with goal Goal. This is obviously
	 % heavily Oyster dependent. Can be used to backtrack through all
	 % current theorems. 
	 %
	 % Old implementation of this used select/1 to cycle through all
	 % theorems, but this is so slooow that we now use our own
	 % intermediate representation of theorems (as record-ed theorem/4
	 % clauses, see the library.pl) which is indirectly linked to the
	 % Oyster representation if needed.
theorem(Thm,Goal) :-
    theorem(Thm,Goal,Type), member(Type,[thm,lemma]).
        % theorem(Thm,Goal,Type) is like theorem/2, but can be used to
        % retrieve other Type's of theorems as well, eg. eqn's, schemes
        % and even synth's (less useful). 
theorem(Thm,Goal,Type) :- 
    recorded(theorem, theorem(_,Type,Goal,Thm), _),
    \+ current_problem(Thm).     % Current theorem (if any) is excluded from
       		 % competition. 

        % condition_set/2 if for the expression Exp there exists a
        % complementary set of conditional rewrites then Conds
        % is instantiated to the associated list of conditions.
condition_set( Term, Conds ) :-
    recorded(condition_set, condition_set( Term,  Conds, _), _ ).
condition_set( Term, Conds, Name) :-
    recorded(condition_set, condition_set( Term,  Conds, Name), _ ).

        % rewrite(?Pos,+Rule,?Exp,?NewExp): NewExp is the result of
        % rewriting the subexpression in Exp at position Pos using
        % equation L=R in T.
        % Only one of Pos, Exp and  NewExp has to be instantiated, so this
        % can also be used to detect if and where a rewrite rule has
        % been applied, but not to generate all possible applications of
        % a rewrite rule.
        %
        % After computing the formal variables in the rewrite rule
        % (using quantify and untype), we use the Oyster
        % substitution predicate twice, once backwards to find the match
        % between formal and actual variables, and once forwards to do
        % the substitution specified by the rewrite rule.
rewrite(Pos,Rule,Exp,NewExp) :-
    matrix(TypedFormalVars,L=R in _,Rule), 
    untype(TypedFormalVars,FormalVars,_),
    exp_at(Exp,Pos,SubExp),
    s(L,ActualVars,FormalVars,SubExp),
    s(R,ActualVars,FormalVars,NewSubExp),
    replace(Pos,NewSubExp,Exp,NewExp).

        % canonical_form(+Exp,+Rules,?NewExp) NewExp is the result of
        % applying to Exp the rewrite rules from Rules as often as possible to
        % as many subexpressions as possible. This of course only makes
        % sense if Rules is confluent. The elements of the list Rules
        % are supposed to be of the form RuleName:Rule
        %
        % The simplest way of writing canonical_form/3 would be to
        % repeatedly call rewrite, trying as many rules on as many
        % subexpressions as possible. This "pure" version would look
        % simply like:
        %       canonical_form(Exp,Rules,NewExp) :-
        %               member(Rule,Rules),
        %               exp_at(Exp,Pos,_),
        %               rewrite(Pos,Rule,Exp,TmpExp),!,
        %               canonical_form(TmpExp,Rules,NewExp).
        % However, this is incredibly expensive, mainly because we call
        % rewrite on all possible subexpressions of Exp. In the version
        % below, the call to rewrite is expanded in-line, and before we
        % do the expensive Oyster substitution s/4, we see if the SubExp
        % we are about to try and rewrite has at least the right functor
        % and arity for the selected Rule to apply. This simple trick
        % reduces the costs of canonical_form 40-fold...
canonical_form(Exp,Rules,NewExp) :-
    member(_:Rule,Rules),
    matrix(TypedFormalVars,L=R in _,Rule),
        functor(L,F,N),
    untype(TypedFormalVars,FormalVars,_),
    exp_at(Exp,Pos,SubExp),
        functor(SubExp,F,N),
    s(L,ActualVars,FormalVars,SubExp),
    s(R,ActualVars,FormalVars,NewSubExp),
    replace(Pos,NewSubExp,Exp,TmpExp),!,
    canonical_form(TmpExp,Rules,NewExp).
canonical_form(Exp,_,Exp).

        % hyp(?Hyp,?HypList) checks if Hyp is among HypList. The methods
        % carry their own hypothesis list around, rather then using
        % Oyster's hyp_list, since we want to be able to add and remove
        % hypotheses at will and carry around meta-level annotations.
        %
        % CLaM hypothesis lists are lists of hypotheses
        % *OR* variable-terminated (i.e. extensible by unifcation)
        % lists of hypotheses.
        %
        % The latter option is intended to support middle-out (least
        % commitment deduction of hypotheses / addition of meta-level
        % annotations.   
        % 
hyp( M, [H|R] ) :-
    H \= (_:[_|_]),
    !,
    ( M = H ;
      hyp( M, R )
    ).
hyp( M, [ih:[_IndInfo | IndHyps] | OtherHyps] ) :-
    nv_member( M, IndHyps );
    hyp( M, OtherHyps ).

        % nv_member(?Member,?NV_term_list )
        % Succeeds if Member is a member of the (Prolog-) variable terminated
        % list MV_term_list.  (The latter are used to allow collections
        % of things to be extended middle-out)
        % 
nv_member( _, L ) :-
        var(L),
        !,
        fail.
nv_member( A, [A|_]).
nv_member( A, [_|L]) :-
        nv_member( A, L ).

/* V:H is an inductive hypothesis in Hs.  An inductive hypothesis is
   said to be in one of three phases, corresponding to position and
   role of that hypothesis in the proof-plan.

   raw: the hypothesis has not be used in any way; this is the
   state immediately following an induction.

   notraw(Ds): the hypothesis is being used during a phase of iterated
    weak-fertilization.  Ds is a list of: D=left for weak
    left-to-right, and D=right for weak right-to left, indicates how H
    was used on each application.  IN reverse order, obviously!

  used(Ds): the hypothesis has been used, and weak-fertilization is
    completed.  Ds is as above, and in addition, in the case of strong
    fertilization, Ds can be [strong].  If Ds==pw the hypothesis has
    been used in piecewise weak-fertilization */  

is_hypothesis(A,H):-
	member(A,H),
	\+ (A = (ih:[_|_])).			%not inductive
is_hypothesis(A,H):-
	inductive_hypothesis(_,A,H).

inductive_hypotheses(Status,IndHyps,Hs) :-
    member(ih:[ihmarker(Status,_)|IndHyps],Hs).

inductive_hypothesis(Status,V:H,Hs) :-
    inductive_hypotheses(Status,IndHyps,Hs),
    member(V:H,IndHyps).

active_inductive_hypothesis(V:H,Hs) :-
    inductive_hypothesis(Status,V:H,Hs),
    (Status = raw; Status = notraw(_)).


/* inductive_hypothesis(Status,V:H,H1,NStatus,H2): V:H is an inductive
   hypothesis in both H1 and H2, with status Status in H1 and status
   NStatus in H2.  H1 and H2 agree on all other elements.  */
inductive_hypothesis(Status,V:H,
		     [ih:[ihmarker(Status,XX),V:H]|Rest],
		     NewStatus,
		     [ih:[ihmarker(NewStatus,XX),V:H]|Rest]) :-
    !.
inductive_hypothesis(Status,V:H, [Hyp|Rest], NewStatus, [Hyp|RRest]) :-
    inductive_hypothesis(Status,V:H, Rest, NewStatus, RRest).

/* H and HH are the same but for notraw hypotheses in H are marked as
        used in HH  */
notraw_to_used([ih:[ihmarker(notraw(Ds),XX),V:H]|Rest],
	[ih:[ihmarker(used(Ds),XX),V:H]|RestUSED]) :-
    !,
    notraw_to_used(Rest, RestUSED).
    
notraw_to_used([Hyp|Rest], [Hyp|RRest]) :-
	notraw_to_used(Rest, RRest).
notraw_to_used([],[]).

/* raw_to_used(Hs,Hyps,NHs): NHs is as Hs but all hypotheses in Hyps
appearing in NHs are marked as used in NHs */

raw_to_used(Hs, [], Hs).
raw_to_used(Hs, [V|Vs], NHs) :-
    raw_to_used(Hs,V,H1),
    raw_to_used(H1,Vs,NHs).

raw_to_used([ih:[ihmarker(raw,XX),V:H]|Rest],V,
	    [ih:[ihmarker(used([strong]),XX),V:H]|Rest]) :- !.
raw_to_used([Hyp|Rest], V, [Hyp|RRest]) :-
    !,raw_to_used(Rest, V, RRest).
raw_to_used(_,_,_) :-
    clam_error('raw_to_used/3: V does not appear in Hs').



/* inductive_hypotheses(VH,VH2,Hyps1,Hyps2): VH is a list of induction
   hypotheses appearing in Hyps1; Hyps2 is as Hyps1 but VH2 replaces
   VH */
inductive_hypotheses([],[],H,H).
inductive_hypotheses([V:H|VHs],[V:NewH|NewVHs],H1,H3) :-
    append(Pre,[ih:[ihmarker(Status,XX),V:H]|Post],H1),
    append(Pre,[ih:[ihmarker(Status,XX),V:NewH]|Post],H2),
    inductive_hypotheses(VHs,NewVHs,H2,H3).

        % hfree( ?VarList, +HypList )
        % VarList is a list of (distinct) variable names free in the
        % hypothesis list HypList
        % 
hfree( [V|R], H ) :-
    var(V),
    genvar(V),
    \+ hyp( V:_, H ),
    !,
    hfree( R, [V:dummy|H] ).
hfree( [V|R], H ) :-
    \+ hyp( V:_, H ),
    hfree( R, [V:dummy|H] ).
hfree( [], _ ).

        % del_hyp( +Hyp, +HypList, -RestHypList )
        % Deletes hypothesis Hyp from HypList giving RestHypList
        % 
del_hyp( M, L, RL ) :-
    selectchk( M, L, RL ),
    !.
del_hyp( M, L, [RHL|RL] ) :-
    select( HL, L, RL ),
    nv_member( M, HL ),
    selectchk( M, HL, RHL ),
    !.

del_hyps( [DH|DL], HL, RL ) :-
    del_hyp( DH, HL, PRL ),
    del_hyps( DL,PRL, RL ).
del_hyps( [], RL, RL ).

/* GG is universal closure of G (actually: under H) */
universal_closure(H,G,GG) :-
    freevarsinterm(G,Vs),
    map_list(Vs,V :=> (V:T),hyp(V:T,H),VTs),
    precon_matrix(VTs,[]=>G,GG).

        % universal_var(+Seq,?Var): Var (of the form V:T) is a
        % universally quantified variable in the sequent Seq. This can
        % be because V:T appears explicitly quantified in the goal of
        % Seq, or because it appears among the hypotheses (being
        % previously intro'd).
universal_var(_==>G,Var:T) :- matrix(Vars,_,G),member(Var:T,Vars).
universal_var(H==>G,Var:T) :- hyp(Var:T,H), thereis {Pos}: exp_at(G,Pos,Var).

/* instantiate(Hyps,Frees,+G1,?G2,?G2Vals) the variables quantified in
   G1 can be instantiated with the values of G2Vals to obtain G2.  All
   variables quantified in G1, other than those in Frees, must be
   instantiated, thus:

          ** ??? **
	  ** next doesn't look like an example of this, y not instantiated **
   
          instantiate([],[],x:pnat=>y:pnat=>f(x,y),y:pnat=>f(1,y),[1])

	  ** this call fails in this version ! **

   Hyps is a hypothesis list that provides context for type-guessing
   when there are type variables in G1. */
instantiate(G1,G2,Vals) :- 
    instantiate([],[],G1,G2,Vals).
instantiate(Hs,G1,G2,Vals) :- 
    instantiate(Hs,[],G1,G2,Vals).
instantiate(Hs,Frees,G1,G2,Vals) :- 
    instantiate(Hs,Frees,G1,G2,[],Vals,[],[]).
instantiate(Hs,Frees,Var:u(_)=>G1,G2,Vars,Vals,TyVars,Ts) :-
    !,instantiate(Hs,Frees,G1,G2,[Var|Vars],Vals,[Var|TyVars],Ts).
instantiate(Hs,Frees,Var:T=>G1,G2,Vars,Vals,TyVars,Ts) :-
    freevarsinterm(T,FVs),
    once((member(TV,TyVars),member(TV,FVs))),
    !,instantiate(Hs,Frees,G1,G2,[Var|Vars],Vals,TyVars,[T|Ts]).
instantiate(Hs,Frees,Var:_T=>G1,G2,Vars,Vals,TyVars,Ts) :-
    !,instantiate(Hs,Frees,G1,G2,[Var|Vars],Vals,TyVars,[none|Ts]).
instantiate(Hs,Frees,Var1:_T1#G1,Var2:_T2#G2,Vars,Vals,TyVars,Ts):-
        replace_all(Var2,Var1,G2,GG2),!,
        instantiate(Hs,Frees,G1,GG2,Vars,Vals,TyVars,[none|Ts]).
instantiate(Hs,Frees,G1,G2,Vars,Vals,TyVars,Ts) :-
    %% It may be the case that it is not necessary to instantiate Vars
    %% in G1 in order to obtain G2.  In this case, RevVals will
    %% contain Prolog variables.  This can cause problems with the
    %% correspondance between the proof-plan and the tactic, since the
    %% plan is typically less precise about variable binding.  For
    %% example, during weak fertilization of
    %%
    %% z:pnat, x:pnat=>f(x)=s(0) in pnat ==>x:pnat=>f'(x)=s(0) in pnat
    %% 
    %% the proof-plan predicts ==>x:pnat=>f'(x)=f(x) in pnat, but this
    %% is nothing more than fortuitious, since the variable x does not
    %% appear on the rhs of the equality in the hypothesis.  So it can
    %% only be used as a rewrite with care.  The tactic might just as
    %% easily produce x:pnat=>f'(x)=f(z) in pnat, since z is of
    %% suitable type.  The tactic needs to take this care, and choose
    %% the instantiation for x as was assumed by the meta-level.
    %% Frees is a list of variables which are to be used to provide
    %% these instantiations.  If Frees is unbound, then ignore such
    %% concerns.  (This is needed when the instantiation is not a
    %% weak-fertilization, for example.)

    s(G1,RevVals,Vars,G2),
    reverse(RevVals,RevRevVals),
    %% nil case means that we are probably inside a casesplit, so the
    %% unversals of the casesplit will have been intro'ed.  Hence the
    %% Frees may be empty, but the Vals will be non-empty.  In general
    %% this will not work: the general problem is when Vals and Frees
    %% are of different lengths.  In that case, we are in the
    %% situation described above. :-(
    ((var(Frees);\+ lengtheq(Frees,RevRevVals))			
      -> RevRevVals  = Vals
      ; (zip(Zip,RevRevVals,Frees),		% do the check
	 map_list(Zip,RV-V :=> RVG,
		  (var(RV)->(RV=V,RVG=V); RVG=RV),Vals))),
    /* CHECK HERE THAT ONLY TYPE VARIABLES ARE VAR */
    /* instantiate type variables */
    
    map_list_filter(Vars,V:=>V,\+ member(V,TyVars),NTVars),
    s_map(NTVars,RevVals,Vars,InstVars),
    s_map(Ts,RevVals,Vars,InstTs),
    
    instantiate_type_variables(InstVars,InstTs,Hs),
    if(\+ground(Vals),clam_warning('Unable to instantiate all type parameters.')).

instantiate_type_variables(TI,_) :-
    ground(TI),!.
instantiate_type_variables(TIR,Hs) :-
    reverse(TIR,TI),
    zip(TI,Vs,Ts),
    instantiate_type_variables(Vs,Ts,Hs),
    if(\+ground(TIR),
       clam_warning('Unable to instantiate all type parameters.')).
instantiate_type_variables([],[],_Hs).
instantiate_type_variables([Val|Vals],[ValType|Ts],Hs) :-
    guess_type(Val,Hs,ValType),!,
    instantiate_type_variables(Vals,Ts,Hs).
instantiate_type_variables([_|Vals],[_|Ts],Hs) :-
    instantiate_type_variables(Vals,Ts,Hs).
    
s_map([T|Ts],RevVals,Vars,[NT|NTs]) :-
    s(T,RevVals,Vars,NT),
    s_map(Ts,RevVals,Vars,NTs).
s_map([],_RevVals,_Vars,[]).


        % groundp(+X) succeeds iff X is ground.
groundp(X) :- \+ \+ numbervars(X,0,0).

        % metavar(Var) checks if Var is a meta-linguistic variable.
        % Since Prolog is our meta-language, meta-linguistic variables
        % are Prolog variables. You guessed: This predicate is for
        % cosmetic purposes only. We wouldn't want ugly Prolog
        % predicates like var/1 in our code, would we.
metavar(Exp) :- var(Exp).

/* constant/2 has moved to oyster-theory.pl */

        % matrix(?TypedVarList,?T1,?T2): Martrix is the matrix of
        % Formula, that is: all quantifiers at the front of Formula have
        % been removed from Matrix. VarList is the list of variables
        % involved in these quantifiers (in the same order as the
        % quantifiers occured in Formula). Actually, this (currently)
        % only works for universal quantifiers.  
matrix([],T1,T1) :- T1 \= (_:_=>_).
matrix([V:T|Vs],T1,V:T=>T2) :- matrix(Vs,T1,T2).

/* precon_matrix(?TypedVarList,?PreConds=>?T1,?T2) Let a prefix R be
 * either v:t or p Then T2 is of the form R=>...R=>T1, where
 * TypedVarList is the collection of v:t's for all R of the first
 * form, and PreConds are the p's for all R of the second form.  Note
 * that there is much backtracking here, since T2 may be of the form
 * R=>T2'. 
 *
 * This is a rather strange specification: why should we want to do
 * this?  I understand the need for precon_matrix in the case were
 * TypedVarList=[] but in other cases usage is probably bogus.  */
precon_matrix([V:T|Vs],T1,V:T=>T2) :-
%    !,						% this cut is suspicious
    precon_matrix(Vs,T1,T2).
precon_matrix(Vars,[H|Hs]=>Body,H=>T2) :- 
    precon_matrix(Vars, Hs=>Body,T2).
precon_matrix([],[]=>Body,Body).

/* META_PRED
 *
 * Definitions of predicates/functions used in the extended
 * method-specification language to support all the fancy
 * ``middle-out deduction'' of induction hypotheses.  */

/* A.Ireland 11/2/91
 *
 * Extensions to existing meta-predicates used within the pre- and post-
 * condition slots of methods. These predicates were introduced in the
 * course of extending CLAM to deal with rippling existentially
 * quantified goals and rippling-in after weak fertilization 
 * (see note 636 for more details).  */
annotations(T,W,GGG,G):-
    \+ var(G),!,
    wave_fronts(GG,W,G),
    sinks(GGG,T,GG).
annotations(T,W,G,GGG):-
    \+ var(T),
    \+ var(W),
    \+ var(G),
    wave_fronts(G,W,GG),
    sinks(GG,T,GGG).

unannotated(GAnn,GNoAnn) :-
    annotations(_,_,GNoAnn,GAnn).

/* sinks(?T1, ?SinksSpec, ?T2): T2 is as T1, except that T2 has sinks
 * in the positions specified by, SinksSpec, a list of term
 * positions. Due to the generous mode of this predicate, sinks/3, can
 * be used to insert (mode sinks(+,+,-)) or to delete sinks (mode
 * sinks(-,+,+)), or locate sinks (mode sinks(-,-,+)). At least one of
 * T1 of T2 must be instantiated.  */
sinks(T,L,TT):- \+ var(TT),!,delete_sinks(TT,L,T).
sinks(T,L,TT):- \+ var(T), \+var(L), !,insert_sinks(T,L,TT).

/* mark-sinks(+Bindings, ?Term, ?NewTerm): Bindings is a list of
 * bindings. The Term and NewTerm are identical except that all
 * variables in Bindings which occur in Term are annotated as sinks in
 * NewTerm.  This code assumes that all variables in Bindings occur
 * free in both terms.  (One of Term or NewTerm must be ground.)  */
id_map(X,X).
sink_map(Var,Var,SinkVar) :- 
    issink(SinkVar,Var),!.
sink_map(_Var,Leaf,Leaf).

mark_sinks([],Term,Term).
mark_sinks([Binding|VarList],Term1,Term3):-
    var(Term3),!,
    (Binding = (Var:_T)  ; Binding = Var),!,
        status_tree_map(sink_map(Var),id_map, Term1,Term2),
    mark_sinks(VarList,Term2,Term3),!.
mark_sinks([Binding|VarList],Term1,Term3):-
    var(Term1),
    (Binding = (Var:_T)  ; Binding = Var),!,
    issink(SV,Var),
    replace_all(SV,Var,Term3,Term2),
    mark_sinks(VarList,Term1,Term2),!.

insert_sinks(Term1,[],Term1).
insert_sinks(Term1,[Pos|PosList],Term3):- !,
    exp_at(Term1,Pos,Exp),
    issink(SinkExp,Exp),
    replace(Pos,SinkExp,Term1,Term2),
    insert_sinks(Term2,PosList,Term3).

delete_sinks(Term1,PosList,Term2):-
     delete_sinks(Term1,[],PosList,Term2),!.
delete_sinks(Term1,_,PosList,Term2) :- (atomic(Term1);var(Term1)),!,
					Term1 = Term2,PosList = [].
delete_sinks(SinkTerm1,Term1Pos,[Term1Pos],Term1):-
    issink(SinkTerm1,Term1),!.
delete_sinks(WF1, InPos,OutPos,WF2) :- 
    iswf(WF1,Typ,Dir,Term1),
    iswf(WF2,Typ,Dir,Term2),
    delete_sinks(Term1,InPos,OutPos,Term2),!.
delete_sinks(Hole1,InPos,OutPos,Hole2) :-
    iswh(Hole1,Term1),
    iswh(Hole2,Term2),
    delete_sinks(Term1,InPos,OutPos,Term2),!.
delete_sinks([H1|T1],[N|L],PosList,[H2|T2]):- !,
     delete_sinks(H1,[N|L],PosList1,H2),
     N1 is N + 1,
     delete_sinks(T1,[N1|L],PosList2,T2),!,
     append(PosList1,PosList2,PosList).
delete_sinks(Term1,PosListIn,PosListOut,Term2):-
     Term1 =.. [F|Args],
     delete_sinks(Args,[1|PosListIn],PosListOut,ArgsNew),
     Term2 =.. [F|ArgsNew].

delete_mark_sinks(Vs,T1,T2) :-
    delete_sinks(T1,_,T),
    mark_sinks(Vs,T,T2).

/* THIS IS NOT DOCUMENTED */
sink_expansions([],S,S).
sink_expansions([WF-WHoles/_|Rest],Sinks,[WF|NewSinks]):-
	 member(WH,WHoles),
	 append(WH,WF,WHPos),
	 member(WHPos,Sinks),
	 delete(Sinks,WHPos,ModSinks),
	 sink_expansions(Rest,ModSinks,NewSinks).
sink_expansions([_WSpec|Rest],Sinks,NewSinks):-
	 sink_expansions(Rest,Sinks,NewSinks).

no_sinks(G,GG) :-
    sinks(GG,_,G).
strip_sinks([],[]).
strip_sinks([H==>G|R],[H==>GG|RR]):-
	 sinks(GG,_,G),
	 strip_sinks(R,RR).


/* strip_redundant_sinks(+T1, -T2): T1 and T2 are lists of goal
 * sequents. The corresponding goal sequents from each list are
 * identical except that for each goal in T1 which contains sinks but
 * no wave-fronts the associated goal in T2 contains no sinks, unless
 * that sink is around a compound term.  */
strip_redundant_sinks([],[]).
strip_redundant_sinks([H==>G|R],[H==>GG|RR]):-
	 wave_fronts(_,[],G),!,			%cut added img
	 sinks(G1,SinkSpec,G),
	 findset(SinkPos,(member(SinkPos,SinkSpec),
			  exp_at(G1,SinkPos,Sink),
			  \+ atomic(Sink)),
		 SSinkSpec),
	 sinks(G1,SSinkSpec,GG),		     
	 strip_redundant_sinks(R,RR).
strip_redundant_sinks([H==>G|R],[H==>G|RR]):-
	 strip_redundant_sinks(R,RR).

/* strip_meta_annotations(+T1, -T2) T1 and T2 are identical except
 * that all meta-level annotations which appear in T1 are eliminated
 * from T2.  */
strip_meta_annotations([],[]) :- !.
strip_meta_annotations([H==>G|R],[H==>GG|RR]) :-
	!,
	strip_meta_annotations(G,GG),
	strip_meta_annotations(R,RR).

strip_meta_annotations(G,GG):-
	annotations(_,_,GG,G).

/* skeleton_position(+GoalPos, +Goal, -HypPos ): if Pos is a position
 * inside the skeleton of G, HPos is the position w.r.t. this
 * position.  If Pos is not a position in the skeleton, fail.  */
skeleton_position(Pos,G,HPos) :-
    wave_fronts(_,Waves,G),
    skeleton_position(Waves,G,Pos,HPos).

skeleton_position(Waves,G,Pos,HypPos) :-
    \+ Waves = [],
    %% See if Pos is a prefix position of a wave-front inside G
    append(WFPrefix,WFOffset,Pos),
    member(WFOffset-HoleList/[_,_], Waves),
    !,
    %% Pos is inside a wave-front.  See which hole it refers to
    member(Hole,HoleList),
    append(Hole,_HoleOffset,WFPrefix),
    append(Hole,WFOffset,AbsHolePos),
    exp_at(G,AbsHolePos,NewG),

    %% find all the sub-wave-fronts of this term (rather than
    %% re-computing them via wave_front(_,SubWaves,NewG).

    findall(SubWFPrefix-SubHoleList/[T,D],
	    (member(SubWFPrefix-SubHoleList/[T,D], Waves),
	     append([_|[_|_SubWF]],WFOffset,SubWFPrefix)),
	    SubWaves),
    append(Remainder, AbsHolePos, Pos),
    skeleton_position(SubWaves,NewG,Remainder,HPos),
    append(HPos,WFOffset,HypPos).

%% this case for empty Waves and when Pos is not inside a wave-front.
skeleton_position(_Waves,_G,Pos,Pos).

/* ground-sinks(+Instan, +Lhs, +Rhs, ?SubTerm)
 * Instan is a list of sink instantiations. For all members of Instan
 * which are prolog variables an instantiation is calculated using Lhs
 * and Rhs, the left and right hand sides of the current goal. SubTerm
 * is a subexpression of Rhs in which uninstantiated sinks may occur.  */
ground_sinks([],_,_,_).
ground_sinks([Var|T],GL,GR,GSub):-
         var(Var),
	 sinks(_GR1,GRsinkPos,GR),
         sinks(GL1,GLsinkPos,GL),
	 diff(GLsinkPos,GRsinkPos,SinkPos),
	 instan_sinks(GL1,SinkPos,Var),
         ground_sinks(T,GL,GR,GSub).
ground_sinks([_|T],GL,GR,GSub):-
         ground_sinks(T,GL,GR,GSub).

instan_sinks(_Term,[],_).
instan_sinks(Term,[Pos|PosL],Var):-
         exp_at(Term,Pos,Var),
	 instan_sinks(Term,PosL,Var).

/* matrix(?VarList,?EVarList,?Matrix,?Formula):
 * matrix/4 is as matrix/3 except it is extended to deal with
 * existential quantification. EVarList is a list with elements of the
 * form MetaVar-ObjVar:Typ where MetaVar is the prolog variable which
 * replaces the object-level variable ObjVar in Formula to give
 * Matrix.  */
matrix([],[],T1,T1) :- T1 \= (_:_=>_), T1 \= (_:_#_).
matrix([V:T|As],Es,T1,V:T=>T2) :- matrix(As,Es,T1,T2).
matrix(As,[V-V:T|Es],T1,V:T#T2) :- 
			\+ var(T1),
			matrix(As,Es,T1,T2).
matrix(As,[MetaV-VV:T|Es],T1,V:T#T2) :- 
                        var(T1),
		        wave_fronts(VV,_,V),
                        replace_all(V,MetaV,T2,T3),
			matrix(As,Es,T1,T3).

/* adjust_existential_vars(+EVars, +VarBase, -NewEVars, -SubstL):
 * EVars is an association list with elements of the form Term-Var:Typ
 * where the prolog term Term denotes the instantiation for the existential
 * variable Var of type Type. The instantiation may be partial so additional 
 * existential variables may be introduced. To prevent the introduction of
 * name clashes the list of current bindings, VarBase, is required. NewEVars
 * and SubstL denote the refined list of existential variables and the
 * associated substitution list respectively.  */
adjust_existential_vars([],_,[],[]).
adjust_existential_vars([Term-Var:Typ|R],Hbase,[Term-Var:Typ|RR],SubstList):- 
	var(Term),!,
	adjust_existential_vars(R,Hbase,RR,SubstList).
adjust_existential_vars([Term-Var:Typ|Rest],Hbase,MetaVars,[Var:Typ,TTerm|RRest]):-
	Term \= Var,!,
	wave_fronts(TTerm,_,Term),
	collect_meta_vars(TTerm,Typ,Hbase,HHbase,MetaVars1),
	adjust_existential_vars(Rest,HHbase,MetaVars2,RRest),
	append(MetaVars1,MetaVars2,MetaVars).
adjust_existential_vars([_|Rest],Hbase,MetaVars,SubstList):-
	adjust_existential_vars(Rest,Hbase,MetaVars,SubstList).

% Separated into collect_meta_vars and collect_meta_vars_list
% because clauses 3 and 4 of the original collect_meta_vars were
% overlapping and causing non-termination.
%
collect_meta_vars(MetaVar,Typ,Hbase,HHbase,[MetaVar-ObjVar:Typ]):- 
	var(MetaVar),
	hfree([ObjVar],Hbase),
        append([ObjVar:Typ],Hbase,HHbase).
%	wave_fronts(ObjVar,[[]-[]/[soft,_]],AnnObjVar).
collect_meta_vars(Atom,_,Hbase,Hbase,[]):- atomic(Atom).
collect_meta_vars(Term,Typ,Hbase,HHbase,Vars):-
	compound(Term),                 % for non-atomic case,
	Term =.. [_|Args], Args=[_|_],  % force Args non nil; 
                                        % atomic case is above
	((Typ = BTyp list,
	 collect_meta_vars_list(Args,[BTyp,Typ],Hbase,HHbase,Vars));
	(collect_meta_vars_list(Args,[Typ],Hbase,HHbase,Vars))).

collect_meta_vars_list([],_,Hbase,Hbase,[]).

collect_meta_vars_list([H|T],[HTyp|TTyp],Hbase,HHbase,Vars):-
	collect_meta_vars(H,HTyp,Hbase,Hbase1,HVars),
	collect_meta_vars_list(T,TTyp,Hbase1,HHbase,TVars),
	append(HVars,TVars,Vars).
			
/* wave_terms_at(+Exp,?Pos,?SubExp) */
wave_terms_at(Exp,Pos,SubExp):-
    ann_exp_at(Exp,Pos,SubExp),
    \+ Pos = [0|_],				%dont want functors
    \+ atomic(SubExp),
    contains_wave_fronts(SubExp).

metavarsinterm(Term,Vars):-
    metavars(Term, Vars).

metavars(Term, [Term]):-
    var(Term),!.
metavars(Term, []):-
    atomic(Term),!.
metavars(Term, Vars):-
    Term =.. [_|Args],
    metavarslist(Args, Vars).

metavarslist([], []).
metavarslist([Arg|Args], AllVars):-
    metavars(Arg, VarsArg),
    metavarslist(Args, VarsArgs),
    append(VarsArg, VarsArgs, AllVars).

pairs([],[]).
pairs([H|T],LL):-
    map_list(T,I:=>O,O = [H,I],L1),
    pairs(T,L2),
    append(L1,L2,LL).

singles(L,LL):-
    map_list(L,I:=>O,O = [I],LL).


%*********************
%*
%*  unannotated_hyps( +AH, -H )
%*  - H is hypotheses AH with all annotations stripped.
%*
%********************* 
unannotated_hyps( [_:[Hd|Tl]|RH], UH ) :-
    findall( WSH,
             ( nv_member(V:H,[Hd|Tl]),
               wave_fronts(WSH,_,V:H)
             ),
             WSIH ),
    append( WSIH, RUH, UH ),
    unannotated_hyps( RH, RUH ),
    !.
unannotated_hyps( [V:H|RH], [V:H|RUH] ) :-
    unannotated_hyps( RH, RUH ),
    !.
unannotated_hyps( [_|RH], RUH ) :-
    unannotated_hyps( RH, RUH ).
unannotated_hyps( [], [] ).


%*********************
%*
%*  nonind_hyps( +AH, -H )
%*  - H is hypotheses AH with all annotations stripped, 
%*  ignoring inductions hyps
%*
%********************* 
nonind_hyps( [_:[_Hd|_Tl]|RH], UH ) :-
    nonind_hyps( RH, UH ),
    !.
nonind_hyps( [V:H|RH], [V:H|RUH] ) :-
    nonind_hyps( RH, RUH ),
    !.
nonind_hyps( [], [] ).


/* ann_exp_at(+TopLevel,?Flag,+Exp,?Pos,?SubExp).
 * much the same as exp_at/3;
 * Flag and TopLevel are tokens from the set {in_front,in_hole}.
 * TopLevel indicates whether Exp (a term) is a wave-front or a
 * wave-hole.  Normally, this is "in_hole" since that corresponds to
 * well-annotated terms;  occasionally, it is necessary to pass 
 * the contents of a wave-front to ann_exp_at (ie a term in which the
 * uppermost annotation (if any) is a wave-hole, not a wave-front); in
 * this case TopLevel should be set to "in_front".
 * 
 * Flag indicates the state of SubExp within Exp, whether it is in a
 * front or a hole; for example to generate possible terms for
 * rippling (i.e., terms which are well-annotated) use:
 * 
 * ann_exp_at(in_hole, in_hole, Exp, Pos, SubExp)
 * 
 * in this way, you are assured (*) that SubExp is a well-annotated
 * term, suitable for rippling.
 * 
 * NOTE(*).  All this comment (and the code too) assumes that (modulo
 * the setting of TopLevel) Exp is a Well-Annotated Term. 
 *
 * ann_exp_at/3 is a convenient wrapper.  */
ann_exp_at(Exp,Pos,SubExp) :-
    ann_exp_at(in_hole,in_hole,Exp,Pos,SubExp).

ann_exp_at(Flag, Flag, Var,[],Var) :- var(Var),!.

ann_exp_at(in_front, in_hole, HoleExp, [], Exp) :-
    striphole(HoleExp,Exp),!.
ann_exp_at(in_hole, _, HoleExp,[],_) :-
    striphole(HoleExp,_),
    !,clam_error('ann_exp_at/5: a wave-hole appears inside a wave-hole.').
ann_exp_at(Flag, Flag, Exp,[],Exp).
ann_exp_at(in_front, in_hole, Sink,[],_) :-
    stripsink(Sink,_),
    !,clam_error('ann_exp_at/5: a sink appears inside a wave-front.').
ann_exp_at(_, in_front, WF,[],Exp) :- 
    stripfront(WF,_,_,Exp).
ann_exp_at(Current, Flag, Exp,[N|P],SubExp) :-
    ann_exp_at(Current, Flag, Exp,[N|P],SubExp,_).

ann_exp_at(_Current, _Flag, _,[],_,_) :- fail.
ann_exp_at(Current, Flag, Exp, Pos, SubExp, SupSubExp) :-
    numbervars(Pos,0,0),!,
    reverse(Pos,RPos),
    r_ann_exp_at(Current, Flag, Exp,RPos,SubExp,SupSubExp).
ann_exp_at(Current, Flag, Exp, Pos, SubExp, SupSubExp) :- 
    r_ann_exp_at(Current, Flag, Exp, RPos, SubExp, SupSubExp),
    reverse(RPos, Pos).

r_ann_exp_at(_Current, _Flag, Exp,_,_,_) :- var(Exp),!,fail.
r_ann_exp_at(_Current, _Flag, Exp,_,_,_) :- atomic(Exp), !, fail.
/* Subsequently exploit that Exp is compound */

r_ann_exp_at(in_front, Flag, Hole,[N],SubExp,SupExp) :- 
    iswh(Hole,Exp),
    r_ann_exp_at(in_hole, Flag, Exp,[N],SubExp,SupExp).
r_ann_exp_at(in_hole, _, Hole,_,_,_) :- 
    iswh(Hole,_),
    !,clam_error('r_ann_exp_at/6: a wave-hole appears inside a wave-hole.').

r_ann_exp_at(Current,Flag, SinkExp,[N],SubExp,SupExp) :- 
    issink(SinkExp,Exp),
    r_ann_exp_at(Current,Flag, Exp,[N],SubExp,SupExp).

r_ann_exp_at(in_hole,Flag,WF,[N], SubExp,WF) :- 
    iswf(WF,_,_,Exp),
    r_ann_exp_at(in_front,Flag,Exp,[N],SubExp,Exp).
r_ann_exp_at(in_front,_,WF,_, _,_) :- 
    iswf(WF,_,_,_),
    !,clam_error('r_ann_exp_at/6: a wave-front appears inside a wave-front.').
r_ann_exp_at(in_front,in_hole,SupExp, [N], Exp, SupExp) :-
    \+ iswf(SupExp,_),
    \+ iswh(SupExp,_),
    \+ issink(SupExp,_),
    genarg0(N,SupExp,Exp1), N > 0,		%[0] is in a front too
    striphole(Exp1,Exp).

/* check for a wave-front just below here */
r_ann_exp_at(in_hole,in_front,SupExp, [N], Exp, SupExp) :-
    \+ iswf(SupExp,_),
    \+ iswh(SupExp,_),
    \+ issink(SupExp,_),
    genarg0(N,SupExp,Exp1), N > 0,		% looking for an argument
    stripfront(Exp1,_,_,Exp).

r_ann_exp_at(in_hole,in_hole,SupExp, [N], Exp, SupExp) :-
    \+ iswf(SupExp,_),
    \+ iswh(SupExp,_),
    \+ issink(SupExp,_),
    genarg0(N,SupExp,Exp1), 
    (iswh(Exp1)->
      clam_error('r_ann_exp_at/6: a wave-hole appears inside a wave-hole.');
      Exp1=Exp).

r_ann_exp_at(in_front,in_front,SupExp, [N], Exp, SupExp) :-
    \+ iswf(SupExp,_),
    \+ iswh(SupExp,_),
    \+ issink(SupExp,_),
    genarg0(N,SupExp,Exp1),
    (\+iswh(Exp1)->Exp1=Exp).

r_ann_exp_at(in_front,Flag,HoleExp,[N1,N2|Ns], SubExp,
	     SupExp) :-
    striphole(HoleExp,Exp),!,
    r_ann_exp_at(in_hole,Flag,Exp,[N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(in_hole,_Flag,HoleExp, [_N1,_N2|_Ns], _SubExp, _SupExp) :- 
    iswh(HoleExp),
    !,clam_error('r_ann_exp_at/6: a wave-hole appears inside a wave-hole.').

r_ann_exp_at(in_hole,Flag,SinkExp,[N1,N2|Ns], SubExp, SupExp) :-
    stripsink(SinkExp,Exp),!,
    r_ann_exp_at(in_hole,Flag,Exp,[N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(in_front,_Flag,Sink, [_N1,_N2|_Ns], _SubExp, _SupExp) :- 
    issink(Sink),
    !,clam_error('r_ann_exp_at/6: a sink appears inside a wave-front.').

r_ann_exp_at(in_hole,Flag,WF,
	     [N1,N2|Ns], SubExp, SupExp) :- 
    iswf(WF,_,_,Exp),!,
    r_ann_exp_at(in_front, Flag, Exp, [N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(Current, Flag, Exp, [N1,N2|Ns], SubExp, SupExp) :-
    genarg0(N1,Exp,Arg),
    r_ann_exp_at(Current, Flag, Arg, [N2|Ns], SubExp, SupExp).


/* contains_wave_fronts(+Term)
 * Succeeds when there is at least one wave-front in Term.  */
contains_wave_fronts(Term) :-
    wave_fronts(_,[_|_],Term),!.

/* SubTerm is a subterm of Term that is inside some wave_front.  NOTE:
   only gives single solution: useful mode is (+,+) (use ann_exp_at
   directly for more generous mode)  */
inside_wave_front(SubTerm,Term) :-
    ann_exp_at(in_hole,in_front,Term,_,SubTerm),!.

/* Stuff to construct complementary wave-rule sets */

/* complementary_sets(?CNames): CNames is a list of the form
 * [C1-R1-Dir1-Name1, ... Cn-Rn-Dirn-Namen]-LHS such that LHS :=> Ri
 * is a rewrite conditional upon Ci (a single condition, not a list of
 * same), with name Namei, and direction Diri.  n>1.  Pictorially:
 *
 *    Name1: C1 -> LHS :=> R1,
 *    :
 *    Namen: Cn -> LHS :=> Rn
 * 
 * These complementary rewrites are drawn from the rewrite database
 * extant when complementary_sets/1 is called.  Notice that the
 * Namei's need not belong to the same family of definitions (by
 * family I mean e.g., member1, member2, member3).  Thus lemmas etc
 * are included.  Noteice also that the Diri's must agree: imp(left)
 * and imp(right) disagree at a given position.
 * 
 * For example, given usual definitions of member and insert we have:
 * CNames =
 * [[(A2<B2=>void)-B2::insert(A2,C2)-equ(_,left)-insert3,
 *   (A2<B2)-A2::B2::C2-equ(_,left)-insert2]-insert(A2,B2::C2),
 *  [(A4=B4 in int=>void)-member(A4,C4)-equ(_,left)-member3,
 *   (A4=B4 in int)-{true}-equ(_,left)-member2]-member(A4,B4::C4)]
 *
 * NB.  The casesplit methods normally use complementary sets to
 * determine appropriate cases when rippling (or some other rewriting)
 * becomes blocked.  Such use obviously requires that the disjunction
 * of all the cases (C1\C2\...\Cn) be provable for the casesplit to be
 * sound.  However, complementary sets does not enforce this
 * condition: it simply collects rewrites with similar LHSs.
 * Consequently it may happen that a pair of rules may result in a
 * complementary set but that the disjunction is not provable or is
 * not pre-stored caseplit lemma.  
 *
 * It is also possible for complementary sets to be formed from
 * cross-family rewrites: an example of this occurrs with greaterplus2
 * and less4:
 * 
 * greater2: x:pnat=>greater(x,0)=>x=0 in pnat=>void
 * less4:    x:pnat=>less(0,x)   =>x=0 in pnat=>void
 * 
 * which yield rewrites:
 *              greater(x,0) -> x=0 in pnat ==> void
 *              less(0,x)    -> x=0 in pnat ==> void
 *
 * which give a complementary set.  This is not a very useful
 * casesplit since the rhs are identical: we choose to drop such
 * complementary sets.  It seems unlikely that the "dynamic" form of
 * complementary sets (see below) will be required in practice, and
 * for this reason, a comp_set record is used to pre-compute
 * complementary sets from a "family" (eg member1, member2, member3)
 * at load time.  (See library code.)  */

complementary_sets(CNames) :-
    %% This assumes that the rewrites have already been added
    findall(C-L-R-Dir-TI-Name,
	    (rewrite_rule(L,R,C,Dir,TI,_,Name,_),
	     \+ C == [], true), Cs),		% C may be a var
    %% collect together all the ones with the same left-hand-sides
    collect(Cs,CNames).

/* complementary_sets(+Names,?CNames). As complementary_sets/1, but
 * first parameter is a list of rewrite names to consider.  For
 * example, complementary_sets([member1, member2, member3], CNames)
 * restricts attention to the member family of definitions.  */
complementary_sets(Names,CNames) :-
    %% This assumes that the rewrites have already been added
    findall(C-L-R-Dir-TI-Name,
	    (rewrite_rule(L,R,C,Dir,TI,_,Name,_),
	     Dir = equ(_,left),
	     member(Name,Names),
	     \+ C == [], true), Cs),		% C may be a var
    Cs \= [],
    %% collect together all those with the same left-hand-side
    collect(Cs,CNames).
complementary_sets(Names,CNames) :-
    %% This assumes that the rewrites have already been added
    findall(C-L-R-Dir-TI-Name,
	    (rewrite_rule(L,R,C,Dir,TI,_,Name,_),
	     Dir = equiv(left),
	     member(Name,Names),
	     \+ C == [], true), Cs),		% C may be a var
    Cs \= [],
    %% collect together all those with the same left-hand-side
    collect(Cs,CNames).

/* complementary_set_dynamic(?C).  C is a complementary set computed
 * for all rewrites present in the database at the time of calling.
 * Typically, this is too strong, and complementary_set should be used
 * instead.  */
complementary_set_dynamic(C) :-
    complementary_sets(CNames),
    member(C,CNames).

/* complementary_set(+Names,?C).  C is a complementary set computed
 * over rewrites derived from Names.  */
complementary_set(Names,C) :-
    complementary_sets(Names,CNames),
    member(C,CNames).

/* complementary_set(?C).  C is a complementary set which was computed
 * for a given set of rewrites at loading time.  */
complementary_set(C) :-
    recorded(comp_set,comp_set(_TheoremNames,C),_).

/* collect(+Cs,?CNames).  Collects together the rewrites in Cs into a
 * complementary form, each having the same LHS and a different RHS.
 * Note that we require that there be n>1 complementary rewrites for a
 * given LHS and so singletons (i.e., simple conditional rules) are
 * discarded.  */
collect([], []).
collect([C-L-R-Dir-TI-Name | Rest], [[C-R-Dir-TI-Name|[One|Cs]]-L|RestCLs]) :-
    %% Pick an L, and look in Rest for those with similar Ls and
    %% different Rs.  We insist on [One|Cs] to ensure n>1.
    collect_cs(L-R,Rest,[One|Cs],NewRest),!,
    collect(NewRest, RestCLs).
collect([_C-_L-_R-_Dir-_TI-_Name | Rest], RestCLs) :-
    %% deal with the failure of the clause above in case there is only
    %% a single rewrite in the complementary set
    collect(Rest, RestCLs).

/* collect_cs(+L-R,+Rest,?Cs,?NewRest).  Cs are all rewrites from Rest
 * whose left-hand side is identical (modulo renaming of prolog
 * variables) to L and whose right-hand side is different.  NewRest
 * are those rewrites which do not match.  */
collect_cs(_L-_R,[], [],[]).
collect_cs(L-R,[C-LL-RR-TTII-Dir-Name | Rest], [C-RR-TTII-Dir-Name|Cs], NewRest) :-
    %% following rubbish is "modulo variable renaming".
    \+ \+ (make_ground(L), L=LL),
    \+ \+ (make_ground(LL),L=LL),

    %% unify to keep all variables consistent throughout the
    %% complementary set
    unify(L,LL), 
    %% we can check for different Rs with == since we know that L==>R
    %% is a rewrite and hence the variables instantiated by unify are
    %% all those appearing in R
    \+ R==RR, !,				
    collect_cs(L-R,Rest, Cs, NewRest).
collect_cs(L-R,[Missed | Rest], Cs, [Missed|NewRest]) :-
    collect_cs(L-R,Rest, Cs, NewRest).

/* Casesplit analysis stuff.  This is used to compute casesplit and
   induction suggestions.  There is a great deal of similarity between
   these two; much of the code was originally written with induction
   in mind, so comments and variables names will mention `induction'.
   However, bear in mind that much of the code is use for casesplit
   analysis as well.  There are some differences, but these are
   controlled from the top-level by flags: induction or casesplit,
   ripple or reduction.  The induction flag introduces annotations
   (wave-fronts and sinks), and uses rippling for look-anhead. The
   alternative flag, casesplit, does not introduce any annotations and
   used reduction for look-ahead.  */


induction_suggestion(H,G,Scheme) :-
    /* ... use induction analysis and rippling. */
    scheme_suggestion(H,G,induction,ripple,AllInductionInfo),
    selection_heuristic(AllInductionInfo, Scheme,_).
unflawed_induction_suggestion(H,G,Scheme) :-
    /* as above, but insist upon 0 flawed occurrences */
    scheme_suggestion(H,G,induction,ripple,AllInductionInfo),
    selection_heuristic(AllInductionInfo, Scheme,0-_-_).
casesplit_suggestion(H,G,Scheme) :-
    /* ... use casesplit analysis and reduction. */
    scheme_suggestion(H,G,casesplit,reduction,AllInductionInfo),
    selection_heuristic(AllInductionInfo, Scheme,_).
flawed_casesplit_suggestion(H,G,Scheme) :-
    /* ... use casesplit analysis and reduction. */
    scheme_suggestion(H,G,casesplit,reduction,AllInductionInfo),
    selection_heuristic(AllInductionInfo, Scheme,_-_-M),
    M > 0.
unflawed_casesplit_suggestion(H,G,Scheme) :-
    /* ditto */
    scheme_suggestion(H,G,casesplit,reduction,AllInductionInfo),
    selection_heuristic(AllInductionInfo, Scheme,0-_-_).    

scheme_suggestion(H,Goal,IoC,RipOrRed,AllInductionInfo) :-
    /* Suggest a scheme with score Score using rewriting look-ahead.
       Schemes may be for casesplits on datatypes or inductions.  This
       is done in two phases: the first phase builds the
       flawed/unflawed table in AllInductionInfo */

    (IoC=induction -> G=Goal; unannotated(Goal,G)),
    matrix(PossibleSinks,MatrixWithSinks,G),

    /* It is possible that G (and so Matrix) contain sink annotations
       (in a nested induction).  We must remove these: those relevant
       to rippling analysis will be inserted at the correct time.
       Casesplits do not introduce sinks.  Note that any wave
       annotation in G is not removed during induction, since these
       may be needed to motivate an induction; however, it is
       meaningless to try an induction on a variable which appears
       below exisiting annotation, since moving the resulting
       differences would (in general) corrupt the skeleton of the
       previous annotation.  So we do not attempt an induction on
       variables which are already inside some annotation.  In some
       situations this may be too restrictive (for example in
       transitivity proofs, eg lesstrans1) and it may be necessary to
       remove annotations from the induction goal.  At the moment,
       this is left to the preconditions of the calling method.  When
       doing casesplit analysis, the annotation is perhaps
       meaningless, so it is removed.  */

    sinks(Matrix,_,MatrixWithSinks),
    findset(Var:T, (universal_var(H==>G,Var:T),
		    \+ inside_wave_front(Var,Matrix)),
	    Vars_Types),
    findall((V:T)-Positions,
	    (member(V:T,Vars_Types),
	     findall(Pos, exp_at(Matrix,Pos,V), Positions)),
	    Vars_Types_Positions),

    /* map_list_history allows us to try each universal variable at
       each occurring position, but to (i) ignore variables which
       don't suggest schemes, and (ii) to avoid computing the scheme
       information for a given variable/scheme-term/hole-position-list
       more than once.  This history of previously computed scheme
       information is passed into the rewrite_path goal as the
       argument IgnoreFlat; For the outer map_list_history_filter the
       initial history is the empty list; for the inner, it is the
       history of the outer one, X0.  This is ugly but separating out
       the generation and then removal of duplicates is too expensive
       (it is the generation which is expensive, not the removal).  */

    retractall(rewrite_path_memo(_)), assert(rewrite_path_memo([])),
    retractall(syntax_path_memo(_)),
    replace_universal_vars(MLVars,Vars_Types,Matrix,LiftedMatrix),
    map_list_filter(
	Vars_Types_Positions,
	((V:T)-Poses) :=> ByPosInductionInfoOtherPosInfoSet, 
	(map_list_filter(Poses, Pos :=> InductionInfoOtherPosInfoSet,
	     setof(InductionInfo-OtherPosInfo,
		   %% MLVars needs to be existentially quantified,
		   %% since they appear free in LiftedMatrix and are
		   %% instantiated by rewrite_path/_
		   MLVars^rewrite_path(IoC-RipOrRed,
				       H-Matrix,Pos,Vars_Types,
				       Vars_Types_Positions,
				       InductionInfo-OtherPosInfo,
				       PossibleSinks,Matrix,LiftedMatrix,V,MLVars),
		   InductionInfoOtherPosInfoSet),
	     ByPosInductionInfoOtherPosInfoSet)),
	InductionInfoOtherPosInfoList),
    flatten(InductionInfoOtherPosInfoList,IrrRedAllInductionInfo),

    %% IrrRedAllInductionInfo may be reducible in the sense that two
    %% scheme suggestions may be identical modulo (a permutation
    %% of) sinks.  It also removes duplicate suggestions.
    irredundant(IrrRedAllInductionInfo,AllInductionInfo).

    %% AllInductionInfo is a list of elements having the form
    %% [(V:T)-HolePosList-IT|Rest]-PosInfo (ie pair), where the first
    %% element is a list of the form shown, describing an
    %% induction/casesplit on the variable V with the term IT, having,
    %% in the cases of induction, holes at the positions in
    %% HolePosList (HolePosList is meaningless in the case of
    %% casesplits).  There are no repeated elements.  Notice however,
    %% that there may be repeated elements modulo differences in hole
    %% positions.  For example, a term f(x) with a rule f(s(s(x))) =
    %% ... will suggest two inductions, since the wave-front may be
    %% either s(s(.)) or s(.).

    %% PosInfo describes how occurrences of V fair under this
    %% suggestion: it is a list of the form P-Tag-Sinks where P is a
    %% position of V in Matrix, Tag is either "unflawed" or "flawed"
    %% and Sinks is a list of variables which must be sinks in the
    %% case of Tag == unflawed (see below) (Sinks is meaningless in
    %% the case of casesplits).  For a given suggestion, at least one
    %% of the occurrences will be unflawed (see comment at the end of
    %% rewrite_path/6)

    %% Sinks describes those variables which must be sinks for this
    %% induction suggestion to be sensible---it is meaningless for
    %% casesplit analysis.  Note that in order to suggest an induction
    %% term for V, it may be necessary to simultaneously suggest an
    %% induction term for some other variable at some other position:
    %% these are also recorded in AllInductionInfo.  For example given
    %% cnc_s, and the Matrix x=y in pnat, AllInductionInfo is
    %% [[(x:pnat)-[[1]]-s(v1),(y:pnat)-[[1]]-s(v0)]-[[1,1]-unflawed-[]]]
    %% and for assp it is
    %% [[(x:pnat)-[[1]]-s(v0)]-[[1,1,2,1]-unflawed-[],[1,1,1]-unflawed-[]],
    %% [(y:pnat)-[[1]]-s(v0)]-[[1,2,1,1]-unflawed-[],[2,1,2,1]-flawed-_15878]]

		    
/* InductionTerm is the term which is required at position Pos in
 * order that a rewrite at that position may take place --- the type
 * of rewriting (reduction or rippling) is determined by the flag
 * RipOrRed.  Furthermore, this rewrite may require that sinks be
 * present (either for sideways ripples or for non-skeleton-preserving
 * ripples).  Sinks are chosen from the variables provided in the
 * OLVars; sinks actually required are Sinks, but it is always the
 * case that Sinks and the induction variables chosen (and made
 * explicit in InductionInfo) will be disjoint.  OLVars is the list of
 * object variables which we are at liberty to do induction on.
 * PossibleSinks is a set of all V:T which are in the prefix of the
 * current goal -- Sinks will be a subset of this.  Pos is the
 * position in Matrix to consider.  ?Ignore is list of
 * InductionChoices which are to be ignored.  Hyps is in case of
 * future expansion.  */

:- dynamic rewrite_path_memo/1.  rewrite_path_memo([]).
:- dynamic syntax_path_memo/1.  

rewrite_path(IoC-RipOrRed,Hyps,Pos,OLVars,Vars_Types_Positions,
	     InductionChoice-OtherInfo,
	     PossibleSinks, Term,LiftedTerm,OLVar,MLVars) :-
%    append([_],PostPos,Pos),			% EXPERIMENTAL: small context
    append([_|_],PostPos,Pos),			% EXPERIMENTAL: small context
    exp_at(LiftedTerm,PostPos,Subterm),		% choose a subterm to ripple
    /* only-non-var terms are meaningful since only these can be instantiated */
    \+ground(Subterm),				
    erase(Subterm,TryTermErase),
    /* Try to narrow this non-ground term into a redex */
    \+ syntax_path_memo((OLVar,PostPos,PossibleSinks)),
    assert(syntax_path_memo((OLVar,TryTermErase,PossibleSinks))),
%    write((OLVar,TryTermErase,PossibleSinks)),nl,
    rewrite_redex(TryTermErase),
    %% rewrite_rule has instantiated the variables in Subterm with
    %% possible induction terms.  For these to be sensible, we need
    %% to check that there is an injection from each of the variables
    %% in OLVars into MLVars
    injection_map(RipOrRed,OLVars,MLVars,InductionInfo),
    if(RipOrRed=ripple,				% need some hole positions
       member((OLVar:_Type)-[_|_]-_TERM, InductionInfo)),
    copy_term(InductionInfo,IIC),
    no_hole_positions(IIC,Memo),
    rewrite_path_memo(Ignore),
    \+ subsumedby(PossibleSinks-Memo,Ignore),
    retractall(rewrite_path_memo(_)),
    assert(rewrite_path_memo([PossibleSinks-Memo|Ignore])),
    %% InductionInfo is a list having the form V:T-HolePositions-IT,
    %% meaning that V is replaced with IT in Subterm a rewrite rule
    %% can be applied; furthermore, IT can be seen as a wave-term by
    %% considering its hole(s) to be marked by one of the positions in
    %% HolePositions.  All elements of InductionInfo for which
    %% HolePositions is [] are variables on which we are not doing an
    %% induction, so we are free to use these ones for sinks (see
    %% below).  In the case of a casesplit, the HolePositions slot
    %% will be uninstantiated.
%    write('trying...'),nl,
%    write(InductionInfo),nl,
    %% We use a copy of the Hyps because we do not want to ground
    %% prolog variables there, only those in InductionInfo.  However,
    %% we want to ground InductionInfo in such a way that Prolog
    %% variables only get grounded to object-level variables which do
    %% not appear in Hyps.  This is a mess, but it is the easiest way
    %% to ensure that the object-variables we use here will be
    %% accecptable by scheme/5.  A more elegant solution is to keep a
    %% copy of InductionInfo before grounding it, and pass that to
    %% scheme/5.
    copy_term(Hyps,HypsVars),
    make_ground(HypsVars-InductionInfo),	
    %% Rather than record sink obligations, try all the variables
    %% which are possible sinks and try all 2^n combinations.  (Only
    %% in case of induction.)  Use of [_|_] in the two map_lists below
    %% is to exclude variables that have induction terms from being
    %% considered as sinks, since they are the ones we are inducing
    %% upon.

    if(IoC = induction,
       map_list_filter(PossibleSinks,(V:_) :=> V,
		       \+ member((V:_)-[_|_]-_,InductionInfo),PossibleSinksUsed)),
    map_list_filter(Vars_Types_Positions,
		    ((V:_)-VPoses) :=> VPoses,
		    member((V:_)-[_|_]-_, InductionInfo),
		    AllPositionsNF),
    flatten_one_level(AllPositionsNF,AllPositions),

%    print('********************'),nl,
    (((IoC = induction ->
       (replace_all_IVs(InductionInfo,InductionChoice,Term,SubtermAnnNormal),
	(well_annotated(SubtermAnnNormal) -> true;
	 clam_internal_error('Ill-formed term in scheme analysis.')));
       red_replace_all_IVs(InductionInfo,InductionChoice,
			   LiftedTerm,SubtermAnnNormal)))),
%    print(SubtermAnnNormal),nl,
    %% InductionChoice is a list of the form V:T-HolePosList-IT.  For
    %% casesplit analysis, try to reduce one of these terms.  For
    %% induction, attempt to ripple this term; there may be the option
    %% of making some of the variables into sinks, in which case all
    %% combinations of these variables (not occurrences).  Sadly we
    %% are not able (currently) to choose maximal use of sinks since
    %% the induction preconditions need to know which universals are
    %% _necessary_ (and not possible, as the former implies the
    %% latter) for rippling to proceed.  Ideally, sink obligations
    %% would be returned from ripple/6 but this is not how things are
    %% done at the moment.  Variables in PossibleSinks which are not
    %% being induced upon may be used as sinks.  InductionChoice shows
    %% which variables are being induced upon (those not being induced
    %% upon are dropped by replace_all_IVs).

    %% Generate a flag of ok/not_ok for each superterm of each of the
    %% variables being induced upon in InductionChoice (there will be
    %% more than one in the case of a simultaneous suggestion)

    % check_time_limit,
    flawed_unflawed_table(AllPositions, OtherInfo, 
			  SubtermAnnNormal, Hyps, PossibleSinksUsed,
			  RipOrRed).

/*  I was experimenting with a different algorithm:
    flawed_unflawed_table_TD(SubtermAnnNormal,[],AllPositions,OtherInfo2,Hyps,
			     PossibleSinksUsed),  */
    %% It is possible for a suggestion to be everywhere flawed since
    %% there are usually different ways of annotating a given
    %% induction term, and not all of these can be rippled.  It is
    %% easy to filter out such unwanted suggestions here.   Perhaps
    %% all induction terms should be strongly annotated (eg
    %% ``{h}::{t}'' for list induction) and rely on weakening at a
    %% later stage?
%    memberchk(_Ps-unflawed-_Sinks,OtherInfo).	% check at least one is unflawed



/* If SubtermAnnNormal can be rewritten at position Ps or at any
   prefix of Ps, then Flag is unflawed, else it is flawed.  This may
   depend on Sinks, which are selected from PossibleSinksUsed.  For
   all the positions of the variables being induced upon, decide
   whether or not they appear in some superterm that can be rewritten.
   Since the occurrences are distinct, some superterms will also be
   distinct, and some will not.  For non-distinct superterms, avoid
   recomputation by looking in the history.

   The term can be searched top-down or bottom-up; here we search
   bottom-up, starting with the induction variables.  In this way we
   are able to reduce the number of sinks needed for an occurrence to
   be unflawed.  */
flawed_unflawed_table(A,B,C,D,E,F) :-
    flawed_unflawed_table(A,B,[],C,D,E,F).
flawed_unflawed_table([], [], _, _,_,_,_).
flawed_unflawed_table([P|Ps], [P-Flag-Sinks|OtherInfo], 
		      History,
		      SubtermAnnNormal, Hyps, PossibleSinksUsed,Test) :-
%    write(clause2),nl,
    /* MEMO CASE, POSITIVE and NEGATIVE */
    /* If we have already examined position P (or perhaps one of its
    superterms) we can simply read the result from the table. */
    member(P-Flag-Sinks, History),!,
    flawed_unflawed_table(Ps, OtherInfo, History,
			  SubtermAnnNormal, Hyps, PossibleSinksUsed,Test).
flawed_unflawed_table([P|Ps], [P-unflawed-Sinks|OtherInfo], % RIPPLE
		      History,
		      SubtermAnnNormal, Hyps, PossibleSinksUsed,ripple) :-
%    write(clause3),nl,

    /* P is not mentioned in the memo table, so check position P and
       its superterms if necessary */
    ann_exp_at(SubtermAnnNormal, P, RippleTerm),
%    write_term(RippleTerm,[quoted(true)]),nl,
%    on_backtracking((write(asar-done),nl)),
    add_sinks_and_ripple(Hyps,SubtermAnnNormal, P, 
			 RippleTerm,PossibleSinksUsed,Sinks),!,
%    write(asar-done),nl,
    flawed_unflawed_table(Ps, OtherInfo, 
			  [P-unflawed-Sinks|History], SubtermAnnNormal,
			  Hyps, PossibleSinksUsed,ripple).
flawed_unflawed_table([P|Ps], [P-unflawed-[]|OtherInfo], % REDUCTION
		      History,
		      Subterm, Hyps, PossibleSinksUsed,reduction) :-
%    write(clause4),nl,
    /* P is not mentioned in the memo table, so check position P and
       its superterms if necessary.  NOTICE: Sinks=[]  */
    exp_at(Subterm, P, Term), 
    /* This is the condition
   Totally unflawed induction.
   Else, try any case split such that it has at least one unflawed occurrence
      (with respect to reduction rules) *and* there is an occurrence of one
      of the base constructors of the type over which the split is being
      performed. Maybe occurrences of any constructor of the type should
      count? We might also refine the conditions to only allow constructor
      occurrences "close to" the unflawed occurrence, e.g. the variable and
      the constructor occur within the two arguments of a binary relation.
   Else, try any other induction.*/
    oyster_type(_,Steps,Bases),
    ((member(Base,Bases), exp_at(Term,[_],Base)) orelse
     (member(Step,Steps), Step =.. [FS|_], exp_at(Term,[0,_],FS))),
    reduction_redex(Term),
    !,
    flawed_unflawed_table(Ps, OtherInfo, 
			  [P-unflawed-[]|History], Subterm,
			  Hyps, PossibleSinksUsed,reduction).
flawed_unflawed_table([P|Ps], [P-Flag-Sinks|OtherInfo], 
		      History,
		      SubtermAnnNormal, Hyps, PossibleSinksUsed,Test) :-
%    write(clause5),nl,
    /* P is flawed (by the clause above), so check its superterms for
       flawedness;  if P is the root of the term, it has no superterms
       so the node is flawed.  */
    ((true,		% EXPERIMENTAL: do not consider superterms
      append([_],Psuper,P)) ->
     (flawed_unflawed_table([Psuper], [Psuperlim-Flag-Sinks], History,
			   SubtermAnnNormal, Hyps, PossibleSinksUsed,Test),
      NewHistory = [Psuperlim-Flag-Sinks|History])
	 ; (Flag = flawed, NewHistory = History)),
    flawed_unflawed_table(Ps, OtherInfo, NewHistory, SubtermAnnNormal,
			  Hyps, PossibleSinksUsed,Test).


/* TOP-DOWN version.  This is probably faster than the bottom-up
   version, but is also less accurrate in that it will not necessarily
   find the smallest sink set for an occurrence to be unflawed.
   However, it has the advantage that top-down is the strategy used in
   step-case to reduce redexes.  */
/* If Term is a variable, it cannot be rippled.  */
flawed_unflawed_table_TD(_Term,P,VarPos,[P-flawed-_],_Hyps,_PossibleSinksUsed) :-
    member(P,VarPos),!.  
flawed_unflawed_table_TD(Term,P,VarPos,Info,Hyps,PossibleSinksUsed) :-
    add_sinks_and_rewrite(ripple,Hyps,Term,PossibleSinksUsed,Sinks),!,
    /* if Term at position P can be rippled all Q's beneath P
       appearing in VarPos are unflawed. Notice that Sinks may not be
       minimal for those subterms! */
    map_list_filter(VarPos, Q:=>(Q-unflawed-Sinks),
		    append(_,P,Q),Info).

/* P is a flawed position, and can be decomposed. */
flawed_unflawed_table_TD(Term,P,VarPos,Info,Hyps,PossibleSinksUsed) :-
    skeleton_arguments(Term,Args),!,
    flawed_unflawed_table_TD_map(Args,P,1,VarPos,Info,Hyps,PossibleSinksUsed).

flawed_unflawed_table_TD(_Term,P,_VarPos,[P-flawed-_],_Hyps,_PossibleSinksUsed).

flawed_unflawed_table_TD_map([],_,_,_VarPos,[],_Hyps,_PossibleSinksUsed).
flawed_unflawed_table_TD_map([A|As],P,N,VarPos,Info,Hyps,PossibleSinksUsed) :-
    /* there is no point in trying [N|P] if it is not on a path to one
    of the VarPos */
    (once((member(VP,VarPos), append(_, [N|P], VP))) ->
     flawed_unflawed_table_TD(A,[N|P],VarPos,I,Hyps,PossibleSinksUsed); 
     (I = [])),
    NN is N + 1,
    flawed_unflawed_table_TD_map(As,P,NN,VarPos,II,Hyps,PossibleSinksUsed),
    append(I,II,Info).
    
add_sinks_and_ripple(_Hyps,Goal,GoalPos,SubtermAnnNormal,
		     PossibleSinksUsed,Sinks) :-
    /* test first that the erasure can be matched! */
    erase(SubtermAnnNormal,Erasure),
    once(rewrite_redex(Erasure)),
    /* PossibleSinksUsed are those variables which are essentially
       universally quantified inside SubtermAnnNormal.  However, not
       all those variables may be present in that term, so we
       calculate all those which are present before making
       sinks---this is to prevent useless backtracking.  */
    freevarsinterm(Erasure,SinkVars),
    intersection(PossibleSinksUsed,SinkVars,SinksToTry),
    power_set(SinksToTry,SinkSet),		% order them
    order_card(SinkSet,OrderedSinkSet),
    /* Determine the sinks appearing inside the term to be rippled. */
    member(Sinks,OrderedSinkSet),	%pick in order of increasing cardinality
    mark_sinks(Sinks,SubtermAnnNormal,SubtermAnnNormalSinks),
    /* dont try rippling in if there are no sinks present */
    (SubtermAnnNormal = SubtermAnnNormalSinks ->
     D = direction_out;
     D = direction_in_or_out),
    ripple_with_meta_ripple(D, SubtermAnnNormalSinks,_DummyRHS,
			    _Condition,_,Dir,_),
    /* I originally thought that polarity information could be
    abstracted from the flawed/unflawed test but in practice it was
    needed sufficiently often to prevent silly inductions. */
    polarity_compatible(Goal,GoalPos, Dir),
    !.						% cut out use of other sinks

/* B and A are the same sets, B's elements are in order of increasing
 * cardinality.  */
order_card(A,B) :-
    map_list(A,E:=>Key-E, length(E,Key), Akeyed),
    keysort(Akeyed,Bkeyed),
    %% now strip off the keys
    map_list(Bkeyed,Key-E:=>E, true, B).

/*  T and TNN have the same skeleton set and erasure, TNN is in normal form */
ann_normal_form(T,T) :-
    (atomic(T);var(T)),!.
ann_normal_form(WF,WF2) :-
    wfparts(WF,F,Args,Dir,T),!,
    /* WF is as WF2, but each Arg must have a hole around it in the
    case that it contains more annotation.  

    ``F(A1,A2)'' -> ``F(A1*,A2*)'' where 

	Ai* = {Ai'} if Ai contains annotation
            = Ai'   otherwise
     where Ai' is in the relation ann_normal_form to Ai.  */
    
    ann_normal_form_holes(Args,NewArgs,Dir,T),
    wfparts(WF2,F,NewArgs,Dir,T).
ann_normal_form(T,S) :-
    T =.. [F|As],
    map_list(As,A :=> B,ann_normal_form(A,B),Bs),
    S =.. [F|Bs].

ann_normal_form_holes([],[],_Dir,_T).

ann_normal_form_holes([A|Args],[NA|NewArgs],Dir,T) :-
    iswh2(A,AC),!,
    ann_normal_form(AC,ACN),
    iswh(NA,ACN), 
    ann_normal_form_holes(Args,NewArgs,Dir,T).
ann_normal_form_holes([A|Args],[NA|NewArgs],Dir,T) :-
    /* A is not a hole but is annotated.  Since the top-level term is
    assumed to be well-formed and A is inside a wave-front, annotation
    in A must be well-formed in the context of a wave-front.  The
    property is invariant to the transformation A -> wh(wf(A)).  */
    annotated(A),!,
    iswf(WF,Dir,T,A),
    iswh(WH,WF),
    ann_normal_form_holes([WH|Args],[NA|NewArgs],Dir,T).
ann_normal_form_holes([A|Args],[A|NewArgs],Dir,T) :-
    /* A is not annotated to skip it and recurse */
    ann_normal_form_holes(Args,NewArgs,Dir,T).    

make_all_holes([],InductionTerm,InductionTerm).
make_all_holes([Pos|Rest],InductionTerm,InductionTermInstantiated) :-
    gensym('iv',IndPar),
    replace(Pos,IndPar,InductionTerm,ITPI),
    make_all_holes(Rest,ITPI,InductionTermInstantiated).

/* For all the non-empty induction terms, choose a possible hole
 * position set (and allow backtracking over all combinations, except
 * the empty one).  A hole is any proper subterm of the induction term
 * (since we are doing structural induction).  It is not sufficient to
 * consider only leaves of the induction term as candidate holes since
 * the induction hypotheis may well contain structure not present in
 * the goal.  For example, given G(ordered(x)) we might consider
 * G(ordered(h::t)) |- G(ordered(``a::{h::t}'')) as the induction,
 * with h::t a non-leaf hole of the induction term a::h::t.  */
injection_map(RipOrRed,B,A,C) :-
    %% collect the positions of atoms in the induction terms
    map_list(A, IT:=>(IT-APs),
	     findall(AP,(exp_at(IT,AP,Atom),\+ [0|_]=AP,atomic(Atom)),APs),
	     Ap),
    injection_map(RipOrRed,B,Ap,C,X),
    \+ var(X).
injection_map(_RipOrRed,[],[],[],_PossiblyTrivial).
injection_map(RipOrRed,[OLVar:Type|OLVars],
	      [OLVar-_|ITs],[(OLVar:Type)-[]-OLVar|HolePositionsList],
	      PossiblyTrivial) :-
    %% this case when IT is a variable (ie identity induction term)
    !,injection_map(RipOrRed,OLVars,ITs,HolePositionsList,PossiblyTrivial).
injection_map(ripple,[OLVar|OLVars],
	      [IT-APs|ITs],[OLVar-HolePositions-IT|HolePositionsList],
	      non_trivial) :-
    %% Simple check to ensure that IT has not been instantiated to a
    %% constant term.  It is also necessary to ensure that all the
    %% variable positions in IT are still variables.  Consider the
    %% following example which illustrates this need.  Term plus(a,b)
    %% is the term we will try to ripple.  With the rule
    %% plus(times(X,Y),Y) :=> times(s(X),Y) we have the induction
    %% suggestion A = times(v0,b); it is the presence of b (an atomic)
    %% inside the induction term which is incorrect.  In fact, since
    %% the induction term must end up as times(v0,v1) (v0 and v1 are
    %% new parameters) it is clear that (i) some check is needed here
    %% and that (ii) this induction suggestion is flawed because the
    %% wave-rule will not match plus(times(v0,v1),b) in any case.  So
    %% we reject this case.  APs is a list of positions in the
    %% top-level induction term which are atomic:  these positions are
    %% allowed to be atomic.
    \+ground(IT),				%ground
    findall(HolePos, (exp_at(IT,HolePos,MLVar),
	     (var(MLVar);compound(MLVar)),
	     \+ HolePos = []),			%filter out identity terms too
	    HolePositions),
    injection_map(ripple,OLVars,ITs,HolePositionsList,_),
    %% the following check has to be done at the end, since some
    %% variables in IT may not yet be grounded (by second clause)
    \+ (exp_at(IT,BP,VarCheck),
	\+ BP=[0|_],
	\+ member(BP,APs),
	atomic(VarCheck)).			%there are no atoms in
						%here (excepting functors)

injection_map(reduction,[OLVar|OLVars],
	      [IT-APs|ITs],[OLVar-HolePositions-IT|HolePositionsList],
	      non_trivial) :-

    %% Here only check that all the variable positions in IT are still
    %% variables.  (cf ripple case above)

    findall(HolePos, (exp_at(IT,HolePos,MLVar),
	     (var(MLVar);compound(MLVar)),
	     \+ HolePos = []),			%filter out identity terms too
	    HolePositions),
    injection_map(reduction,OLVars,ITs,HolePositionsList,_),
    %% The following check has to be done at the end, since some
    %% variables in IT may not yet be grounded (by second clause)
    \+ (exp_at(IT,BP,VarCheck),
	\+ BP=[0|_],
	\+ member(BP,APs),
	atomic(VarCheck)).			%there are no atoms in
						%here (excepting functors)
/* Insert the annotations described in InductionInfo (first argument)
 * into Term, to result in TermAnn.  RestChoice is the particular
 * assignment of holes which is selected from those possible in
 * InductionInfo.  NB strongest annotations are picked first, but this
 * is by good fortune rather than anything else, weakenings are picked
 * on backtracking (it may be preferable to make weakening explicit).
 * Also, the RestChoice does not record variables on which no
 * induction takes place.  */

replace_all_IVs([],[],T,T).			% no more substitutions
/* This clause drops variables which are not being induced upon */
replace_all_IVs([(_V:_T)-[]-_|Rest],RestChoice,Term,TermAnn) :-
    !,replace_all_IVs(Rest,RestChoice,Term,TermAnn).
replace_all_IVs([(V:T)-HolePosList-IT|Rest],
		    [(V:T)-HoleList-IT   |RestChoice],Term,TermAnn) :-
    power_set(HolePosList,SPHolePosList),
    /* sorting them allows taking deepest holes first */
    sort(SPHolePosList,SSPHolePosList),
    reverse(SSPHolePosList,PHolePosList),
    member(HoleList,PHolePosList),
    \+ HoleList = [],
    %% ensure that the positions in HoleList are not prefixes of each
    %% other (since we do not want annotatons such as
    %% ``{h1}::{{h2}::{t}}'').  Since we check all elements of the
    %% list, there is no need to check the "vice-versa" case.
    \+ (select(H,HoleList,RestHoleList),
	member(Hother,RestHoleList),
	append(_DeeperOffest,H,Hother)),!,
    wave_fronts(IT,[[]-HoleList/[hard,out]],AnnITA),
    ann_normal_form(AnnITA,AnnIT),		%put in normal form
    replace_all(V,AnnIT,Term,TermNew),		%replace the V with AnnIT
    replace_all_IVs(Rest,RestChoice,TermNew,TermAnn).

/* Similar case for reduction */
red_replace_all_IVs([],[],T,T).
/* This clause drops variables which are not being induced upon */
red_replace_all_IVs([(_V:_T)-[]-_|Rest],RestChoice,Term,TermAnn) :-
    red_replace_all_IVs(Rest,RestChoice,Term,TermAnn).
red_replace_all_IVs([(V:T)-[_|_]-IT|Rest],
		    [(V:T)-_-IT   |RestChoice],Term1,Term2) :-
    /* HolePosList is left uninstantiated */
    red_replace_all_IVs(Rest,RestChoice,Term1,Term2).

/* Abstract hole positions into variables */
most_general_choice([],[],[]).
most_general_choice([VT-HP-IT| Rest], [VT-X-IT | RR],[X-HP|XRHP]) :-
    most_general_choice(Rest, RR,XRHP).

/* look to see if IC appears inside Others, ignoring the positions of
    holes inside Others.  That is, membship test modulo the
    HolePositions part of induction information. */
subsumedby(_PossibleSinks1-IC,Others) :-
    member(_PossibleSinks2-OtherIC,Others),
    equal_modulo_meta_variable_renaming2(IC,OtherIC).

map_list_wfs([IT|ITs],[HolePosList|HolePosListList],[AnnIT|AnnITs]) :-
    \+ HolePosList = [],!,	%we only want non-trivial inductions
    power_set(HolePosList,PHolePosList),
    member(HoleList,PHolePosList),
    \+ HoleList = [],
    wave_fronts(IT,[[]-HoleList/[hard,out]],AnnIT),
    map_list_wfs(ITs,HolePosListList,AnnITs).
map_list_wfs([_|_ITs],[_|_HolePosListList],[_AnnIT|_AnnITs]) :-
map_list_wfs([],[],[]).
	     

/*
 * enumerates the power set of Set in order of decreasing cardinality
 * of SetPSOrdered
 */
order_ps(Set,E) :-
    power_set(Set,PS),
    order_card(PS,SetPSOrdered),
    rmember(E,SetPSOrdered),
    \+E=[].

/* A and B are the same, except that there are no duplicate entries in
   B.  Entries are duplicates iff they have the same variables, IT and
   sinks.  */
irredundant(A,B) :- 
    irredundant_aux(A,[],B).
irredundant_aux([],_,[]).
irredundant_aux([H|T],[], [H|Red]) :-
    !,irredundant_aux(T,[H],Red).
irredundant_aux([VarStuff-OtherPosInfo|T],Seen,Red) :-		% H is redundant
    member(VarStuff-OPI, Seen),
    equal_mod_positions_and_sinks(OPI,OtherPosInfo),
    !, irredundant_aux(T,[VarStuff-OtherPosInfo|Seen],Red).
irredundant_aux([H|T],Seen,[H|Red]) :-		% H is irredundant
    irredundant_aux(T,[H|Seen],Red).

%%% arguments are of the form Pos-Tag-Sinks
equal_mod_positions_and_sinks([],_).
equal_mod_positions_and_sinks([Pos-flawed-_|OPI],OtherPosInfo) :-
    member(Pos-flawed-_,OtherPosInfo),!,
    equal_mod_positions_and_sinks(OPI,OtherPosInfo).
equal_mod_positions_and_sinks([Pos-unflawed-Sinks|OPI],OtherPosInfo) :-
    member(Pos-unflawed-OtherSinks,OtherPosInfo),!,
    if(\+ground(Sinks-OtherSinks),
       clam_internal_error(
	   'equal_mod_positions_and_sinks: unflawed sinks must be a ground set!')),
    subset(Sinks,OtherSinks),
    equal_mod_positions_and_sinks(OPI,OtherPosInfo).


		   /* HEURISTIC-SPECIFIC STUFF.  */

/* Try to find single unflawed scheme (can be for induction or
 * casesplits) such a scheme is one in which all variable occurrences
 * are unflawed, and the contexts are non-overlapping.  Scheme with
 * score Score is chosen from the induction information in II.  Score
 * is a triple of the form NumFlawed-Depth-NumUnflawed.  Since it is
 * likely that the contexts criterion is not important, it is not
 * considered here.  */
selection_heuristic(II,S,Score) :-
    /* we don't exploit the HP information in these heuristics */
    map_list(II, (A-B) :=> (AA-B),
	     map_list(A, (VT-_HP-IT) :=> (VT-IT), true, AA),
	     III),
    selection_heuristic_(III,S,Score).

selection_heuristic_(AllInductionInfo,Scheme,SchemeScore) :-
    %% VarsScore is as AllInductionInfo but with a count of
    %% unflawed/flawed, and without detailled positional info.
    map_list(AllInductionInfo,
	     IND-Poses :=> Score-IND,
	     heuristic_score(Poses, Score),
	     VarsScore),
    %% choosing from these is simply a matter of ordering VarsScore
    %% according to NumUnflawed/NumFlawed-Depths
    keysort(VarsScore,P),
    member(SchemeScore-Scheme,P).

/* Evaluate the induction described by Poses; NumUnflawed is the
 * number of unflawed occurrences of Variable, and NumFlawed is the
 * number of flawed occurrences.  */
heuristic_score(Poses,NumFlawed-Depth-NumUnflawed) :-
    count_member(Poses,_-unflawed-_,NumUnflawed),
    count_member(Poses,_-flawed-_,NumFlawed),
    %% in the case of a draw on the number of flawed occurrences, we
    %% want to know just how deep in the term these flaws are (see
    %% bbnote 1018) so that we can score them.  I don't know how to
    %% compare the depths of multiple, flawed occurrences so instead I
    %% crudely add them all up, and that is the single integer Depth.
    %% Hopefully that will do.
    map_list(Poses, Pos-Flag-_ :=> Depth,
             (Flag = flawed -> length(Pos,Depth)
               ; Depth = 0) ,DepthList),
    sum_of_list(DepthList,Depth).


        % instantiation(T1,T2) tests if T2 is an instantiation of T1.
        % alpha_variant(T1,T2) tests if T1 and T2 are alphabetic variants.
        % 
        % See that great masterwork, my thesis, page 92 for formal
        % definitions and page 100 for implementation.
instantiation(T1,T2) :- \+ \+ (make_ground(T1),T1=T2).
alpha_variant(T1,T2) :- instantiation(T1,T2), instantiation(T2,T1).


/* assume erasure of Qp is Q. */
updated_sinks(Decls,Qp,Q,NewQ) :-
    /* find all sink positions in the matrix */
    findall(P,(ann_exp_at(Q,P,V),member(V:_,Decls)),SinkPoses),

    /* find the corresponding positions in the annotated term */
    findall(Pos-T,(ann_exp_at(Qp,Pos,T),
		   skeleton_position(Pos,Qp,SkelPos),
		   member(SkelPos,SinkPoses)),PosTs),
    updated_sinks(PosTs,Qp,NewQ).

updated_sinks([],Q,Q).
updated_sinks([P-T|PosT],Qp,NewQ) :-
    issink(T,Tcont),!,
    replace(P,Tcont,Qp,Q2),
    updated_sinks(PosT,Q2,NewQ).

updated_sinks([_P-_T|PosT],Qp,NewQ) :-
    /* There is no sink marker, so just skip this position */
    updated_sinks(PosT,Qp,NewQ).

/* FI is an variable-free instance of formula F, which is
   quantifier-free.  Values are chosen arbitrarily. */
term_instance(Context,F1,FI) :-
    erase_sequent(Context==>F1,C==>F),
    matrix(C,F,Goal),			%add in prefix
    check_term_instance(Goal),
    !,
    term_instance(Goal,FI).


/* as term_instance, only w/o backtracking---quickly check that there
   is at least one instance */
check_term_instance(V:T1=>T2) :-
    freevarinterm(T2,V),!,
    instance_of_type(T1,T1i),!,
    s(T2,[T1i],[V],T2i),
    check_term_instance(T2i).
check_term_instance(_V:T1=>T2) :-
	!,check_term_instance(T1),
	check_term_instance(T2).
check_term_instance(_V:_T1=>_T2) :- !,fail.
check_term_instance(_).

term_instance(V:T1=>T2,Inst) :-
    freevarinterm(T2,V),!,
    instance_of_type(T1,T1i),
    s(T2,[T1i],[V],T2i),
    term_instance(T2i,Inst).
/* if V is not free in T2, we have a non-dependant function type (an
   implication), so simply recurse inside the antecedent and consequent.  */
term_instance(_V:T1=>T2,T1i=>T2i) :-
    !,term_instance(T1,T1i),
    term_instance(T2,T2i).
term_instance(_V:_T1=>_T2,_) :- !,fail.
term_instance(F,F).

/* collect upto M different random instances of F in FIs.  There may
be feweer than M different instances (due to behaviour of
random_term_instance), in which case return as many as possible.  */

term_instances(M,C,F,FI) :-
    term_instances(M,C,F,FI,[]).
term_instances(0,_C,_F,[],_).
term_instances(M,C,F,[RF|FIs],Done) :-
    M > 0,
    term_instance(C,F,RF),
    \+ member(RF,Done),				%avoid repetitions
    !,
    MM is M - 1,
    term_instances(MM,C,F,FIs,[RF|Done]).
term_instances(_M,_C,_F,[],_).
    /* no more RFs to generate, so make do */

/* F is a formula in context C which can be readily shown to be false.
   Variable free instances of F are used.  */
trivially_falsifiable(C,F) :-
    retractall(ev_rec(_,_)),			% empty memo table
    term_instances(5,C,F,FIs),
    member(FI,FIs),
    (ev(FI,V) -> true;				%assume canonical
	clam_warning('Couldnt evaluate %t\n',[FI])),
    ((V == void; V == {true}) -> true;
	clam_warning('Non canonical evaluation %t\n',[V])),	
    V = void.
    
no_hole_positions(A,B) :- 
    map_list(A,(VT-_-IT) :=> (VT-IT),B).


/* immediate/[1,2] for discharging things which fall into some
   reasonable class.  */
immediate(H==>G) :-
    immediate(H==>G,_).
immediate(_==>[],[]) :- !.
immediate(H==>[G|Gs],[Tac|Tacs]) :-
    immediate(H==>G,Tac),!,
    immediate(H==>Gs,Tacs).	
immediate(H==>G,Tac) :-
    propositional(H==>G,Tac).

/* D defines a transitive relation */
is_transitive(def(D),_) :-
	transitive_pred(D),!.
is_transitive(def(D),Dom) :-
    A =.. [D,x,y],
    B =.. [D,y,z],
    C =.. [D,x,z],
    Conj = (x:Dom=>y:Dom=>z:Dom=>A=>B=>C),
    /* there may be type-variables in Conj, so ground them first.
    Here we hope that these unquantified type variables will not
    prevent a proof (plan).  */
    make_ground(Conj),				
    quickly_proveable(Conj),
    retractall(transitive_pred(D)),
    assert(transitive_pred(D)).

commutative_function([]).

%
% +JDCR
%
/* D defines a transitive relation */
is_commutative(def(D),_) :-
	commutative_function(D),!.
is_commutative(def(D),Dom=>Dom=>OType) :-
    A =.. [D,x,y],
    B =.. [D,y,x],
    Conj = (x:Dom=>y:Dom=>A=B in OType),
    /* there may be type-variables in Conj, so ground them first.
    Here we hope that these unquantified type variables will not
    prevent a proof (plan).  */
    make_ground(Conj),				
    quickly_proveable(Conj),
    retractall(commutative_pred(D)),
    assert(commutative_pred(D)).

/* attempt to quickly (60s) prove Conj */
quickly_proveable(Conj) :-  
    ex(lpa_dp(Conj,yes),60).
quickly_proveable(Conj) :-
    matrix(Vars,Matrix,Conj),
    \+ trivially_falsifiable(Vars,Matrix),
    ex(dplan([]==>Conj,_Plan,[],0),60).


/* presburger_context(A,B): B are those elements of A which are in
   Presburger arithmetic */
presburger_context([],[]).
presburger_context([_V:T|Ts],[T|Rs]) :-
	presb_formula(T),!,
	presburger_context(Ts,Rs).
presburger_context([_V:_T|Ts],Rs) :-
	presburger_context(Ts,Rs).

larger_size(A,B) :-
    /* term A has more functors in it that term B */
    findall(AP,(exp_at(A,AP,_),\+ AP=[0|_]),APs),
    findall(BP,(exp_at(B,BP,_),\+ BP=[0|_]),BPs),
    length(APs,NA),
    length(BPs,NB),
    NA > NB.

    

/*
 * @(#)$Id: wave_rules.pl,v 1.58 2008/05/21 14:14:14 smaill Exp $
 *
 * $Log: wave_rules.pl,v $
 * Revision 1.58  2008/05/21 14:14:14  smaill
 * update for sicstus4
 *
 * Revision 1.57  1999/01/07 16:33:40  img
 * ripple_and_cancel flag added to ripple code
 *
 * Revision 1.56  1998/11/10 16:02:39  img
 * *** empty log message ***
 *
 * Revision 1.55  1998/11/05 16:45:50  img
 * is_annotated/3 (added): easy-to-use wrapper for abstract term syntax.
 * status_map/5: dont map down the functor of the term--only its
 * arguments.
 *
 * Revision 1.54  1998/09/16 13:47:01  img
 * rewrite_rule/8: special clause for mode in which L is ground, intended
 * to speed-up rule lookup.
 *
 * Revision 1.53  1998/08/26 12:11:35  img
 * rewrite_rule/_: use unification on all arguments.
 * narrowed_rewrite_redex/1 deleted because redundant (use
 * rewrite_redex/1 instead)
 *
 * Revision 1.52  1998/07/27 12:12:44  img
 * Conditional tracing messages
 *
 * Revision 1.51  1998/06/25 10:43:47  img
 * multi_extension: moved to so.pl
 *
 * Revision 1.50  1998/06/10 08:21:57  img
 * ind_ripple added: allows weakening
 *
 * Revision 1.49  1998/03/25 10:28:48  img
 * Added support for polymorphic rewrites---type guessing takes place
 * when a rule is applied.  Wrapped all access to the recorded database.
 * Generalize conditional equations before making them rewrites.
 *
 * Revision 1.48  1998/02/17 13:50:25  img
 * record origin of equations; sinkable_or_cancellable added and used in ripple/6
 *
 * Revision 1.47  1998/02/11 12:43:25  img
 * erase_sequents_goal/2: added. Extra info on adding rewrite rules.
 *
 * Revision 1.46  1997/11/08 12:20:27  img
 * cosmetic changes
 *
 * Revision 1.45  1997/09/26 14:38:43  img
 * erase_sequent/2 added; delete/3 -> delete_one_id/3
 *
 * Revision 1.44  1997/07/09 15:26:41  img
 * Generalize predicates for rewriting/reduction rules to allow certain
 * variables to appear on the RHS or in the condition of a rule which do
 * not appear in the LHS.  (An extra argument carries this set.)  This
 * may be used (eg) for type variables in polymorphic expressions.
 *
 * Revision 1.43  1997/06/17 14:32:47  img
 * Pass registry explicitly.
 *
 * Revision 1.42  1997/06/05 10:42:03  img
 * Extra argument to equ/1 tag on equational rewrites to record type; replace_universal_vars/3: treat binding constructions directly rather than inside s/4.
 *
 * Revision 1.41  1997/05/05 14:12:54  img
 * skeleton_args/2 added.
 *
 * Revision 1.40  1997/04/07 11:41:11  img
 * rationalize code for equal length lists.
 *
 * Revision 1.39  1997/01/14 10:44:36  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.38  1996/12/12 12:41:25  img
 * Error message predicates.
 *
 * Revision 1.37  1996/12/04 12:17:46  img
 * All annotation abstracted
 * terminating/3 moved to so.pl
 * pick_an/4->5: extra argument parameterized the direction to be added
 *   to wave-fronts
 * well_annotated/2: swap parameters
 * meta_ripple/3: short-cut if WTT has no wave-fronts
 * parse_try_memo/4: use parse_memo/4 to cache wave rules
 * rewrite_rule/6: (ground case) bug removed
 * ripple_with_meta_ripple/_: allow more than one meta-ripple before a
 *   ripple proper
 *
 * Revision 1.36  1996/08/05  14:51:51  img
 * Cleaned up code for skeleton modulo sinks---it was not necessary to
 * use id_check (that has been deleted).  Some speed improvements.
 * Abstracting some annotation.
 *
 * Revision 1.35  1996/07/30  10:01:40  img
 * pick_an/4: Existentially quantify Skel.  Abstract meta-level functors
 * into wave_front_functor/1 etc.  well_annotated/1: parity bit incorrect
 *
 * Revision 1.34  1996/07/09 14:46:27  img
 * well_annotated/1 added: succeeds iff argument is a annotated term;
 * proper_rewrite/3: allow variable left-hand sides, providing the
 * condition is non-trivial.
 *
 * Revision 1.33  1996/06/18  17:16:35  img
 * helpful error messages
 *
 * Revision 1.32  1996/06/11  16:37:21  img
 * left_and_right_variants: tidied up and fixed some bugs.
 *
 * Revision 1.31  1996/05/24  09:37:05  img
 * Generalized add_rewrite_rule/2 into add_rule/3: first argument
 * indicates rewrite rule or reduction rule.  Both are treated in much
 * the same way, but reduction rules must be shown to be terminating.
 * Equality reduction rules are taken only from left to right;
 * implications only from right-to-left (ie. so that they are applicable
 * only in positions of positve polarity).  Rules based on _ = _ in _ are
 * distinguished from _ <=> _ using tags equ(_,_) and equiv(_).  Labelled
 * rewriting support added.
 *
 * Revision 1.30  1995/10/24  14:53:17  img
 * removed old parsing code
 *
 * Revision 1.29  1995/10/18  13:23:10  img
 * Newline and eof added for SWI
 *
 * Revision 1.28  1995/10/03  13:25:51  img
 * warning message removed
 *
 * Revision 1.27  1995/08/01  08:38:38  img
 * allow multiple conditions via conjunction
 *
 * Revision 1.26  1995/07/18  18:14:15  img
 * add_wave_rule removed; speeded-up parsing of rewrite rules
 *
 * Revision 1.25  1995/05/17  02:18:03  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.24  1995/05/10  18:27:08  img
 * 	* reverted to version 1.21 since old parser is needed for
 * 	  reduction rules (sigh)
 *
 * Revision 1.23  1995/05/10  14:38:53  img
 * 	* typo
 *
 * Revision 1.22  1995/05/10  03:54:17  img
 * 	* Removed lots of old wave-rule junk;  some cosmetic changes
 *
 * Revision 1.21  1995/04/28  16:43:56  img
 * 	* Tidied up add_wave_rule/1;  proper_rewrite/3 checks that
 * 	  variable conditions are met;  WARNING: {true} is compound so
 * 	  could be LHS of a rewrite---maybe we need to go to the
 * 	  trouble of checking for this pseudo-atomic case?
 *
 * Revision 1.20  1995/04/25  09:40:27  img
 * 	* fast_meta_ripple/2: move wave-fronts over identical function
 * 	  symbols.  meta_ripple/3 is too slow for this purpose.
 *
 * Revision 1.19  1995/03/29  10:47:57  img
 * 	* map_list_filter added
 *
 * Revision 1.18  1995/03/01  04:14:51  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.17  1995/03/01  03:42:10  img
 * 	* Cosmetic changes, removed singleton variables
 *
 * Revision 1.16  1995/02/28  02:42:13  img
 * 	* NOTE: pick_an does not add multiple holes to wave-fronts
 * 	  since it chooses a particular skeleton from Skels to work
 * 	  on.
 *
 * Revision 1.15  1995/02/28  00:20:48  img
 * 	* tidied up;  generalized some of the code by adding an
 * 	  argument indicating permissible wave-front directions
 *
 * Revision 1.14  1995/02/22  17:03:04  img
 * 	* ripple does not allow weakening;  weakening/2 plays that role
 *
 * Revision 1.13  1995/02/16  22:46:27  img
 * 	* optional code to enforce set equality of skeletons---this
 * 	  would require  weakening to be done explicitly
 *
 * Revision 1.12  1995/02/16  22:44:30  img
 * 	* re-order the clauses for pick_an so as to generate
 * 	  multi-hole solutions first (see comment there).
 *
 * Revision 1.11  1994/12/07  18:40:23  dream
 * 	* added explicit unify/2 check for soundness
 * 	* added version of replace_meta_vars which records the
 * 	  meta-variables introduced
 *
 * Revision 1.10  1994/09/30  14:07:23  dream
 * 	* changed all occurrences of copy/2 to copy_term/2
 *
 * Revision 1.9  1994/09/22  10:27:35  dream
 * 	* forgot to replace wf and wh in apply_subs!
 * 	* added add_rewrite_rule/1 to support the library interface to the
 * 	  pre-recored rewrite database.  Rewrite rules are added at
 * 	  the same time a wave-rule is parsed.
 *
 * Revision 1.8  1994/09/22  00:04:40  dream
 * 	* more (supposed) efficiency improvements: pre-compute the flag
 * 	  SinksPresent for each Skels in pick_an/4.   The idea is to
 * 	  prevent the need for a memberchk1_rec each time a sink
 * 	  annotation is to be added to a term.  The only time this flag
 * 	  needs to be updated is when we imitate and decscend recursively
 * 	  into a term (and hence similarly for the target skeleton).  This
 * 	  update is done by the map_list in map_pick_an/3 (wave_rules.pl)
 *
 * 	[ This efficiency improvement may well be made redundant if all
 * 	the rippling code is rewritten _over ground terms_. In this way the
 * 	(currently cumbersome) need for explicit id_check on sinks can
 * 	be avoided and prolog unification used to test for equality
 * 	modulo sinks. ]
 *
 * 	* removed spurious check for empty set in pick_an (wave_rules.pl)
 *
 * Revision 1.7  1994/09/21  23:17:39  dream
 * 	* really delete subset1/2 this time!
 *
 * Revision 1.6  1994/09/21  23:14:05  dream
 * 	* replaced pick_rule/5 clauses with the more familiar pre-recorded
 * 	  approach using the record database (cf. library.pl for building
 * 	  the rewrite database);  deleted the old convert_anns/2 and
 * 	  wave_to_wave code which is no longer required
 * 	* removed subset1/2 which is no longer required
 *
 * Revision 1.5  1994/09/21  21:59:28  dream
 * 	* redefined match_erasure/2 so that the erasure of LHS (in the
 * 	  body of ripple/5) need not be repeatedly computed for each
 * 	  success of pick_rule (wave_rules.pl)
 * 	* removed pick_an_pos/4, since this was unused (wave_rules.pl)
 * 	* IMPORTANT: I have propagated the convert_anns conversion code up
 * 	  into the body of the dynamic rippling, but this has the effect of
 * 	  decentralizing the representation of annotations.  This will be a
 * 	  problem when soft wave fronts are to be dealt with.  We do not yet
 * 	  have this case: THIS CODE WILL NOT WORK WITH SOFT WAVE FRONTS!
 * 	  (wave_rules.pl)
 *
 * Revision 1.4  1994/09/21  09:44:09  dream
 * 	* first version with dynamic wave-rule parsing/application
 *
 * Revision 1.3  1994/09/16  13:38:55  dream
 * 	* removed potential-waves/2
 *
 * Revision 1.2  1994/09/16  10:53:23  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: wave_rules.pl,v 1.58 2008/05/21 14:14:14 smaill Exp $').

/*
 * Dynamic wave-rule application/parsing
 * 
 * To rewrite, take term T and try to rewrite at some position T'.  Insist that
 * T' is annotated (somewhere).  Do book keeping to mark replacement position
 * using the magic of prolog meta-variables.
 * All skeleton equality is considered modulo any sinks present in WT
 * (see bb note 939).
 *
 * Kind is one of "ripple_and_cancel", "direction_in", "direction_out"
 * or "direction_in_or_out", this constrains the direction of the
 * wave-fronts that will be generated: eg "direction_in" means only
 * inward wave-front will be present on NWTT, and that all these
 * fronts appear above a sink position.  */

 /* ind_ripple and ripple are the same but ind_ripple _does_ allow weakening */
ind_ripple(Kind,WTT,NWTT,Cond,Rn,Dir,TI) :-		% rewrite at some (annotated) position)
    ((Kind == ripple_and_cancel;
      Kind == direction_in; 
      Kind == direction_out;			% just a check
      Kind =  direction_in_or_out) ->		% default is in_or_out
     true; clam_error('ripple/6: Flag must be one of ripple_and_cancel, direction_in, direction_out or direction_in_or_out.')),
    /* we may need the erasure of WTT a few times here, so fetch it first */
    erase(WTT, WTTerasure),
    rewrite_rule_no_unify(WTTerasure,LHS,RHS,Cond,Dir,TI,Rn,_),
						% pick a rule, but dont instantiate
    /* think of this as direction_in for a while... */
    (Kind == ripple_and_cancel -> Kind2=direction_in; Kind2=Kind),
    superimpose(Kind2,WTT,LHS,RHS,NWTT),		% perform superposition (if successful)
    if(\+ Kind == ripple_and_cancel, sinkable(NWTT)),
/*    skeletons(WTT,InSkels),
    skeletons(NWTT,OutSkels),			% DO NOT weaken
    lengtheq(InSkels,OutSkels),  
*/
    WTTerasure = LHS.				% instantiate Cond

ripple(Kind,WTT,NWTT,Cond,Rn,Dir,TI) :-		% rewrite at some (annotated) position)
    ((Kind == ripple_and_cancel; 
      Kind == direction_in; 
      Kind == direction_out;			% just a check
      Kind =  direction_in_or_out) ->		% default is in_or_out
     true; clam_error('ripple/6: Flag must be one direction_in, direction_out or direction_in_or_out.')),
    /* we may need the erasure of WTT a few times here, so fetch it first */
    erase(WTT, WTTerasure),
    rewrite_rule_no_unify(WTTerasure,LHS,RHS,Cond,Dir,TI,Rn,_),
						% pick a rule, but dont instantiate
    (Kind == ripple_and_cancel -> Kind2=direction_in; Kind2=Kind),
    superimpose(Kind2,WTT,LHS,RHS,NWTT),		% perform superposition (if successful)
    if(\+ Kind == ripple_and_cancel, sinkable_or_cancellable(NWTT)),
    skeletons(WTT,InSkels),
    skeletons(NWTT,OutSkels),			% DO NOT weaken
    lengtheq(InSkels,OutSkels),  

    WTTerasure = LHS.				% instantiate Cond

/* NWTT is the same as WTT but the wave-measure is smaller for the
 * former and their skeletons are identical. This is really a sort of
 * restricted difference match.  D is the predicate describing the
 * directions permitted.  The case when WTT does not contain
 * wave-fronts is optimized away (if there are no wave-fronts, there
 * can only be a single skeleton, and it must be identical to WTT:
 * NB: skeletons/2 preserves sinks in WTT).  */
meta_ripple(D,WTT,NWTT) :-
    skeletons(WTT,S),
    \+ S == [WTT],
    erase(WTT,E),
    pick_an(dir,no,S,E,T),
    maximize_orient(D,WTT,T,NWTT).

fast_meta_ripple(WTT,NWTT) :-
    ann_exp_at(WTT,Pos,ST),
    ST =.. [F,Farg],  iswf(Farg,hard,out,SST),
    SST =..  [F,Farg2], iswh(Farg2,Hole),
    SSTn =.. [F,Hole],
    STn =.. [F,Farg3],iswh(Farg3,SSTn),
    iswf(NWTTp, hard, out, STn),
    replace(Pos,NWTTp,WTT,NWTT).
fast_meta_ripple_star(WTT,NWTT) :-
    fast_meta_ripple(WTT,NWTT).
fast_meta_ripple_star(WTT,NWTT) :-
    fast_meta_ripple(WTT,WTTp),
    fast_meta_ripple_star(WTTp,NWTT).



/* 
 * rippling with meta-rippling
 */
ripple_with_meta_ripple(D,WTT,NWTT,Cond,Rn,Dir,TI) :-
    ind_ripple(D,WTT,NWTT,Cond,Rn,Dir,TI).
ripple_with_meta_ripple(D,WTTpre,NWTT,Cond,Rn,Dir,TI) :-
    fast_meta_ripple(WTTpre,WTT),    
    ripple_with_meta_ripple(D,WTT,NWTT,Cond,Rn,Dir,TI).
/*ripple_with_meta_ripple(D,WTTpre,NWTT,Cond,Rn,Dir,TI) :-
    weaker(WTTpre,WTT),    
    write(weaker:WTT),nl,
    ripple_with_meta_ripple(D,WTT,NWTT,Cond,Rn,Dir,TI).
*/
:- dynamic parse_memo/4.

/* superimpose(Direction, T, LHS, RHS, ST)
 * T is a term, LHS and RHS the halves of an unannotated rewrite rule
 * and returns the annotated replacement ST. Direction describes the
 * direction of the generated wave-fronts on ST
 */
superimpose_without_cache(Direction,T, LHS, RHS, ST) :-
    copy_an(T,LHS,ALHS,Subs),           % copy annotations and generate subs
    parse(Direction,_,ALHS,RHS,ARHS),   % find compatible RHS from annotated LHS
    apply_subs(Subs,ARHS,ST).           % Apply substitutions to parsed RHS

/* Same as above, but exploits cache.  */
superimpose(Direction,T, LHS, RHS, ST) :-
    copy_an(T,LHS,ALHS,Subs),           % copy annotations and generate subs
    (parse_try_memo(ALHS,Direction,RHS,ARHS);
     (parse(Direction,_,ALHS,RHS,ARHS),	% find compatible RHS from annotated LHS
      add_to_parse_memo(ALHS,Direction,RHS,ARHS))),
    %% Apply substitutions to parsed RHS
    apply_subs(Subs,ARHS,ST).


add_to_parse_memo(ALHS,Direction,RHS,ARHS) :-
    /* Don't extend the memo table if we have seen this before! */
    \+ (parse_memo(MAL,MDirection,_,MAR),
	equal_modulo_meta_variable_renaming(dummy(ALHS,Direction,ARHS),
					    dummy(MAL,MDirection,MAR))),
    assert(parse_memo(ALHS,Direction,RHS,ARHS)).

empty_wave_rule_cache :-
    retractall(parse_memo(_,_,_,_)),
    plantraced(23,clam_info('Wave-rule cache is now empty.\n',[])).
parse_try_memo(AL,Direction,R,AR) :-
    parse_memo(MAL,MDirection,MR,AR),
    equal_modulo_meta_variable_renaming(dummy(MAL,MDirection,MR),
					dummy(AL,Direction,R)).

/*
 * parse takes annotated left hand side, unannotated right,
 * and annotates right.  For convenience, return the Skeletons of AL.
 * Direction describes the direction of the generated wave-fronts on AR
 */
parse(Direction,Skels,AL,R,AR) :-
    skeletons(AL,Skels),
    (sinks_present(Skels)->SP=yes; % initialize the flag
                           SP=no),
    pick_an(dir,SP,Skels,R,A),			% annotate RHS
    maximize_orient(Direction,AL,A,AR).		% Orient RHS, in/out direction

% Check if T2 matches erasure of T1 (but don't perform instantiations)]
% (this is just a quick check)
match_erasure(T2,ET) :-
    \+ \+ ET = T2.

/* Picks all possible (maximally split) annotations; try to improve
   efficiency by looking at the list of skeletons, if there is one.   */
pick_an(_Dir,_,Skels,Term,Term) :-
     /* this is an optimization in the case of a single skeleton which
        is identical to the term we are trying to annotated.  If these are
        ==, there can only be one solution.  */
     \+ var(Skels),
     Skels = [Skel],
     Skel == Term,!.
    

pick_an(_Dir,yes,_Skels,T,Sink) :-
    issink(Sink,T).
    /* T can only be a sink if one of the skeletons is a sink too */

pick_an(_Dir,_SinksPresent,Skels,T,T) :-
    /* an atomic can only be unannotated if it appears in a skeleton */
    \+ compound(T),!,
    (var(Skels); member1(T,Skels)),!.
pick_an(Dir,_SinksPresent,Skels,T,AT) :- 
    %% filter out all functors in Skels which are different from 
    %% F, since these must be hidden, and this clause is in the business of
    %% imitation.  If there are no skeletons in Skels which have F as a top-level
    %% then we must hide, since imitation is pointless.  Note that we cannot commit
    %% either way (hide/imitate) in the case of same functor, since both are
    %% required for completeness.
    %% 
    %% SinksPresent is irrelevant here since we need to recompute that
    %% for each of the  subskeletons of Skels which partially match F.
    %% (This is done in map_pick_an).  In fact, it is not irrelevant
    %% if we make the restriction that a sink cannot appear inside a sink.  
    T =.. [F|Args], 
    if(compound(Skels),
       setof(FArgs,	
	     Skel^(member(Skel,Skels),
		   compound(Skel),
		   Skel =.. [F|FArgs]),		% preserve all which can imitate
	     FilteredSkels)),			% all the argument skeletons
    map_pick_an(Dir, FilteredSkels,Args, AnArgs), 
    AT =.. [F|AnArgs].

    /* this clause is in the business of hiding F.  In the case of different
     * functors, we must hide for skeleton preservation but, as above, for
     * identical functors we can do either.  So in this case we cant constrain, since
     * hiding preserves skeletons.  Since Skels is preserved, so is SinksPresent.
     */
pick_an(Dir,SinksPresent,Skels,T,AT) :-
    T =.. [F|Args],
    pick_an(Dir,SinksPresent,Skels,Args,AnArgs,0),  % hole-ize and recursively annotate
    AnT =.. [F|AnArgs],
    iswf(AT,hard,Dir,AnT).

% stick a hole around at least one subterm
/* I don't know the best order of these clauses.  Putting the H-H clause second
 * has the effect of returning weaker solutions first (terms are left unannotated),
 * putting the H1-H2 clause second and the H-H clause last adds as much annotation
 * as is possible.  The current setup is an attempt to mimic clam 2.1 behaviour, 
 * at least as I observed it planning rotlen (img/mrg/feb95), that is, weakenings 
 * (if there are any) on backtracking.
 */
pick_an(_,_SinksPresent,_Skels,[],[],N) :- N > 0.
pick_an(Dir,SinksPresent,Skels,[H1|T1],[H2|T2],N) :-
    pick_an(Dir,SinksPresent,Skels,H1,AH1),
    iswh(H2,AH1), 
    NN is N+1, 
    pick_an(Dir,SinksPresent,Skels,T1,T2,NN).
pick_an(Dir,SinksPresent,Skels,[H|T1],[H|T2],N) :-
    pick_an(Dir,SinksPresent,Skels,T1,T2,N).

/* FilteredSkels is a list of lists of skeletons; each sublist corresponds to 
 * a possible skeleton of the corresponing element of Args
 */
map_pick_an(Dir,FilteredSkel, Args, AnArgs) :-
    var(FilteredSkel),!,
    maplist(pick_an(Dir,no,_),Args, AnArgs).
map_pick_an(Dir,FilteredSkel, Args, AnArgs) :-
    nary_zip(FilteredSkel,ArgsSkels),
    map_list(ArgsSkels, I:=>O, 
	     (sinks_present(I)->O=yes; O=no),
	     SinksPresentList),
    maplist(pick_an(Dir), SinksPresentList, ArgsSkels,Args, AnArgs).

nary_zip([[]|_],[]).
nary_zip(L1,[Cars|Rest]) :-
    strip(L1,Cars,NewL1),
    nary_zip(NewL1,Rest).

strip([], [], []).
strip([[H|T] | Rest] , [H|Cars], [T|Trest]) :-
    strip(Rest, Cars, Trest).


% Routines to copy annotations and apply substitutons.  Recall that
% rewrite rules use Prolog variables as match variables.  We can't use this
% though as our matching/substitution is not the standard one. 

% copy_an(+A,+Pat,-APat,-Sub) 
% Preconditions: A is well-annotated and its erasure matches Pat
% Depends on depend on 1 functor thick normal form so that we
% do not pick up substitution wh(...)/X where wh(...) is not a WAT
%
% We move the annotations from A onto Pat (in result APat).  As we reach
% the leaves of Pat we generate a substitution Sub.  Note that the ordering of
% these clauses matters and junk will be generated if preconditions are not met.
% 
% Use auxilliary bit to keep track of wf/sk (wavefront or skel)
%
% A may be a non-ground term: variables are not instantiated.

copy_an(A,Pat,APat,Sub) :- copy_an(sk,A,Pat,APat,Sub).

copy_an(_,A,_Pat,_APat,_Sub) :- 
    metavar(A),!,
    clam_error('Metavariables not yet supported in rippling.').
/* In subsequent clauses we assume A is not a variable */ 
copy_an(wf,A,Pat,APat,Sub) :- 
    iswh(A,A1), !,				% A is wh
    iswh(APat,APat1),				% copy over
    copy_an(sk,A1,Pat,APat1,Sub).		% recurse
copy_an(sk,SinkA,Pat,SinkPat,[sub(Pat,A,sk)]) :-
    issink(SinkA,A),
    issink(SinkPat,Pat),
    var(Pat),!.
/* I can't think of a reason not to allow sinks around constants! */
copy_an(sk,SinkA,B,SinkBB,Sub) :-
    issink(SinkA,A),
    issink(SinkBB,BB),
    copy_an(sk,A,B,BB,Sub).
copy_an(wf,SinkA,_,_,_) :-
    issink(SinkA,_),!,
    clam_error('copy_an/5: sink inside wave-front').

copy_an(St,A,Pat,Pat,[sub(Pat,A,St)]) :-
    var(Pat), !.				% Pat is a var
/* In this clause we are really checking that the erasure of A and Pat
   match: they must be identical when A is atomic since in that case
   the erasure of A is A, and since Pat is non-var, it can only match
   if it is the same atom.  */
copy_an(_,A,Pat,Pat,[]) :-
    atomic(A), !,             % A is atom (so should Pat!)
    (Pat == A -> true;
     clam_internal_error('copy_an/5.6 Erasure does not match pattern.',[])).

copy_an(sk,A,Pat,APat,Sub) :-
    iswf(A,hard,Dir,A1), !,				% A is wf
    iswf(APat,hard,Dir,APat1),			% copy over
    copy_an(wf,A1,Pat,APat1,Sub).		% recurse

copy_an(St,A,Pat,APat,Sub) :-			% other functor
  A =.. [F|Args],
  Pat =.. [F|PArgs],
  copy_args(Args,PArgs,APargs, Sub,St),
  APat =.. [F|APargs].
  
copy_args([],[],[],[],_).

copy_args([A|AR],[PA|PAR],[APA|APAR],S,St) :-
  copy_an(St,A,PA,APA,S1),
  copy_args(AR,PAR,APAR,SN,St),
  merge_subs(S1,SN,S).

% Two instances of X must have same skeleton
% If one is annotated and the other isn't, you can merge provided unannotated
% var is in a wave-front

merge_subs([],S,S).

merge_subs([sub(V,T,St)|R],S1,S2) :-
  sub_lookup(V,T1,St1,S1), !, 
  merge_subs(St,T,T1,V,St1,R,S1,S2).

merge_subs([H|R],S1,[H|S2]) :- merge_subs(R,S1,S2).

merge_subs(wf,T,T1,_,wf,R,S1,S2) :- !, T == T1, merge_subs(R,S1,S2).

merge_subs(sk,T,T1,_,sk,R,S1,S2) :- !, T == T1, merge_subs(R,S1,S2).

merge_subs(wf,T,T1,_,sk,R,S1,S2) :- !,
    erase_id(T1,T),
    merge_subs(R,S1,S2).

merge_subs(sk,T,T1,V,wf,R,S1,S2) :- !, 
    ((unannotated(T) ->  T == T1, merge_subs(R,S1,S2));
     (erase_id(T,T1), S2 = [sub(V,T,sk)|NS2],
      delete_one_id(S1,sub(V,T1,wf),NS1), merge_subs(R,NS1,NS2))).

sub_lookup(V,T,St,[sub(V1,T,St)|_]) :-
    V == V1,!.					% should only be one
sub_lookup(V,T,St,[_|Sub]) :-
    sub_lookup(V,T,St,Sub).

% apply_subs(Subs,Pat,Res)
% apply substitution Subs to annotated pattern, resulting in Res.
% Unfortunately can't use normal Prolog unification as we must strip
% annotation when substituting into wave-fronts.

apply_subs(Subs,Pat,Res) :-
    status_tree_map(ap_sub(out,Subs),ap_sub(in,Subs),Pat,Res).

ap_sub(in,Subs,Leaf,Res) :-
    (sub_lookup(Leaf,T,_,Subs) -> 
     erase(T,Res) ; Res = Leaf).
ap_sub(out,Subs,Leaf,Res) :-
    (sub_lookup(Leaf,T,_,Subs) -> 
     Res = T ; Res = Leaf).

is_skeleton(A,B) :-
    skeletons(A,As),
    member(B,As).
share_skeleton(A,B) :-
    skeletons(A,As),
    skeletons(B,Bs),
    member(AA,As),
    member(AA,Bs),!.
skeletons(T,Skelset) :-
    unannotated(T), Skelset = [T], !.		% Unannotated --- return self

/* We keep the skeleton of a sink around and try to use it later
 * when comparing skeletons then, we allow sinks to 
 * match, even when X and Y are different (this is what I mean by 
 * "modulo sinks" in the preamble of this file).
 */
skeletons(Sink,[Sink]) :-
    issink(Sink), !.				% sink case

skeletons(T,Skelset) :-				% Wave front case
  wfholes(T,Holes),				% list of holes
  maplist(skeletons, Holes, HoleSkels),		% skel sets for each hole
  lflatten(HoleSkels,Skelset),			% flatten to list of skels
  !.   

skeletons(T,Skelset) :-				% Normal function case
   T =.. [F|Args],
   maplist(skeletons, Args, Skels), 
   setprod(Skels,FArgs),
   maplist(args_to_func(F), FArgs, Skelset).

args_to_func(F,L,T) :- T =.. [F|L].

% Calculuate weakenings of term T  A weakening consist of taking a wave-front
% w/ multiple holes and removing some holes.  Weakest terms  are maximally weak. 

weaken(T,T) :- \+ compound(T), !.
weaken(T,Q) :-
    wfparts(T,F,Args,Type,Dir),
    holeweak(Args,WArgs,0),
    wfparts(Q,F,WArgs,Type,Dir).
weaken(T,Q) :-
    T =.. [F|Args],  
    maplist(weaken, Args, WArgs), Q =.. [F|WArgs].

weaker(T,Q) :- weaken(T,Q), \+ T == Q.
weakest(T,Q) :- weaken(T,Q),  \+ weaker(Q,_).

weakenings(T,S) :- setof(W,weakest(T,W),S).

holeweak(A,B, C) :-
    holeweak(A,B,C,0).

% argument so at least 1 hole remains, and at least 1 hole removed
holeweak([],[], N, M) :- 
    N > 0, M > 0,!.    
holeweak([H|T1],[H|T2],N,M) :-			% keep a hole/keep a non-hole
    (iswh(H) -> N1 is N+1 ; N1 is N),
    holeweak(T1,T2,N1,M).
holeweak([H1|T1],[H2|T2],N,M) :-		% drop a hole
    striphole(H1,H1Hole),
    erase(H1Hole,H2),
    M1 is M+1,
    holeweak(T1,T2,N,M1). 

% Orientation routines.  To find maximal orientation generate (naively)
% all  possible annotations with measure and return max ones.  Only directions
% satisfying the predicate Direction are tried.

maximize_orient(Direction,OL,R,OR) :-                   
  setof(AM, an_with_measure(Direction,R,AM),AMSet),	
						% set of all orientation/measures
  measure(OL,OLM),				% measure of LHS
  max_solution(OLM,AMSet,OR).			% Pick max solution < LHS measure

% maximal solution for out orientation

max_solution(Upper,Set,Max) :-			% set is annotation/measure pair
   member(pair(Max,MMax),Set),			% <Max,MMax> Measure in set
   mcompare(Upper,MMax),			% Measure less than that of upper
   \+ (member(pair(_,Measure),Set),		% Nothing else
       mcompare(Upper,Measure),			% that is less than upper
       mcompare(Measure,MMax)).			% but also greater than what we have

% nondeterministically return an annotation of T 
an_with_measure(Direction,T, ATWM) :-
    flip_orient(Direction,T,AT),
    measure(AT,ATM),
    pair(ATWM,AT,ATM).

measure(T,M) :-					% in/out pair of weakenings measures
   weakenings(T,TWS),				% compute all weakenings
   maplist(simple_measure(out),TWS,Mout),	% compute out measures
   maplist(simple_measure(in),TWS,Min),		% compute in measures
   pair(M,Mout,Min).				% pair them

% Compute measure list of simply annotated term. 
% Measure used is WIDTH measure (see CADE-12 paper) which gives each wave-front
% a weight of 1.  This measures width as wave-fronts are already maximally split.
% Note that routines work for computing both in/out measures so we pass in the
% direction Dir so we only count the appropriate fronts.

simple_measure(_,T,[0]) :- \+ compound(T), !.     % Atoms have weight 0

simple_measure(Dir,T,M) :-                 % wavefront with single argument
  iswf(T,Orient),
  wfholes(T,[Arg]),
  simple_measure(Dir,Arg,[AH|AT]),         
  (Dir == Orient ->  AH1 is AH + 1; AH1 = AH),   % Check that direction corresponds to
  M = [AH1|AT], !.                               % what we are measuring

simple_measure(_,T,_) :- 
    iswh(T), 
    clam_internal_error('simple_measure/3.1').	% Shouldn't happen

simple_measure(Dir,T,[0|MRest]) :-                % Non-wave-front functor.
  T =.. [_|Args],
  maplist(simple_measure(Dir),Args,ArgVals),      % get measures for arguments
  talley(ArgVals,[MRest]).                        % add these pointwise

% measure compare.  Compare lexicographically,  (Note ordering of clauses significant!)

mcompare(pair(O1,_),pair(O2,_)) :-  multi_greater(out,O1,O2), !.
mcompare(pair(O1,I1),pair(O2,I2)) :-  
   \+ multi_greater(out,O2,O1),                      % hence they have equal measure
   multi_greater(in,I1,I2).                          % so check inner measurement

% compare using multiset extension of simple ordering

multi_greater(Dir,ML,NL) :-
   list2mset(ML,M),   list2mset(NL,N),
   \+ mseteq(M,N),
   forall(X/Nx,N, 
      (mmember(X/Mx,M),!,
      if(Nx>Mx,
          (thereis(Y/My,M,
                  (mmember(Y/Ny,N),
                   My > Ny,
                   simple_compare(Dir,Y, X))
                   )
         )
       ),!
      )
   ).

/* compare using multiset extension ordering of a quasi-ordering P.
   This predicate is taken from the Huet/Oppen defintion, which it
   closely follows.  A more efficient implementation can be found in
   Jouannaud 1992 (MIT/TM/219).  */
multi_extension_HO(P,M,N) :-
    \+ mseteq(M,N),				% not equal
    forall(X/Nx,N,				% pick an X in N
	   (mmember(X/Mx,M),!,			% which occurs in M
	    if(Nx>Mx,
	       (thereis(Y/My,M,
			(mmember(Y/Ny,N),
			 My > Ny,
			 call(P,Y,X))
		       )
	       )
	      ),!
	   )
	  ).

/* Zs is the difference between Xs and Ys (multiset).  Equality is
   modulo the equivalence relation E, so we are really interested in
   equivalence classes */
mset_difference(TP,NTP,Vars,E,Xs,Ys,Zs) :-
    %% there are Ny (>0) Y in Ys.  We want to remove as many
    %% of these from Xs as possible
    member(Y/Ny,Ys),
    delete_ms(TP,NTP,Vars,E,Y/Ny,Xs,Xrest,Nx),!, % still things to delete
    delete_one_id(Ys,Y/Nx,Yrest),
    mset_difference(TP,NTP,Vars,E,Xrest,Yrest,Zs).
mset_difference(TP,TP,_Vars,_E,Xs,_Ys,Xs).

/* S2 is as S1, only M copies of Y in S1 are deleted from S2.
   Subject to the constraint that M <= N (i.e., at most N copies are
   removed) and that M is as large as possible (i.e., as many as
   possible are deleted, subject to M <= N).

   Procedurally: delete as many (but not more than N) Ys from S1 to
   get S2   */
delete_ms(_,_,_,_E,_Y/_N,[],_S2,_M) :-
    !,fail.
delete_ms(TP,NTP,Vars,E,Y/N,[X/N|S1],S1,N) :-
    Call =.. [E,TP,NTP,Vars,Y,X],
    Call,!.    /* call(TP,NTP,Vars,E,Y,X),!.*/
delete_ms(TP,NTP,Vars,E,Y/N,[X/L|S1],[X/Nx|S1],N) :-
    N < L,
    Call =.. [E,TP,NTP,Vars,Y,X],
    Call,   /*    call(E,Y,X), */
    Nx is L - N.
delete_ms(TP,NTP2,Vars,E,Y/N,[X/L|S1],S2,M) :-
    L < N,
    Call =.. [E,TP,NTP,Vars,Y,X],
    Call,   /*    call(E,Y,X), */
    %% delete X/L, and then some more
    NewN is N - L,
    delete_ms(NTP,NTP2,Vars,E,Y/NewN,S1,S2,MM),
    M is MM + L.
delete_ms(TP,NTP,Vars,E,Y/N,[S|S1],[S|S2],M) :-
    delete_ms(TP,NTP,Vars,E,Y/N,S1,S2,M).
delete_ms(TP,TP,_Vars,_E,_Y/_N,[],_S2,0).

/* S and T are equal under equivalence relation E  */
mseteq(TP,NTP2,V,E,S,T) :-
    mset_difference(TP,NTP,V,E,S,T,[]),
    mset_difference(NTP,NTP2,V,E,T,S,[]).





% Simple comparison is lex or revlex.  Pad to make lists equal length.

simple_compare(out,SLM,SRM) :- pad(SLM,SRM,L,R),  revlex(L,R).
simple_compare(in,SLM,SRM) :- pad(SLM,SRM,L,R), lex(L,R).


% pad --- 0 pads lists to make same size
pad([],[],[],[]) :- !.
pad([H1|T1],[],[H1|N1],[0|N2]) :- pad(T1,[],N1,N2).
pad([], [H2|T2],[0|N1],[H2|N2]) :- pad([],T2,N1,N2).
pad([H1|T1],[H2|T2],[H1|N1],[H2|N2]) :- pad(T1,T2,N1,N2).

% lex over lists of same size
lex([],[]) :- !, fail.
lex([H|T1],[H|T2]) :- lex(T1,T2), !.
lex([H1|_],[H2|_]) :- H1 > H2.

revlex(A,B) :- rev(A,RA), rev(B,RB), lex(RA,RB).

% Functions for handling orientation direction, annotation decomposition
% Note that variables in terms may be Prolog variables and these shouldn't
% be instantiated by tests/decomposition.  Hence sometimes I must use == and
% novar.  Don't mess with these!

/* DANGER: these predicate names are overloaded as flags to the
 * various methods, so if they are changed here, they must also be
 * changed there too!  (this is just to save mapping flags).
 */
direction_in_or_out(out).
direction_in_or_out(in).
direction_out(out).
direction_in(in).

/* flip_orient(Direction,T,T') 
 * T and T' are the same, only all wave-fronts in T' have a direction X
 * whilst all those in T are anonymous (ie. "dir"), such that
 * Direction(X) is satisfied.  Typically, Direction(in) and Direction(out)
 * will hold, but other possibilties are useful too (eg restriction to "out"
 * only).
 */
flip_orient(_Direction,T,T) :-
    \+ compound(T),!.
flip_orient(Direction,WF,NewWF) :-
    wfparts(WF,F,Args,Type,Dir),			% a wave-front here
    !, % Why is this a variable?
    (var(Dir) -> clam_internal_error('flip_orient/3.2',[]);true),
    D =.. [Direction,NewDir], call(D),		% get the direction
    maplist(flip_orient(Direction),Args,NArgs),
    wfparts(NewWF,F,NArgs,Type,NewDir).
flip_orient(Direction,T,NT) :-
    T =.. [F|Args],
    maplist(flip_orient(Direction),Args,NArgs),
    NT =.. [F|NArgs].

addhole(X,Y) :- iswf(Y,X).
striphole(X,Y) :- nonvar(X), iswh(X,Y).
stripsink(X,Y) :- nonvar(X), issink(X,Y).
stripfront(WF,T,D,S) :- nonvar(WF), iswf(WF,T,D,S).

meta_level_annotation(F) :-
    wave_front_functor(F);
    wave_hole_functor(F);
    wave_hole_coloured_functor(F);
    sink_functor(F).

/* if Term is not a wave-front, Args is simply the list of terms to
   which the top-most functor of Term is applied.  If Term is a
   wave-front, Args are those arguments of that functor which are in
   the skeleton (i.e., inside a hole).  Fails if Term is compound.   */
skeleton_arguments(Term,_Args) :-
    atomic(Term),!,fail.
skeleton_arguments(Term,Args) :-
    wfholes(Term,Args),!.
skeleton_arguments(Term,Args) :-
    Term =.. [_|Args].
   

iswf(WF,Dir) :- iswf(WF,_,Dir,_).
iswf(WF,T,Dir) :- iswf(WF,_,Dir,T).
iswf(X) :- nonvar(X), iswf(X,_).
iswf2(X,  T,D,S) :-
    nonvar(X),iswf(X,T,D,S).

issink(X) :- nonvar(X), issink(X,_).
issink2(X,Y) :- nonvar(X), issink(X,Y).
iswh(X) :- nonvar(X), iswh(X,_).
iswh2(X,Y) :- nonvar(X), iswh(X,Y).
iswh_colour(X) :- nonvar(X), iswh_colour(X,_,_).

wfparts(X,F,Args,Type,Dir) :- 
    iswf(X,Type,Dir,T),
    T =.. [F| Args].
wffunc(W,F) :- wfparts(W,F,_,_,_).
wfargs(WF, Args) :- 
    iswf(WF,T,_),
    T =.. [_| Args].

wfholes(T,Holes) :- wfargs(T,TArgs), convlist(striphole,TArgs,Holes).

/* Term is a wave-front with functor Front; ArgList are its tagged
   arguments; a tagged argument is of the form hole:T or front:T,
   meaning that the argument is either in a hole or front,
   respectively.  This code assumes that Term is well-annotated. */
is_annotated(Term,Front,ArgList) :-
	wfparts(Term,Front,AnnArgs,_,_),
	is_annotated_(AnnArgs,ArgList).
is_annotated_([],[]).
is_annotated_([Ann|AnnArgs],[hole:A|As]) :-
	striphole(Ann,A),!,
	is_annotated_(AnnArgs,As).
is_annotated_([Ann|AnnArgs],[front:Ann|As]) :-
	is_annotated_(AnnArgs,As).

annotated(T) :- \+ compound(T), !, fail.    % T have anny annotation?
annotated(T) :- iswf(T), !.   
annotated(T) :- iswh(T), !.   
annotated(T) :- issink(T), !.
annotated(T) :- T =.. [_|Args],  somechk(annotated,Args).
unannotated(T) :- \+ annotated(T).


/* ensure T is well-annotated  */
well_annotated(T) :-
    well_annotated(hole,T).

well_annotated(_,Atom) :-
    (atomic(Atom); var(Atom)),
    !.
well_annotated(Flag, Sterm) :-
    issink(Sterm,Sink),
    !,
    Flag == hole,
    well_annotated(hole,Sink).
well_annotated(Flag, WFterm) :-
    iswf(WFterm,WF,_), !,
    Flag == hole,
    compound(WF),				% there must be a wave-front
    \+ iswf(WF,_,_),			% can't have nested fronts
    WF =.. [_|As],
    well_annotated_map1(As,front).
well_annotated(_, Hterm) :-
    %% holes are dealt with only inside map1/2 version.  HTerm cannot
    %% be a var or an atom (by the first clause). 
    iswh(Hterm,_), !, fail.
well_annotated(Flag, Term) :-    
    %% Term is non-var and compound (by first clause)
    Term =.. [_|As],
    all(well_annotated(Flag),As).

/* Inside a front, so check for at least one hole, and no
   sinks. Furthermore, all non-holes must be unannotated, since they
   are in a wave-front. */
well_annotated_map1([],front) :-
    !,fail.
well_annotated_map1([Sterm|_],front) :-
    issink(Sterm),
    !,fail.
well_annotated_map1([Hterm|Rest],front) :-
    iswh2(Hterm,Hole), !,
    /* Found one; check Rest are well annotated, but don't need more holes */ 
    well_annotated(hole,Hole),
    well_annotated_map2(Rest,front).
well_annotated_map1([WF|Rest],front) :-
    well_annotated(front,WF),
    well_annotated_map1(Rest,front).
    
well_annotated_map2([],_).
well_annotated_map2([H|Hs],Flag) :-
    iswh(H,HH),!,
    well_annotated(hole,HH),
    well_annotated_map2(Hs,Flag).
well_annotated_map2([H|Hs],Flag) :-
    !,unannotated(H),
    well_annotated_map2(Hs,Flag).

/*
 * erase(+P,-Q) Q is P with all annotation removed
 */
erase_sequent(H==>G,HH==>GG) :-
    unannotated_hyps(H,HH),
    erase(G,GG).
erase_sequents([],[]).
erase_sequents([HG|HGs],[HGe|HGse]) :-
    erase_sequent(HG,HGe),
    erase_sequents(HGs,HGse).
/* as above, but only remove annotation from the goal of each sequent */
erase_sequents_goal([],[]).
erase_sequents_goal([H==>G|HGs],[H==>Ge|HGse]) :-
    erase(G,Ge),
    erase_sequents_goal(HGs,HGse).
erase(T,T) :- \+ compound(T), !.
erase(T,Q) :- iswf(T,Arg,_), erase(Arg,Q), !.
erase(T,Q) :- iswh(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- issink(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- T =.. [F|Args],  maplist(erase, Args, EArgs), Q =.. [F|EArgs].

/*
 * erase_id(+P,-Q) Q is identical to P with all annotation removed
 * (faster than erase(P,X), X == Q).
 */
erase_id(T,S) :- \+ compound(T), !, T == S.
erase_id(T,Q) :- iswf(T,Arg,_), erase_id(Arg,Q), !.
erase_id(T,Q) :- iswh(T,Arg), erase_id(Arg,Q), !.
erase_id(T,Q) :- issink(T,Arg), erase_id(Arg,Q), !.
erase_id(T,Q) :- T =.. [F|Args],  Q =.. [F|EArgs], maplist(erase_id, Args, EArgs).

% sink stuff    represent sink as functor "sink"  (Admittedly not creative!)
% sinkable if term has no inward wavefront that does not have sink beneath

sinkable(T) :- \+ compound(T), !.       
sinkable(T) :-  % don't bother discriminating holes from non-holes
    iswf(T,ST,out), !, sinkable(ST).  
sinkable(T) :-  % recursive call as there could be nested fronts!
    iswf(T,ST,in), !, sinkwithin(ST), sinkable(ST).
sinkable(T) :-  T =.. [_|Args],  all(sinkable,Args).

/* As sinkable, but a term is sinkable_or_cancellable iff there is a
sink or an outboad wave-front beneath all in-bound wave-fronts.  */ 

sinkable_or_cancellable(T) :- \+ compound(T), !.       
sinkable_or_cancellable(T) :-
    iswf(T,ST,out), !, sinkable(ST).  
sinkable_or_cancellable(T) :-
    iswf(T,ST,in), !, sink_or_wfout_within(ST), sinkable_or_cancellable(ST).
sinkable_or_cancellable(T) :-
    T =.. [_|Args],
    all(sinkable_or_cancellable,Args).

sinkwithin(T) :- \+ compound(T), !, fail.
sinkwithin(T) :- issink(T), !.
sinkwithin(T) :- T =.. [_|Args], somechk(sinkwithin,Args).

sink_or_wfout_within(T) :- \+ compound(T), !, fail.
sink_or_wfout_within(T) :- issink(T), !.	% a sink
sink_or_wfout_within(T) :- iswf(T,_,out), !.	% or an outbound front
sink_or_wfout_within(T) :-
    T =.. [_|Args],
    somechk(sink_or_wfout_within,Args).

all(_,[]).
all(P,[H|T]) :- call(P,H), all(P,T).

% map_on_tree apply predicate to all nodes in tree T
% Can backtrack over Pred
map_on_tree(Pred,T1) :- \+ compound(T1), !, call(Pred, T1).
map_on_tree(Pred,T1) :- 
   T1 =.. ExpT1, maplist(map_on_tree(Pred),ExpT1,_).

map_on_tree(Pred,T1,T2) :- \+ compound(T1), !, call(Pred, T1,T2).
map_on_tree(Pred,T1,T2) :- 
   T1 =.. ExpT1, maplist(map_on_tree(Pred),ExpT1,ExpT2), T2 =.. ExpT2.

% same as above except with 2 functions one for applications to leaves
% within wave-fronts, other within skeleton.  Use flag to toggle cases.  
% NOTE: makes syntactic assumption about names of wave-front/hole functors!
% in/out mean in wave-front or out of wave front

status_tree_map(Op,Ip,T1,T2) :- status_map(out,Op,Ip,T1,T2).

status_map(S,OP,IP,T1,T2) :- \+ compound(T1), !,
 (S == out ->  call(OP, T1,T2); call(IP,T1,T2)).

status_map(S,OP,IP,T1,T2) :-   T1 =.. [H|ExpT1],
 (wave_front_functor(H) -> NS = in; (wave_hole_functor(H) -> NS = out; NS = S)),
 maplist(status_map(NS,OP,IP),ExpT1,ExpT2), T2 =.. [H|ExpT2].

% set product takes a list of sets and returns a set of products

lflatten([],[]).
lflatten([H|T], Flat) :- lflatten(T,TFlat), append(H,TFlat,Flat).

setprod([],[[]]).
setprod([H|T],Out) :-  setprod(T,TOut), setprod(H,TOut,Out).

setprod([], _, []).  % First arg is now a set of elements 
setprod([H|T], L, Product) :-
        maplist(append([H]),L,HL),
        setprod(T,L,Rest),
        append(HL,Rest,Product).

% Talley takes list of list of values and returns list of their pointwise sums
talley([],[]).       
talley([H],[H]).
talley([H1,H2|T],R) :-  talley(H1,H2,O), talley([O|T],R).

talley([],R,R) :- !.
talley(R,[],R) :- !.
talley([H1|T1],[H2|T2],[H3|T3]) :- H3 is H1 + H2, talley(T1,T2,T3).

pair(pair(A,B),A,B).
first(pair(A,_), A).
second(pair(_,B), B).


% Multisets Utilities
% 
% Multisets are represented by unordered lists of the 
% form [El1/N1, .. Eln/Nn] where Eli are the elements
% of the multiset and Ni are the number of occurrences
% of Eli. 

mmember(El/N,M):-   member(El/N,M).
mmember(El/0,M):-  \+member(El/_,M).

munion([],M,M).
munion([El/N1|M],N,[El/N3|P]):-
     mmember(El/N2,N),
     N3 is N2 + N1,
     delete_one_id(N,El/N2,NE),
     munion(M,NE,P).

mseteq([],[]).
mseteq([El/N1|M],N):-
     member(El/N1,N),
     delete_one_id(N,El/N1,NE),
     mseteq(M,NE).

list2mset([],[]).
list2mset([El|L],M):-
     list2mset(L,N),
     munion([El/1],N,M).

list2set([],[]).
list2set([El|L],M):-
     list2set(L,N),
     union([El/1],N,M).

% Universal, Existenial and Conditional meta-predicates

thereis(Var,[Var|_],Pred):-  \+ \+ Pred,!.
thereis(Var,[_|Ls],Pred):- thereis(Var,Ls,Pred).

forall(_,[],_).
forall(Elem,[L|Ls],Pred) :-
    \+ \+ (Elem = L, Pred),
    forall(Elem,Ls,Pred).

if(Test,Then):-
    Test,!,Then.
if(_,_).

sinks_present(V) :- var(V),!,fail.
sinks_present([Sink|_]) :-
    issink(Sink),!.
sinks_present([_|Ts]) :-
    sinks_present(Ts).

member1(X, [Y|_]    ) :- X == Y.
member1(X, [_|L]    ) :- member1(X, L).

/* extract a rule from the pre-recorded rewrite database. */
rewrite_rule(LHS, RHS, Cond, Dir, Rulename,Ref) :-
    rewrite_rule(LHS, RHS, Cond, Dir, _,Rulename,Ref).
rewrite_rule(LHS, RHS, Cond, Dir, O,Rulename,Ref) :-
    rewrite_rule(LHS, RHS, Cond, Dir, _,O,Rulename,Ref).

rewrite_rule(L, R, C, D, TypeInfo, O,Rulename,Ref) :-
    /* this clause treats the L ground mode specially to try to avoid
     the cost of unify/2 (which is significant) */  
    ground(L),!,
    recorded(rewrite,rewrite(L,_, R,_, C, D, TypeInfo, O,Rulename),Ref).

rewrite_rule(LHS, RHS, Cond, Dir, TypeInfo,O,Rulename,Ref) :-
    rewrite_rule(LHS, _,RHS, _,Cond, Dir, TypeInfo,O,Rulename,Ref).

/* as rewrite_rule/7, but extra arguments return labelling */
rewrite_rule(L,Ll, R,Rl, C, D, TypeInfo, O,Rulename,Ref) :-
    recorded(rewrite,rewrite(L1,Ll1, R1,Rl1, C1, D1, TypeInfo1, O,Rulename),Ref),
    unify(rewrite(L1, Ll1, R1, Rl1,C1, D1, TypeInfo1, O,Rulename),
	  rewrite(L, Ll, R, Rl, C, D, TypeInfo, O,Rulename)).

/* See if a term is a rewrite redex */
rewrite_redex(LHS) :-
    rewrite_rule(LHS,_,_,_,_,_).

/* Extract a rule from the pre-recorded rewrite database.  unify/2 is
 * used since LHS may contain multiple occurrences of same variable.
 * LHS is _not_ instantiated. */
rewrite_rule_no_unify(WTTerasure,LHS, RHS, Cond, Dir, TI,Rulename,Ref) :-
    copy_term(WTTerasure-Cond-Dir,LHScopy-CC-DD),
    rewrite_rule(LHScopy,_,CC,DD,_,_,Rulename,Ref),
    rewrite_rule(LHS,RHS,Cond,Dir,TI,_,Rulename,Ref).

/* replace_universal_vars(Vars,Term,NewTerm). Simple loop to replace
 * universally quantified variables. NewTerm is as Term, except that
 * all variables mentioned in Vars (a list with elements Var:Type)
 * will be replaced by meta-(Prolog) variables.  Simply iterates
 * replace_all/4, taking care to deal with lists by ourselves, since
 * they are caught as special (namely as introducing local variables)
 * by s/4 which is used by replace_all/4.  */
replace_universal_vars(Vars,Term,NewTerm) :-
    untype(Vars,Vs,_), zip(VsNewVs,Vs,_),
    replace_universal_vars_1(VsNewVs,Term,NewTerm).
replace_universal_vars_1(_,Tm,Tm) :- var(Tm),!.
replace_universal_vars_1(VsNewVs,[H|T],[HH|TT]) :- !,
    replace_universal_vars_1(VsNewVs,H,HH),
    replace_universal_vars_1(VsNewVs,T,TT).
replace_universal_vars_1(VsNewVs,T1:T2,TT1:TT2) :- !,
    replace_universal_vars_1(VsNewVs,T1-T2,TT1-TT2),!.
replace_universal_vars_1([],In,In).
replace_universal_vars_1([Object-Meta|Vars],In,Out) :- !,
    replace_all(Object,Meta,In,Out1),
    replace_universal_vars_1(Vars,Out1,Out).

%% replace_universal_vars(MLVars,Vars,Term,NewTerm).  
 %% Same as replace_universal_vars/3 but additional argument keeps track of
 %% the meta variables introduced.
replace_universal_vars(MLVars,Vars,Term,NewTerm) :-
    untype(Vars,Vs,_), zip(VsNewVs,Vs,_),
    replace_universal_vars_1(MLVars,VsNewVs,Term,NewTerm).
replace_universal_vars_1(_MLVars,_,Tm,Tm) :- var(Tm),!.
replace_universal_vars_1(MLVars,VsNewVs,[H|T],[HH|TT]) :- !,
    replace_universal_vars_1(MLVars,VsNewVs,H,HH),
    replace_universal_vars_1(MLVars,VsNewVs,T,TT).
replace_universal_vars_1([],[],In,In).
replace_universal_vars_1([Meta|MLVars],[Object-Meta|Vars],In,Out) :- !,
    replace_all(Object,Meta,In,Out1),
    replace_universal_vars_1(MLVars,Vars,Out1,Out).

/*
 * 3. Code for abstracting away the implementation of wave fronts.
 * 
 */

/*
 * The main predicate below, wave_fronts/3, provides a form of 
 * abstract-datatyping for wave-fronts. 
 * 
 * Wave fronts are represented as tags inside a formula: see issink/1 etc.
 *
 * Ideally, I would like to have this all done in one predicate usuable
 * in different modes, but somehow I can't get that to work. At the
 * moment, we do have indeed have one predicate, which forks out into
 * two different (but very similar) pieces of code depending on the
 * call-mode (delete_wave_fronts/3 and insert_wave_fronts/3)
 */

        % wave_fronts(T,L,TT): TT is equal to T
        % except that it has wave-fronts in positions specified by L.
        %
        % The elements of L are of the form 
	%
	%                    FrontPos-TermPosList/[Typ,Dir] 
        %
        % where FrontPos is a list specifying the position of the wave front
        % and TermPosList is a list of positions specifying the wave
        % terms in the wave front. Typ and Dir denote the type (soft/hard)
        % and direction (in/out) of the wave front respectively.
        % NOTE: The positions in TermPosList are relative to FrontPos.
        % EXAMPLE: the following term in underline-notation:
        %       plus(X,B)
        %       ----- - -
        % looks like: 
        %
        %    wave_front(T,D,plus(wave_var(X),wave_var(B))).
        %
        % Pretty-print clauses are provided (via the portray clauses in
        % util.pl). wave_front(T,D,X) terms (the wave-fronts) are printed 
        % as ``X''<T/D>, and wave_var(X) terms (the wave-variables) 
        % are printed as {X}.
        % Thus, the above term would print as ``plus({X},{B})''<T/D>.
        %
        % Different modes of this predicate can than be used for finding
        % wave-fronts (wave_fronts(_,-,+)), deleting wave-fronts (mode
        % wave_fronts(-,+,+)), and inserting wave-fronts (mode
        % wave_fronts(+,+,-)).
        % (In fact, these are the minimally required modes. Thus, either
        % the third or the first and second argument need to be
        % instantiated). 
wave_fronts(T,L,TT) :- \+ var(TT), !, delete_wave_fronts(TT,L,T).
wave_fronts(T,L,TT) :- \+ var(T), \+ var(L), !, insert_wave_fronts(T,L,TT).

        % Following are the auxiliary predicates for wave_fronts/4,
        % All of this code is extremely tedious and boring. It's all of
        % the flavour: iterate over list, recursively descend down
        % terms, and do your thing...
        %
        % delete_wave_fronts(+Term,?List,?Term1): Term1 is like Term
        % except that it has wave-fronts deleted at positions
        % specified in List.
        % delete_wave_fronts/4 does the real work: the second argument
        % keeps track of the current position while recursively
        % descending down the term. If we hit a wave-front we delete it
        % and return the current position and term (after removing the
        % wave-variables). 
delete_wave_fronts(Term,FrontsList,Term1) :-
    delete_wave_fronts(Term,[],FrontsList,Term1).
delete_wave_fronts(T,_,L,T1) :- (atomic(T);var(T)), !, T=T1, L=[].
delete_wave_fronts(WF,L,
		   [L-WVarList/[Typ,Dir]|T1FrontsList],T2) :-
    stripfront(WF,Typ,Dir,T),!, 
    delete_wvars(T,[],WVarList,T1),
        % wave fronts can be nested. The following recursive calls
        % removes nested wave-fronts:
    delete_wave_fronts(T1,L,T1FrontsList,T2).
delete_wave_fronts(SinkT,L,LL,SinkTT):- 
    stripsink(SinkT,T),!,
    issink(SinkTT,TT),
    delete_wave_fronts(T,L,LL,TT).
delete_wave_fronts([H|T],[N|L],Ls,[HH|TT]) :- !,
    delete_wave_fronts(H,[N|L],L1s,HH),
    N1 is N+1,
    delete_wave_fronts(T,[N1|L],L2s,TT),
    append(L1s,L2s,Ls).
delete_wave_fronts(T,Lin,Lout,TT) :-
    T =.. [F|Args],
    delete_wave_fronts(Args,[1|Lin],Lout,Args2),
    TT =.. [F|Args2].
        % delete_wvars/4: auxiliary predicte to delete_wave_fronts. It
        % removes wave-vars in much the same way as
        % delete_wave_fronts/4 removes wave-fronts. 
         % Note the clause to ignore wave-variables that appear within
         % nested wave-fronts.  These latter can appear due to substitutions etc
         % in the planning process.
delete_wvars(T,_,L,T1) :- (atomic(T);var(T)), !, T=T1, L=[].
/* T is assumed non-var in subsequent clauses */
delete_wvars(Hole,L,[L],T) :- iswh(Hole,T),!.
delete_wvars(WF,_, [],WF)  :- iswf(WF),!.
delete_wvars([H|T],[N|L],Ls,[HH|TT]) :- !,
    delete_wvars(H,[N|L],L1s,HH),
    N1 is N+1,
    delete_wvars(T,[N1|L],L2s,TT),
    append(L1s,L2s,Ls).
delete_wvars(T,Lin,Lout,TT) :-
    T =.. [F|Args],
    delete_wvars(Args,[1|Lin],Lout,Args2),
    TT =..[F|Args2].
        % insert_wave_fronts(+Term,+List,?Term1): Term1 is like Term
        % except that is has wave-fronts inserted at positions specified
        % in List.
        % insert_wave_fronts/3 just iterates insert_wave_fronts/4 over
        % the elements of List.
        % insert_wave_fronts/4 does the real work: First insert the
        % wave_var/1 terms as specified (remember that the positions
        % of the wave_var/1s are relative to the position of 
        % wave_front/3), then insert wave_front/3 at the
        % specified position. 
        % 
        % The first clause is normal termination of iteration of the
        % wave-front list, the fourth clause is the normal step-clause,
        % and the second clause catches the special case when wave_front/3
        % term and wave_var/1 term are immediately adjacent. This case is
        % "nonsensical". Such specifications can sometimes be generated
        % by calling code (e.g. in is_a_wave_rule/6), but are just
        % ignored here. Similarly, a wave-front with no wave_vars in
        % it is equally non-sensical, and caught by the third clause.
insert_wave_fronts(Term,[],Term).
insert_wave_fronts(Term,[_-[[]]/_|FrontsList],Term1) :- !,
    insert_wave_fronts(Term,FrontsList,Term1).
%insert_wave_fronts(Term,[_-[]|FrontsList],Term1) :- !,
%   insert_wave_fronts(Term,FrontsList,Term1).
insert_wave_fronts(Term,[Front-WVarList/[Typ,Dir]|FrontsList],Term2) :-
    insert_wave_fronts(Term,Front,WVarList,Typ,Dir,Term1),
    insert_wave_fronts(Term1,FrontsList,Term2).
insert_wave_fronts(Term,FrontPos,VarPosList,Typ,Dir,FrontTerm) :-
    map_list(VarPosList, Relative:=>Absolute,
            append(Relative,FrontPos,Absolute),
            NewVarPosList), 
    insert_wvars(Term,NewVarPosList,VarTerm),
    exp_at(VarTerm,FrontPos,FrontArg),
    iswf(WF,Typ,Dir,FrontArg),			%make wave-front
    replace(FrontPos,WF,VarTerm,FrontTerm).
insert_wvars(Term,[],Term).
insert_wvars(Term,[VarPos|VPs],VarTerm) :-
    exp_at(Term,VarPos,VarArg),
    
    /* THIS NEEDS TO BE RETHOUGHT */

    replace(VarPos,dummy(VarArg),Term,VarTerm1),
    wave_hole_functor(WV),
    replace([0|VarPos],WV,VarTerm1,VarTerm2),
    insert_wvars(VarTerm2,VPs,VarTerm).

/*
 * 4. Code for joining and splitting wave fronts.
 * 
 */

/*
 * These predicates are needed because sometimes we must split wave
 * fronts in order to apply a wave rule. The most obvious example of
 * this occurs in the evenp theorem. After induction, we end up with
 * even(plus(``s(s({x}))''<hard,out>,y)) In order to apply the step rules for
 * plus/2, we need to split up the ``s(s({x}))''<hard/out> wave front into
 * ``s({``s({x})''<hard/out>})''<hard/out>. After rippling the separate 
 * s/1's over the plus,
 * we need to join the wave fronts in the resulting term:
 * even(``s({``s({plus(x,y)})''<hard/out>})''<hard/out>) into 
 * even(``s(s({plus(x,y)}))''<hard/out>)
 * in order to ripple the two s/1's simulataneously over the even/1.
 *
 * It would have been nicer if it had been possible to write all this
 * code using the abstract representation of wave fronts implemented in
 * section 4. above. However, I found this very hard, if not impossible
 * to do. As a result, the code below for splitting/joining wave fronts
 * is written using the implementation of wave fronts in terms of
 * wave_front/3 and wave_var/1 terms.
 * 
 */

        % split_wave_fronts(+Term,?PosList,?SplitTerm):
        % SplitTerm will be as Term, but with a number of complex wave
        % front split into smaller ones. PosList will contain the
        % positions of the wave fronts in Term which were split.
        % 
        % This predicate generates on backtracking all possible splits
        % of all wave fronts.
        %
        % This code deliberately returns the possible splits in a
        % sensible order: it returns the splits in bigger chunks (ie.
        % few splits) before splits in smaller chungs (since this
        % favours wave rules that ripple large wave fronts over wave
        % rules that ripple small wave fronts)).
        %
        % The algorithm for producing the split wave fronts is as follows:
        % (Algorithm design courtesy of Andrew Stevens):
        % 
        %  [1] pick any number of splittable ``...''s, and for any of
        %      these do the following: 
        %  [2] label all terms spanning the {...}'s of the ``...''
        %      picked in [1] 
        %      (that is, not including {...}'s part of other ``...''s,
        %       whether nested in the term picked at [1] or not)
        %      (these terms are exactly those where possible wave front
        %       splits can be introduced)
        %  [3] descend down all the subterms of the ``...'' chosen in [1],
        %      while for each doing the following:
        %      [i]   if un-labelled term, return term
        %      [ii]  if {...}, return term (subsumed by [i])
        %      [iii] if labelled term then do one of the following:
        %            [a] un-label term, and repeat [3] for this term
        %            [b] - change label to {``...''}
        %                  (ie insert new wave front), then 
        %                - remove all labels from subterms, then
        %                - return
        %
        % This algorithm is non-deterministic in two places, namely step
        % [1] and step [3][iii]
split_wave_fronts(In,PosL,Out) :-
        % Step [1]:
    findall(FrontPos-VarPosL-[Typ,Dir]-FTerm,
	    (iswf(WF,Typ,Dir,FTerm),
	     pick_deep_wave_front(In,FrontPos,VarPosL,WF)),
            FrontsTerms),
    subseq(FrontsTerms,[SomeFr|OntsTerms],_),
        % Step [2]-[3]:
    map_list([SomeFr|OntsTerms],
            (FrontPos-VarPosL-TypDir-FTerm):=>(FrontPos-SplitSubTerm),
            split_one_wave_front(FTerm,VarPosL,TypDir,SplitSubTerm),
            FrontPosSplitSubTerms),
        % Do the final replacement into the output term:
    SomeFr = (_-_-[Typ,Dir]-_),
    replace_splits(FrontPosSplitSubTerms,[Typ,Dir],In,Out),
        % and collect the list of locations of split wave fronts:
    zip(FrontPosSplitSubTerms,PosL,_).

        % split_one_wave_front(Term,VarPosL,SplitTerm): implements steps
        % [2]-[3] of the splitting algorithm described above, where Term
        % is the term to be split (i.e. a ``...'' term picked in step
        % [1]), VarPosL is the position list of {...} terms in Term, and
        % SplitTerm is the result of splitting Term. Backtracks to
        % generate all possible splits of Term.
split_one_wave_front(FrontTerm,VarPosL,TypDir,SplitSubTerm) :-
        % Step [2]:
    label_split(FrontTerm,VarPosL,Labelled),
        % Step [3]:
    Labelled=..[F|Args],
    traverse_split(Args,TypDir,SplitArgs),
    SplitSubTerm=..[F|SplitArgs],
        % Disallow input term to be returned (this can happen if we
        % choose [3][iii][a] at each labelled node):
    SplitSubTerm\=FrontTerm.

        % Pick a wave front which is splittable (ie which has a "depth">=1
        % (depth = max. distance from ``...'' to any {...})
pick_deep_wave_front(Term,FrontPos,VarL,FrontTerm) :-
    wave_fronts(_,FrontList,Term),
    member(FrontPos-VarL/_,FrontList),
    Long=[_,_|_], thereis {Long}:member(Long,VarL),
    exp_at(Term,FrontPos,FrontTerm).

        % label_split(Term,PosList,LabelledTerm)
        % Term is as LabelledTerm, except that all subterms in Term
        % spanning those positions specified in PosList are marked with
        % a '@label@'/1 term.
        % This is step [2] of the algorithm described above.
        %
        % label_split/3 just iterates label_1_var/3 for each element of
        % PosList:
label_split(Term,[],Term).
label_split(Term,[VarPos|VarPosL],Labelled) :-
    reverse(VarPos,VarPosR),
    label_1_var(Term,VarPosR,Term1),
    label_split(Term1,VarPosL,Labelled).
        % label_1_var(Term,Pos,Labelled) labels all positions in Term
        % spanning Pos. Take care not to instantiate any possible
        % meta-variables in Term,  which is why we use functorp/1 a lot,
        % rather than relying on (more efficient) unification.
        % clause 1: termination of descend
        % clause 2: skip terms already labelled (can happen with terms
        %           spanning more than one {...})
        % clause 3: do the real work: descend according to
        %           path-expression, and stick label around the arg as
        %           specified in the path-expression, except when there
        %           already is a label, or when the argument is a {...}
        %           term.
label_1_var(T,[],T).
label_1_var(T,[N|P],T1) :-
    functorp(T,'@label@',1), !,
    T='@label@'(TArg),
    label_1_var(TArg,[N|P],T1).
label_1_var(T,[N|P],T1) :-
    T=..[F|Args],
    partition_c([F|Args],N,PreNth,Nth,PostNth),
    label_1_var(Nth,P,Nth1),
    (   functorp(Nth1,'@label@',1)    -> LabelNth=Nth1
     ;  iswh(Nth1) -> LabelNth=Nth1
     ;  LabelNth='@label@'(Nth1)
    ),
    append(PreNth,[LabelNth|PostNth],[F|NewArgs]),
    T1=..[F|NewArgs].

        % Step [3] from the algorithm described above:
        % clause 1: leave variables alone.
        % clause 2: step [3][iii][a]
        % clause 3: step [3][iii][b]
        % clause 4,5: iterate over arg-lists
        % clause 6: step [3][i,ii]
        %
        % The order of clauses 2 and 3 cause splits in large chunks to
        % be computed before small ones. The only real choice between
        % the clauses of this predicate is between 2 and 3, the rest is
        % deterministic. 
traverse_split(Term,_,Term) :- var(Term),!.
traverse_split('@label@'(Term),TypDir,SplitTerm) :-
    Term=..[F|Args],
    traverse_split(Args,TypDir,SplitArgs),
    SplitTerm=..[F|SplitArgs].
traverse_split('@label@'(Term),[Typ,Dir], Hole) :-
    iswh(Hole,WF),
    iswf(WF,Typ,Dir,SplitTerm),
    unlabel_split(Term,SplitTerm),!.
traverse_split([],_,[]) :- !.
traverse_split([H|T],TypDir,[H1|T1]) :- !, traverse_split(H,TypDir,H1),traverse_split(T,TypDir,T1).
traverse_split(Term,_,Term).

        % Traverse a term and removes anything that smells of '@label@'/1.
unlabel_split(Term,Term) :- var(Term),!.
unlabel_split(Term,Term) :- atomic(Term),!.
unlabel_split([],[]) :- !.
unlabel_split([H|T],[H1|T1]) :- !,unlabel_split(H,H1), unlabel_split(T,T1).
unlabel_split('@label@'(Term),Term1) :- unlabel_split(Term,Term1),!.
unlabel_split(Term,Term1) :-
    Term =..[F|Args],
    unlabel_split(Args,NewArgs),
    Term1=..[F|NewArgs],!.

        % Simply iterate replace/4 over the first argument:
replace_splits([],_,T,T).
replace_splits([(Pos-SplitSubTerm)|PosTermL],[Typ,Dir],Term,SplitTerm)
	:-
    iswf(WF,Typ,Dir,SplitSubTerm),
    replace(Pos,WF,Term,Split1Term),
    replace_splits(PosTermL,[Typ,Dir],Split1Term,SplitTerm).

        % join_wave_fronts(+Term,?PosL,?JoinTerm) JoinTerm is as Term,
        % but with a number of meeting wave-fronts joined. The joins
        % live in Term as positions specified in PosL.
        %
        % The algorithm is very simple:
        % [1] pick any number of joinable wave fronts (these are places
        %     that look like {``...''} (i.e  places where one wave front
        %     starts at the place where another one ends).
        % [2] perform the joins at places picked in [1].
        %
        % QUESTION: Why is the algorithm for joining so much simpler
        % than that for splitting?
join_wave_fronts(Term,PosL,JoinTerm) :-
    findall(Pos,pick_a_join(Term,Pos),AllPosL),
    PosL=[_|_],
    subseq(AllPosL,PosL,_),
    do_join_wave_fronts(Term,PosL,JoinTerm).
maximally_joined(Term,JoinTerm) :-
    findall(Pos,pick_a_join(Term,Pos),AllPosL),
    do_join_wave_fronts(Term,AllPosL,JoinTerm),!.
maximally_joined(Term,Term).
    
        % Find a place where wave fronts can be joined, (these are
        % places that look like {``...''} (i.e places where one wave
        % front starts at the place where another one ends).
pick_a_join(Term,[N|Pos]) :-
    exp_at(Term,[N|Pos],Sub1,Sup1),
    join_comps( Sub1, Sup1, Sub,Typb,Dirb,Sup,_Typp,_Dirp ),
    iswh(Hole,WF),
    iswf(WF,Typb,Dirb,Sub),
    arg(N,Sup,Hole).
join_comps( Sub1, Sup1, Sub,Typb,Dirb,Sup,Typp,Dirp) :-
    stripfront(Sub1,Typb,Dirb,Sub),
    ( stripfront(Sup1,Typp,Dirp,Sup) -> true ;
      Sup1=Sup
    ).


        % iterate the predicate that performs one join:
do_join_wave_fronts(Term,[],Term).
do_join_wave_fronts(Term,[Pos|PosL],JoinTerm) :-
    join_1_wave_front(Term,Pos,Join1Term),
    do_join_wave_fronts(Join1Term,PosL,JoinTerm).    

        % perform one join at the specified position. All we have to do
        % is to remove the {``...''} markers at the specified place. 
join_1_wave_front(Term,[N|Pos],JoinTerm) :-
    exp_at(Term,Pos,Sup1),
    (iswf(Sup1,Typ,Dir,Sup) orelse Sup1=Sup),
    Sup =.. [F|Args],
    partition_c([F|Args],N,PreN,Nth,PostN),
    iswh(Nth,WF),
    iswf(WF,Typ,Dir,Sub),
    append(PreN,[Sub|PostN],[F|NewArgs]),
    NSup =.. [F|NewArgs],
    do_join1_wf( Sup1, Sup, NSup1, NSup ),
    replace(Pos,NSup1,Term,JoinTerm).
do_join1_wf( Sup1, Sup, NSup1, NSup ) :-
    iswf(Sup1,Typ,Dir,Sup), !, 
    iswf(NSup1,Typ,Dir,NSup) ; NSup1=NSup.

/*
5.  Code for supporting wave-front rewriting.
*/

%
% This code explicitly uses the internal representation of wave fronts, as
% it cannot be written using wave_fronts/3.
%

      % wave_front_proper( Wave, WaveSansAnnotation )
      % Given a wave-front strip off its outermost annotation
wave_front_proper( WF,BodyWaveFront) :-
    stripfront(WF,_,_,BodyWaveFront).
% Adding by A.Ireland 31/5/91
wave_front_proper( WF,Typ,Dir,BodyWaveFront) :-
    stripfront(WF,Typ,Dir,BodyWaveFront).
      % wave_hole_proper( Hole, HoleSansAnnotation )
      % Given a wave-hole strip off its outermost annotation
wave_hole_proper( T, Hole) :-
    striphole(T,Hole).

/*
 * sink-proper(?T1, ?T2):
 *
 * T1 is identical to T2 except that T1 is enclosed in a sink. 
 * sink-proper/2 can be used to retrieve the contents of a sink 
 * (mode sink-proper(+,-)) or package up a term in a sink 
 * (mode sink-proper(-,+)). Either T1 or T2 must be instantiated.
 */
sink_proper( T,BodySink) :- stripsink(T,BodySink).

      % wave_var_terms( Wave, WaveVars )
      % Given a wave return its wave-variables
wave_var_terms( Tm, WvTms ) :-
        findall( WvTm, wave_var_term(Tm, WvTm), WvTms ).
wave_var_term( WF,  WF) :- iswf(WF,_),!.
wave_var_term(WH,  WH ) :- iswh(WH,_),!.
wave_var_term(Tm, X ) :-
        imm_subterms(Tm,STmL,_),
        member( STm, STmL ),
        wave_var_term( STm, X).

    
/* 
 * modify-wave-ann(+WaveSpec, -NewWaveSpec):
 *
 * WaveSpec is a list of wave-front specifications. NewWaveSpec is a
 * a modified version of WaveSpec which takes into account the cancellation
 * of the outermost constructors.
 *
 * Not very elegant. \notnice A normal form for wave-rules where wave-fronts
 * are be maximal split would remove this problem.
 */
modify_wave_ann([],[]).
modify_wave_ann([[_,1]-[[_]]/_|T],TT):-
                modify_wave_ann(T,TT).
modify_wave_ann([[N,1]-[WV]/TypDir|T],[[N,1]-[NewWV]/TypDir|TT]):-
                reverse(WV,[_|L1]),
                reverse(L1,NewWV),
                modify_wave_ann(T,TT).
modify_wave_ann([WF-WVars/TypDir|T],[NewWF-WVars/TypDir|TT]):-
                reverse(WF,[_,N,_|L1]),
                reverse([1,N|L1],NewWF),
                modify_wave_ann(T,TT).

/*
 * mark-potential-waves(+Goal, -NewGoal):
 *
 * Goal and NewGoal are identical formula except that the
 * existential variables in NewGoal are annotated as 
 * potential wave-fronts.
 * NB.  THIS PREDICATE ONLY DEALS WITH EXISTENTIALS IN THE PREFIX!
 */
mark_potential_waves(G,NewG):-
    matrix(Vars,X:Xtype#TX,G),
    mark_potential_waves(X/Dir,TX,NewTX),!,
    iswf(WF,soft,Dir,X),
    matrix(Vars,WF:Xtype#NewTX,NewG).
mark_potential_waves(G,G).

mark_potential_waves(X/Dir,X,WF) :-
    iswf(WF,soft,Dir,X).
mark_potential_waves(_X/_,T,T):- atomic(T).
mark_potential_waves(X/Dir,[H|T],[HH|TT]):-
 	mark_potential_waves(X/Dir,H,HH),
	mark_potential_waves(X/Dir,T,TT).
mark_potential_waves(X/Dir,T,TT):-
	T =.. [F|Args],
	mark_potential_waves(X/Dir,Args,NewArgs),
	TT =.. [F|NewArgs].

/* D is the name of a definition or theorem, and Thm is the name of a
   theorem; process Thm for use as a rewrite rule having parentage D.
   As many rewrites as possible will be extracted from Thm to be used
   in rippling.  */
add_rewrite_rules(D,Thm) :-
    add_rules(rewrite,D,Thm),
    if(\+ rewrite_rule(_,_,_,_,_,Thm,_),
       clam_warning('No rewrite/wave rules were derived from %t.\n',[Thm])).


/* add_rules(Kind,Origin,Thm) generalize, preprocess and then add the
   rule extracted from Thm.  Origin is the parent of Thm: if it is
   different from Thm is it is assumes that Thm is one of a family of
   definitional equations; if identical to Thm, Thm is
   non-definitional.  */
add_rules(Kind,Origin,Thm) :-
    oyster_problem(Thm,[]==>Goal),
    generalized_equation(Goal,GenGoal),
    matrix(Vars,Matrix,GenGoal),
    poly_type_variables(Vars,TypeVars),
    replace_universal_vars(MVs,Vars,TypeVars-Matrix,MTVs-LiftedGoal),
    /* need to fiddle: map : into - since r_u_v ignores : */
    map_list(Vars,(A:B):=>(A-B),FVars),
    replace_universal_vars(MVs,Vars,FVars,TypeInfo),
    !,
    add_rules(Kind,Origin,Thm,MTVs,TypeInfo,LiftedGoal).

/* Default wrappers for below */
add_rules(Kind,Origin,Thm,LiftedGoal) :-
    add_rules(Kind,Origin,Thm,[],LiftedGoal).
add_rules(Kind,Origin,Thm,TypeVars,LiftedGoal) :-
    add_rules(Kind,Origin,Thm,TypeVars,[],LiftedGoal).    

/* add_rules(+Kind,+Origin,+Thm,+TypeVars,+TypeInfo,+LiftedGoal):
   extract and store conditional rewrite rules from the lifted theorem
   Goal (lifted = universal variables consistently replaced by Prolog
   variables).  Origin traces the 'parentage' of rules extracted from
   eqn's). Rules with no such origin should have Thm==Origin.  We
   insist, since rules will be used in a left-to-right direction, that
   ((FV(r)\cup FV(c))\TypeVars) \subseteq FV(l) for any conditional
   rewrite c=>l=r.  That is, any variable occurring in either the
   condition or the rhs must appear in the lhs, excepting those
   variables in the list TypeVars.  As its name suggests, the expected
   use of this is to allow type-variables to by instantiated by means
   other than that of instantiating the lhs.

   Note that both l-to-r and r-to-l variants are stored in the case of
   Kind==rewrite.  If Kind==reduction, a simplification ordering is
   used to orient. Kind is also use to determine where in the database
   the rules are stored. 

   Backtracking is used to extract multiple rules.
*/

add_rules(Kind,Origin,Thm,TypeVars,TypeInfo,LiftedGoal) :- % equality
    precon_matrix([], C => L = R in Type, LiftedGoal),
    list_to_oyster_conjunction(C,TTC),		% make an Oyster conjunction
    left_and_right_variants(Kind,Origin,Thm, [TTC,L,R],
			    TypeVars,TypeInfo,equ,Type),fail.
add_rules(Kind,Origin,Thm,TypeVars,TypeInfo,LiftedGoal) :- % equivalence
    precon_matrix([], C => L <=> R, LiftedGoal),
    list_to_oyster_conjunction(C,TTC),		% make an Oyster conjunction
    left_and_right_variants(Kind,Origin,Thm, [TTC,L,R],TypeVars,TypeInfo,equiv,_),fail.
add_rules(Kind,Origin,Thm,TypeVars,TypeInfo,LiftedGoal) :- % implications
    precon_matrix([], C => L => R, LiftedGoal),
    list_to_oyster_conjunction(C,TTC),		% make an Oyster conjunction
    left_and_right_variants(Kind,Origin,Thm, [TTC,L,R],TypeVars,TypeInfo,imp,_),fail.
add_rules(_Kind,_Origin,_Thm,_TypeVars,_TypeInfo,_LiftedGoal).

/* Add left-to-right and right-to-left variants, checking for
   well-formedness. Rewrites must have a non-trivial LHS; reduction
   rules must be measure-decreasing.  metavars(RHS) subseteq metavars(LHS) cup FVs

   These rules may be used during labelled rewriting (cf
   reduction.pl); so here we compute the label mapping between the LHS
   and RHS.  In fact, this is trivial: it is simply the partial
   labelling of the RHS, in which all nodes labelled with ticks.
    
   (See comments in reduction.pl).
 */
left_and_right_variants(Kind,Origin,Thm, E, FVs,TypeInfo,Equ,TType) :-
    left_or_right_variant(Kind,Origin,Thm, E, FVs,TypeInfo,Equ,TType),
    fail.
left_and_right_variants(_Kind,_Origin,_Thm, _E, _FVs,_TypeInfo,_Equ,_TType).

left_or_right_variant(rewrite,Origin,Thm, [C,L,R], FVs, TypeInfo,equ,TType) :-
    ((proper_rewrite(FVs,L,C,R), TypeDir =.. [equ,TType,left],  Left = L, Right = R);
     (proper_rewrite(FVs,R,C,L), TypeDir =.. [equ,TType,right], Left = R, Right = L)),
    rule_labelling(Left,Ll,Right,Rl),
    uniq_recorda(rewrite,rewrite(Left,Ll,Right,Rl,C,TypeDir,TypeInfo,Origin,Thm),_),
    lib_writef(23,'Added (=) %t rewrite-record for %t\n',[TypeDir,Thm]),
    plantraced(40,show_rule([Thm,TypeDir,C,Left,Right])).
left_or_right_variant(rewrite,Origin,Thm, [C,L,R], FVs, TypeInfo,Type,_) :-
    \+ (Type = equ),
    ((proper_rewrite(FVs,L,C,R), TypeDir =.. [Type,left],  Left = L, Right = R);
     (proper_rewrite(FVs,R,C,L), TypeDir =.. [Type,right], Left = R, Right = L)),
    rule_labelling(Left,Ll,Right,Rl),
    uniq_recorda(rewrite,rewrite(Left,Ll,Right,Rl,C,TypeDir,TypeInfo,Origin,Thm),_),
    (Type = equiv ->
     lib_writef(23,'Added (<=>) %t rewrite-record for %t\n',[TypeDir,Thm]);
     lib_writef(23,'Added (=>) %t rewrite-record for %t\n',[TypeDir,Thm])),
    plantraced(40,show_rule([Thm,TypeDir,C,Left,Right])).
left_or_right_variant(reduction,Origin,Thm, [C,L,R], FVs,TypeInfo,Type,TType) :-
    once(((Type == equiv,TypeDir = equiv(Dir));
	  (Type == equ,TypeDir = equ(TType,Dir)))),
    once(((Dir = left,
	   Left=L,Right=R,			% left-to-right
	   proper_rewrite(FVs,Left,C,Right),
	   terminating(positive,Left,Right),
	   terminating(negative,Left,Right));
	  (Dir = right,
	   Left=R,Right=L,			% right-to-left
	   proper_rewrite(FVs,Left,C,Right),
	   terminating(positive,Left,Right),
	   terminating(negative,Left,Right)))),
    rule_labelling(Left,Ll,Right,Rl),
    uniq_recorda(reduction,reduction(Left,Ll,Right,Rl,C,TypeDir,TypeInfo,Origin,Thm),_),
    lib_writef(23,'Added (=) %t reduction-record for %t\n',[TypeDir,Thm]),
    plantraced(40,show_rule([Thm,TypeDir,C,Left,Right])).
left_or_right_variant(reduction,Origin,Thm, [C,Left,Right], FVs,TypeInfo,imp,_) :-
    proper_rewrite(FVs,Left,C,Right),
    TypeDir = imp(left),
    terminating(negative,Left,Right),
    rule_labelling(Left,Ll,Right,Rl),
    uniq_recorda(reduction,reduction(Left,Ll,Right,Rl,C,TypeDir,TypeInfo,Origin,Thm),_),
    lib_writef(23,'Added (=>) %t reduction-record for %t\n',[TypeDir,Thm]),
    plantraced(40,show_rule([Thm,TypeDir,C,Left,Right])).
left_or_right_variant(reduction,Origin,Thm, [C,Left,Right], FVs,TypeInfo,imp,_) :-
    proper_rewrite(FVs,Right,C,Left),
    TypeDir = imp(right),
    terminating(positive,Right,Left),
    rule_labelling(Right,Rl,Left,Ll),
    uniq_recorda(reduction,reduction(Right,Rl,Left,Ll,C,TypeDir,TypeInfo,Origin,Thm),_),
    lib_writef(23,'Added (<=) %t reduction-record for %t\n',[TypeDir,Thm]),
    plantraced(40,show_rule([Thm,TypeDir,C,Left,Right])).

/* Checks that a rewrite rule is to be used in a sensible direction.
   C and R are terms whose (meta-level) free variables are a subset of
   the (meta-level) free variables of the term L union those variables
   in FVs.  If L is a var, ensure that C is non-trivial: otherwise the
   rule is obviously non-terminating.  */
proper_rewrite(FVps,Lp,Condsp,Rp) :-
    if(var(Lp),\+ Condsp == []),
    copy(FVps-Lp-Condsp-Rp,FVs-L-Conds-R),
    metavarsinterm(L,FVl), union(FVs,FVl,Vs),
    metavarsinterm(Conds-R,FVr),
    make_ground(Vs-FVr),
    subset(FVr,Vs).

/* TV is a list of those variable declarations appearing in T which
   are declarin polymorphic types, defined by type_delcaration/1.  */
poly_type_variables([],[]).
poly_type_variables([V:T|VTs],[V|Vs]) :-
    poly_type_declaration(V:T),!,
    poly_type_variables(VTs,Vs).
poly_type_variables([_|VTs],Vs) :-
    poly_type_variables(VTs,Vs).    


/* V:T is a polymorphic type declaration.  By this we mean a
   declaration used to introduce a type variable, for example
   t:u(1)=>...x=y in t list.  I wont attempt a formal definition,
   since I'm not sure there is one.  */
poly_type_declaration(_:u(_)).

/* `Generalize' the univerally quantified equational formula E that
   corresponds to the definiton of some function F.  GE is
   equivprobable to E, but if the LHS of the definition of F in E is a
   non-linear constructor pattern the LHS in GE will be linear, and in
   which case additional conditions are introduced to effect
   non-linearity.  If E does not meet these conditions, GE is
   identical to E.  */

generalized_equation(E,GE) :-
    matrix(Vars,M,E),
    precon_matrix([], C => L <=> R, M),
    generalized_cond_rewrite(Vars,C => L <=> R, NewVars,GR),!,
    precon_matrix([], GR, GEE),
    matrix(NewVars,GEE,GE).

generalized_equation(E,GE) :-
    matrix(Vars,M,E),
    precon_matrix([], C => L = R in Type, M),
    generalized_cond_rewrite(Vars,C => L = R in Type, NewVars,GR),!,
    precon_matrix([], GR, GEE),
    matrix(NewVars,GEE,GE).
generalized_equation(E,E).

/* C => L=R is a conditional rewrite, where L is a (possible
   non-linear) constructor term.  CC=>LL=R is a new c.r. in which CC =
   C<>D such that under the assumption D, L is provably equal to LL.
   LL is a linear constructor term.  */

generalized_cond_rewrite(Vars,C => L = R in Type, 
			 NewVars,CC => LL = R in Type) :-
    L =.. [_|Args],
    forall(A,Args,constructor_term(A,Vars)),
    findall(V,freevarinterm(L,V),LVs),		%not a set
    generalized_cond_rewrite(Vars,LVs,[C,L],NewVars,[CC,LL]).
generalized_cond_rewrite(Vars,C => L <=> R, 
			 NewVars,CC => LL <=> R) :-
    L =.. [_|Args],
    forall(A,Args,constructor_term(A,Vars)),
    findall(V,freevarinterm(L,V),LVs),		%not a set
    generalized_cond_rewrite(Vars,LVs,[C,L],NewVars,[CC,LL]).

generalized_cond_rewrite(Vars,LVs,[C,L],Vars,[C,L]) :-
    /* L is okay */
    is_set(LVs),!.

/* L is non-linear.  Why...? */
/* really ought to compute a partition of LVs on == */
generalized_cond_rewrite(Vars,LVs,[C,L],NewVars,[CC,LL]) :-
    /* just worry about non-linear variables; in fact, we only require
       NLVs to count the number of non-linear variables minus 1, since
	one occurrence can be left as-is */
    findall(V,(select(V,LVs,Rest),
	       member(V,Rest)), NLVs),
    generalized_cond_rewrite(Vars,NLVs,[C,L],NewVars,_,[CC,LL]).

/* LVs is a list of variables (each of which is declared in Vars).  T
   is a term containing LVs.  TT is a new term in which some
   occurrences of variables from LVs are replaced with fresh variables
   such that TT is linear in NewVars; CC is of the form C<>(V=Vi) for
   each V in LVs and each fresh variable Vi, such that T and TT are
   provably equal under CC.  As many occurrences of V appearing in LVs
   are replaced as occurrences appearing in T.

    THIS ONLY WORKS ON ALGEBRAIC FIRST-ORDER TERMS! */
generalized_cond_rewrite(Vars,LVs,[C,V], NewVars,Rest,[CC,NV]) :-
    select(V,LVs,Rest),				%V is non-linear, and
    member(V,Rest),!,
    member(V:Vtype,Vars),			%same type
    free([NV],Vars),
    append(Vars,[NV:Vtype],NewVars),
    append(C,[NV=V in Vtype],CC).

generalized_cond_rewrite(Vars,LVs,[C,L],Vars,LVs,[C,L]) :-
    \+ compound(L),!.

generalized_cond_rewrite(Vars,LVs,[C,L],NewVars,NewLVs,[CC,LL]) :-
    L =.. [F|As],
    generalized_cond_rewrite_map(Vars,LVs,[C,As],NewVars,NewLVs,[CC,AAs]),
    LL =.. [F|AAs].

generalized_cond_rewrite_map(Vars,LVs,[C,[]],Vars,LVs,[C,[]]).
generalized_cond_rewrite_map(Vars,LVs,[C,[A|As]],NewVars,NewLVs,[CCC,[AA|AAA]]) :-
    generalized_cond_rewrite(Vars,LVs,[C,A],V1,NV1,[CC,AA]),
    generalized_cond_rewrite_map(V1,NV1,[CC,As],NewVars,NewLVs,[CCC,AAA]).



    
    
    
    



    

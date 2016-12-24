/* -*- Mode: Prolog -*-
 * @(#)$Id: library.pl,v 1.55 2008/05/21 14:14:14 smaill Exp $
 *
 * $Log: library.pl,v $
 * Revision 1.55  2008/05/21 14:14:14  smaill
 * update for sicstus4
 *
 * Revision 1.54  2003/01/22 18:58:35  smaill
 * for DICE
 *
 * Revision 1.53  1999/05/19 15:58:59  julianr
 * Modified library mechanism to produce commuted variants of loaded equations
 * which involve a commutative function, and changed the timing code.
 *
 * Revision 1.52  1999/04/30 14:37:16  img
 * lib-load-dep/3 added
 *
 * Revision 1.51  1999/03/31 13:10:36  img
 * fixed log
 *
 * Revision 1.50  1999/03/31 13:09:16  img
 * red(T,_) -> red(T); typo in lib_writef fixed
 *
 * Revision 1.49  1998/09/16 13:57:42  img
 * is_transitive/2 and quickly_proveable/1 moved (to method_pre).
 *
 * Revision 1.48  1998/08/26 12:33:28  img
 * replace needs/2 with is_needed/2.  this implements the new needs.pl
 * dependancy mechanism in which the clause needs(_,[]) should not be
 * used.  This allows multiple needs.pl across multiple libraries.
 *
 * Revision 1.47  1998/07/27 12:15:17  img
 * Support for . as equation separator. Conditional tracing messages
 *
 * Revision 1.46  1998/06/10 09:35:25  img
 * added lib_delete(eqns(T))
 *
 * Revision 1.45  1998/05/13 13:04:11  img
 * Uniformly access recorded database via predicates, not directly.
 * Format of equations changed from NameN to Name.N.  Attempt to show
 * that binary predicates of the appropriate type are transitive:
 * controlled by 'trans_proving/0'.
 *
 * Revision 1.44  1998/02/17 13:54:51  img
 * record origin of equations
 *
 * Revision 1.43  1998/02/11 12:42:22  img
 * lib_load(redwave()) added; lib_load(eqn()) and lib_load(eqns()) distinguished
 *
 * Revision 1.42  1997/11/14 16:28:30  img
 * *** empty log message ***
 *
 * Revision 1.41  1997/11/14 12:23:56  img
 * reorded clauses in lib_save and lib_load
 *
 * Revision 1.40  1997/11/14 12:21:24  img
 * reorded clauses in lib_save and lib_load
 *
 * Revision 1.39  1997/11/11 17:25:17  img
 * typo
 *
 * Revision 1.38  1997/11/08 12:27:22  img
 * cosmetic changes
 *
 * Revision 1.36  1997/10/09 17:02:15  img
 * lib_fname_exists/3: added lib_fname/2
 *
 * Revision 1.35  1997/09/26 15:05:05  img
 * general bug fixes; lib_load(scheme) calls add_induction_scheme/1
 *
 * Revision 1.34  1997/07/09 15:29:31  img
 * Alter format of registry in trs object for inequalities.  Extend
 * uniq_recorda for scheme objects (incomplete).
 *
 * Revision 1.33  1997/06/17 14:40:39  img
 * Pass registry explicitly.
 *
 * Revision 1.32  1997/06/05 10:47:56  img
 * uniq_recorda: added clause for schemes; lib_present: eqn's are present
 * if rewrite rules are present; lib_delete: don't require presence of
 * def when trying to remove eqn's.
 *
 * Revision 1.31  1997/04/07 11:46:07  img
 * Improve user interface on lib_set/1.
 *
 * Revision 1.30  1997/01/14 10:45:20  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.29  1996/12/17 18:45:54  img
 * typo.
 *
 * Revision 1.28  1996/12/12 13:25:11  img
 * Typo.
 *
 * Revision 1.27  1996/12/12 12:41:58  img
 * Error message stuff.
 *
 * Revision 1.26  1996/12/06 14:36:54  img
 * lib_save(plan(.)) added.  Timing info added to proof-plan object.
 *
 * Revision 1.25  1996/12/04 12:49:16  img
 * Check that a rewrite rule is added if one was called for.  proof_plan
 * object has extra argument for CPU time. Don't fail if there are no
 * eqn's to save when saving a def. Don't attempt to save individual
 * equations---need more effort here. lib_fname_exists/3: new clause to
 * deal with '*'.
 *
 * Revision 1.24  1996/07/09 15:00:10  img
 * lib_save(thm(.)): give oyster_version/1 and the statement of the
 * conjecture in the plan object written to the library.
 *
 * Revision 1.23  1996/07/05  10:23:54  img
 * Alert user when a theorem is loaded which is not "complete".
 *
 * Revision 1.22  1996/06/18  17:21:11  img
 * lib_save(eqn()): allow numbered equations to be saved.  Cosmetic
 * changes.
 *
 * Revision 1.21  1996/06/12  12:47:38  img
 * singletons are sometimes called valerie
 *
 * Revision 1.20  1996/06/11  16:44:01  img
 * moved much of the reduction rule stuff to add_rule/_; changes to the
 * library mechanism to deal with trs library objects and reduction rules
 * in uniq_recorda/_
 *
 * Revision 1.19  1996/05/24  10:01:10  img
 * Preliminary support for trs logical object: to load and save rewriting
 * systems.  lib_delete: fewer cases are mapped into delete(anythm).
 * special clauses for wave, red and plan allow the user to remove a wave
 * rule without removing (say) associated reduction rules.  All eqn's are
 * stored as reduction rules: hence, there are no func_defeqn anymore.
 * Things loaded as wave are not added as red.  Labelled term rewriting
 * support.
 *
 * Revision 1.18  1995/11/28  16:17:38  img
 * delete complementary sets when theorem on which they are based is deleted
 *
 * Revision 1.17  1995/10/24  14:53:06  img
 * removed old parsing code
 *
 * Revision 1.16  1995/10/18  12:14:29  img
 * lib_load(eqn...) extended to allow individual equations to be added
 *
 * Revision 1.15  1995/10/03  13:10:14  img
 * logical object "plan" added;  lib_save(plan(.)) added;  uniq_recorda
 * added;  library search  path added;  complementary sets recorded at
 * load-time.
 *
 * Revision 1.14  1995/07/31  12:05:07  img
 * uniq_recorda no longer tries to delete rewrite records, since it
 * cannot do so reliably;  use lib_present not Oyster
 *
 * Revision 1.13  1995/07/19  14:23:10  img
 * lib_error gives brief documentation (via logical_object/3);  deletion
 * of definitions debugged.
 *
 * Revision 1.12  1995/07/19  11:18:06  img
 * added lib-create/[1;2];  fixed bugs in lib-save(def(O))
 *
 * Revision 1.11  1995/07/18  18:15:32  img
 * eqns are no longer parsed as wave-rules
 *
 * Revision 1.10  1995/07/17  15:48:31  img
 * Removed fixed limit of 20 equations in lib_load and lib_save eqn(D).
 * Now loads and saves as many as can be found _provided_ they are
 * consecutively numbered.
 *
 * Revision 1.9  1995/05/17  02:18:58  img
 *      * Conditional multifile declaration (for Quintus).
 *
 * Revision 1.8  1995/03/01  04:15:22  img
 *      * Added file_version/1 and associated multifile declaration
 *
 * Revision 1.7  1995/03/01  03:47:01  img
 *      * Redundant call to add_recursive_clause/1 removed;
 *        lib_delete adjusted
 *
 * Revision 1.6  1995/02/14  03:16:01  img
 *      * deleted redundant add_complementary_eqns
 *
 * Revision 1.5  1995/02/14  02:51:56  img
 *      * stuff to do with gazing removed
 *
 * Revision 1.4  1994/09/22  10:12:21  dream
 *      * removed spurious tryto in add_wave_rules_list
 *      * undid some of the previous changes (re. rewrite rule
 *        database) and moved them to wave_rules.pl
 *
 * Revision 1.3  1994/09/22  00:13:52  dream
 *      * added recorda record for the new class of things "rewrite" these
 *        are all the theorems which can be used as wave-rules by the
 *        dynamic wave-rule parser (cf. wave_rules.pl)
 *
 * Revision 1.2  1994/09/16  10:53:41  dream
 *      * made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: library.pl,v 1.55 2008/05/21 14:14:14 smaill Exp $').

/*
 * This file contains a primitive library mechanism which can be used to
 * keep track of dependencies between logical objects such as
 * definitions, theorems, lemma's etc.
 *
 * Main predicates defined in this file are
 *      lib_load/[1;2;3]
 *      lib_save/[1;2]
 *      lib_delete/1
 *      lib_present/1
 *      lib_edit/[1;2]
 *      lib_set/1
 *      lib_tidy/0
 *      needed/2
 */


        % lib_load(+Thing) will load object Thing, plus all other
        % objects needed by Thing which are not already loaded.
        %
        % Thing can be:
        % - mthd(M): M is of the form F/A and specifies a method with
        %   functor F of arity A.
        % - smthd(M): M is of the form F/A and specifies a submethod with
        %   functor F of arity A.
        %
logical_object(thm(T),'%t is a theorem',[T]).
logical_object(lemma(T),
        '%t is a lemma which is only needed for technical\
        reasons, and is not interesting as a thm in its own right.\
        Thus, if %t is both an interesting theorem in its own right\
        but can also be used as a lemma, it is a thm, not a lemma.\
        Consequently the only things that should be lemmas are thms\
        needed for \"technical\" reasons (ie to beef up arithmetic or so).',[T,T]).
logical_object(wave(T),
               '%t is a thm, but is needed in its role as a wave rule',[T]).
logical_object(synth(T),
               '%t is a theorem only used to synthesise a particular\
        function.  In this sense, synths are close to def\'s.',[T]).

logical_object(scheme(T),
               '%t is an induction scheme.',[T]).
logical_object(def(T),'%t is a definition.  Loading def(%t) will also result\
        in loading all consecutively numbered eqn''s of the form Dn, with\
        n=1... These are expected to be the recursion equations for %t.',[T,T,T]).
logical_object(eqn(T),'%t is a theorem, used as a recursion equation for def(%t).',
               [T,T]).
logical_object(red(T),'%t is a reduction rule.',[T]).
logical_object(mthd(M/A),'Specifies a method with functor %t of arity %t.',
               [M,A]).
logical_object(smthd(M/A),'Specifies a submethod with functor %t of arity %t.',
               [M,A]).
logical_object(hint(M/A),'Specifies a hint with functor %t of arity %t.',
               [M,A]).
logical_object(plan(T),'(Saving only) Specifies a proof-plan of theorem %t.',
               [T]).
logical_object(trs(T),'(Cannot be loaded or saved) Specifies a TRS labelled %t.',
               [T]).
logical_object(redwave(T),'(Loading only) An abbreviation for both red(%t) and wave(%t).',
               [T]).
/* The corresponding files are expected to be in directories thm,
 * lemma, synth, scheme, def, mthd and smthd.  Apart from loading the
 * Oyster representation of theorems, defs, etc., we maintain our own
 * storage mechanism which is partly much more efficient than Oysters
 * and partly so that we can cache often re-computed results.  This is
 * all done in the recorded database under the keys rewrite, wave,
 * theorem and reduction.
 *
 * Dependancies between objects are expected to stored in needs/2
 * clauses such as
 *   needs(thm(assm), [def(times)]).
 *   needs(def(times),[def(plus)]).
 *
 * The real work is done by lib_load/2, which as a second argument
 * takes the directory path from which the stuff is to be loaded.  If
 * not given it defaults to the value specified by lib_dir/1.  For
 * methods, the arguments are slightly different: second argument is
 * position-in-database (one of {first,last,before(_),after(_)}) or
 * mthd-file to read methods from.  Both arguments can also be given
 * via lib_load/3.  The real work for (sub)methods is done by
 * load_mthd in method-db.pl.  */

/* load lists of things */
lib_load([]) :- !.
lib_load([H|T]):- !, lib_load(H),lib_load(T).

lib_load(mthd(M/A))  :- !, load_method(M/A).
lib_load(smthd(M/A)) :- !, load_submethod(M/A).
lib_load(hint(M/A)) :- !, load_hint(M/A).
lib_load(Thm) :- lib_dir(LibDir), lib_load(Thm,LibDir).

lib_load([],_):- !.
lib_load([H|T],Arg2) :- !, lib_load(H,Arg2), lib_load(T,Arg2).

lib_load(mthd(M/A),Arg2) :- !, load_method(M/A,Arg2).
lib_load(smthd(M/A),Arg2) :- !, load_submethod(M/A,Arg2).
lib_load(hint(M/A),Arg2) :- !, load_hint(M/A,Arg2).
%lib_load(rtype(N),Arg2) :- !,load_rectype(N,Arg2).
lib_load(synth(T),Dir) :- !, lib_load(anythm(T,synth),Dir).
lib_load(lemma(T),Dir) :- !, lib_load(anythm(T,lemma),Dir).
lib_load(thm(T),Dir)   :- !, lib_load(anythm(T,thm),Dir).
lib_load(scheme(T),Dir):- !,
    lib_load(anythm(T,scheme),Dir),
    add_induction_scheme(T).

lib_load(plan(T),Path) :- !,
    (lib_fname_exists(Path,_Dir,T,plan,File) ->true;
     clam_user_error('There is no plan(%t) in the library path: %t\n',
                     [T,Path]),fail),
    (lib_present(thm(T)) -> true;
     clam_user_error('Please load thm(%t) before loading the plan.',[T]),fail),
    readfile(File,proof_plan(H==>G,T,TimeTaken,P,Planner)),
    uniq_recorda(proof_plan,proof_plan(H==>G,T,TimeTaken,P,Planner),_),
    lib_writef(23,'Loaded plan(%t)\n', [T]).


/* EXPERIMENTAL: load a known terminating rewrite system.  There can
   only be one such system loaded at a given time.  */
lib_load(trs(TRS),Path) :- !,
    TRS = default,
    write('lib_load(trs(.)) is not yet implemented.'),nl,fail,
    (lib_fname_exists(Path,_Dir,TRS,trs,_File) -> true;
     clam_user_error('There is no trs(%t) in the library path: %t\n',
                     [TRS,Path]),fail),
    lib_writef(23,'Loaded trs(%t)\n',[TRS]),
    %% read_from_file(File,Term),
    %% record Term in the database
    true.
lib_load(def({D}),Path) :-
    !,lib_load(def(D),Path).
lib_load(def(D),Path) :-
   \+ is_list(D),!,
    is_needed(def(D),Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Path)),!,
    (lib_fname_exists(Path, Dir,D,'synth', _)
      -> lib_load(synth(D),[Dir])
      ;  true),
    (lib_fname_exists( Path, _, D,'def',File) -> true;
     clam_user_error('There is no def(%t) in the library path: %t\n',
                     [D,Path]),fail),
    create_def(File),!,
    lib_load(eqns(D),Path),                     % load any recursion equations
    lib_writef(23,'Loaded def(%t)\n',[D]),
%
% Add commuted versions of any defining equations.
%
    if((comm_proving,binary_function_on_type(def(D),DomC)),
       (clam_info('Definition def(%t) has the type of a binary function.\n',[D]),
       clam_info('Trying to show it is commutative.\n',[]),
        (is_commutative(def(D),DomC) ->
         clam_info('Proved def(%t) to be commutative.\n',[D]),
         clam_info('Adding commuted versions of wave rules.\n',[]),
         add_commuted_equations(def(D))
             ;   clam_info('Failed to prove def(%t) commutative.\n',[D])))),

    if((trans_proving,binary_relation_on_type(def(D),Dom)),
       (clam_info('Definition def(%t) has the type of a transitive relation.\n',[D]),
        clam_info('Trying to show it is indeed transitive.\n',[]),
        (is_transitive(def(D),Dom) ->
         clam_info('Proved def(%t) to be transitive.\n',[D])
             ;   clam_info('Failed to prove def(%t) transitive.\n',[D])))).

        % LOADING EQNs
        % Find out if there are any recursion equations for definition D
        % and call lib_load(anythm(..,eqn)) for each of them. Also, try
        % installing the wave/5 record for those equations to which
        % that applies.
lib_load(eqns(D),Path) :- !,
    lib_load_aux(D,Path,_Dir,DRootList,1),
    if(\+ DRootList = [],
       (add_rewrite_rules_list(D,DRootList),
        add_complementary_sets(DRootList),
        add_reduction_rules_list(D,DRootList))).

lib_load(eqn(_),_) :- !,
    clam_user_error('Loading individual equations requires the name of the definiton this equation helps define.  E.g., lib_load(eqn(plus,plus2))',[]),
    fail.

lib_load(eqn(Origin,D),Path) :- !,              % load a single specified eqn
    lib_load(anythm(D,eqn),Path),
    add_rewrite_rules(Origin,D),
    add_reduction_rules(Origin,D),
    clam_warning(
        'Loading a single equation will not update any complementary rewrite sets.'),
    clam_warning(
        'You must re-load the entire definition to build these.').

lib_load(redwave(T),Dir) :-
    lib_load(red(T),Dir),
    lib_load(wave(T),Dir).

        % LOADING WAVEs
        % Firstly deal with the case where condition sets are
        % specified by the user using the wave([r1,..,rn]) notation.
lib_load(wave(Tlist),Dir) :-
    is_list(Tlist),!,
    lib_load_list(thm(Tlist),Dir),
    add_rewrite_rules_list(Tlist),
    add_complementary_sets(Tlist).

        % Secondly deal with the case where a single wave rule
        % is supplied.
lib_load(wave(T),Dir) :- !,
    lib_load(thm(T),Dir),
    add_rewrite_rules(T,T),
    add_cancel_rule(T).


/* Loading reduction rules: First load T as a thm and then add the
   reduction rule.  */
lib_load(red([]),_Dir).
lib_load(red([T|Ts]),Dir) :-
    lib_load(red(T),Dir),
    lib_load(red(Ts),Dir).
lib_load(red(T),Dir) :-
    !,
    lib_load(thm(T),Dir),
    add_reduction_rules(T,T).

/* LOADING THMs
 * Deals with synth, lemma, thm, scheme and eqn.  Load thing from file
 * and store the theorem/4 record which we use as our own theorem
 * represention (in preference to Oyster's representations).
 *
 * If Thm is a list of things, load each of them, in the same way.
 */
lib_load(anythm(ThmList,Type),Path) :-
    is_list(ThmList),!,
    map_list(ThmList, Thm :=> nothing,
             (lib_load(anythm(Thm,Type),Path)->true;
              writef('Clam warning: failed to load %t(%t)\n',[Type,Thm])),_),
    !.
lib_load(anythm(Thm,Type),Path) :- !,
    TypeThm =.. [Type,Thm],
    is_needed(TypeThm,Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Path)),!,
    (lib_fname_exists(Path,_Dir,Thm,Type,File) -> true;
     clam_user_error('There is no %t(%t) in the library path: %t\n',
                     [Type,Thm,Path]),fail),
    load_thm(Thm,File,Status),
    record_thm( Thm, Type ),
    lib_writef(23,'Loaded %t(%t)\n',[Type,Thm]),
    if(\+ Status == complete,
       plantraced(23,clam_warning('Theorem %t has status %t\n',[Thm,Status]))).

        % report error in case of failure.
lib_load(T,_) :- lib_error(T).

/* Load as many _consecutively_ indexed equations as can be found
 * There is a choice as to whether all equations should be loaded from
 * the same directory (i.e., disregarding other directories in the
 * Path.  For the moment, I choose the least liberal, that is, looking
 * for the first equation in the Path and then loading all subsequent
 * eqns from that same directory.  */
lib_load_aux(D,Path,Dir,[Root|DRootList], N) :-
    var(Dir),                                   %still to find an eqn
    indexed_equation_name(D,N,Root),
    lib_fname_exists(Path,Dir,Root,'eqn',_),!,
    lib_load(anythm(Root,eqn),[Dir]),
    M is N + 1,
    lib_load_aux(D,Path,Dir,DRootList, M).
lib_load_aux(D,Path,Dir,[Root|DRootList], N) :-
    \+var(Dir),                                 % continue with the
                                                % same Dir
    indexed_equation_name(D,N,Root),
    lib_fname_exists([Dir],_,Root,'eqn',_),!,
    lib_load(anythm(Root,eqn),[Dir]),           %force same Dir
    M is N + 1,
    lib_load_aux(D,Path,Dir,DRootList, M).
lib_load_aux(_D,_Path,_Dir,[], _M) :- !.

        % CODE for lib_load/3 only useful for methods:
lib_load([],_,_).
lib_load([H|T],Where,File) :- lib_load(H,Where,File), lib_load(T,Where,File).
lib_load(mthd(M),Where,File)  :- !, load_method(M,Where,File).
lib_load(smthd(M),Where,File) :- !, load_submethod(M,Where,File).
lib_load(hint(M),Where,File) :- !, load_hint(M,Where,File).
lib_load(T,_,_) :- lib_error(T).

record_thm( Thm, Type ) :-
    oyster_problem(Thm,_==>Goal),
    (Type=eqn
     ->( name(Thm,NameNum),
         append(NameL,[_Num],NameNum),
         name(Name,NameL)
       )
     ;
     Name=Thm
    ),
    uniq_recorda(theorem,theorem(Name,Type,Goal,Thm),_),
    !.

lib_load_list(thm([]),_).
lib_load_list(thm([H|T]),Dir) :-
    lib_load(thm(H),Dir),
    lib_load_list(thm(T),Dir).
add_rewrite_rules_list(_,[]).
add_rewrite_rules_list(D,[H|T] ) :-
    add_rewrite_rules(D,H),
    add_rewrite_rules_list(D,T).
add_rewrite_rules_list([]).
add_rewrite_rules_list([H|T] ) :-
    add_rewrite_rules(H,H),
    add_rewrite_rules_list(T).

/* pre-compute complementary set information for groups of
 * wave-rules/equations as they are loaded, and store them in the
 * recorded database.  One expects methods to access complementary
 * sets via this pre-computed form, rather than via
 * complementary_set/1 or complementary_sets/1 because it will be
 * faster; however, note that computing the set dynamically is more
 * powerful since the entire database is used when finding
 * complementary rewrites.  */
add_complementary_sets(Thms) :-
    complementary_set(Thms,CS),
    uniq_recorda(comp_set,comp_set(Thms,CS),_),
    lib_writef(23,'Added complementary set record for %t\n', [Thms]),
    !.
add_complementary_sets(_).

lib_tidy :-
    recorded(comp_set,_,R),
    erase(R),
    fail.
lib_tidy.

        % lib_save(Thing, Dir) saves Thing in directory Dir in files
        % with the appropriate suffix.
        %
        % lib_save(Thing) is as lib_save/2, with Dir defaulting to the
        % current dir:
/* load lists of things */
lib_save([]) :- !.
lib_save([H|T]):- !, lib_save(H),lib_save(T).

lib_save(Thing) :- lib_sdir(D),lib_save(Thing, D).
lib_save([],_):- !.
lib_save([H|T],Arg2) :- !, lib_save(H,Arg2), lib_save(T,Arg2).
lib_save(Thing,_) :-
    Thing =.. [_,[]],
    !.
lib_save(Thing,Path) :-
    Thing =.. [Type,[O|Os]],!,
    OneThing =.. [Type,O],
    lib_save(OneThing,Path),
    RestThing =.. [Type,Os],
    lib_save(RestThing,Path).

lib_save(thm(T), Dir) :- !, lib_save(anythm(T,thm),Dir).
lib_save(lemma(T), Dir) :- !, lib_save(anythm(T,lemma),Dir).
lib_save(scheme(T), Dir) :- !, lib_save(anythm(T,scheme),Dir).
lib_save(synth(T), Dir) :- !, lib_save(anythm(T,synth),Dir).
lib_save(wave(T), Dir) :- !, lib_save(anythm(T,thm),Dir).
lib_save(red(T), Dir) :- !, lib_save(anythm(T,thm),Dir).

/* EXPERIMENTAL: save a known terminating rewrite system.  There can
   only be one such system loaded at a given time.  */
lib_save(trs(TRS),Dir) :- !,
    TRS = default,
    write('lib_save(trs(.)) is not yet implemented.'),nl,fail,
    lib_fname_exists(_Path,Dir,TRS,trs,_File),
    lib_writef(23,'Saved trs(%t)\n',[TRS]),
    %% read_from_file(File,Term),
    %% record Term in the database
    true.

lib_save(plan(T),Dir) :-
    recorded(proof_plan,proof_plan(H==>G,T,TimeTaken,P,Planner),_),!,
    lib_fname(Dir,T,'plan',File),
    clam_version(CV),
    oyster_version(OV),
    (tell(File) -> true;
     (clam_user_error('Unable to save plan(%t) to %t\n',[T,File]),fail)),
    write('/*  This is a proof plan for theorem:'),nl,
    writef('    %t: %t\n',[T,H==>G]),
    writef('    planner = %t, clam_version(%t), oyster_version(%t)\n',[Planner,CV,OV]),
    writef('\n    Time taken to find plan: %tms\n    Environment:\n',[TimeTaken]),
    findall(X,(lib_present(X), \+ X=plan(_)),Xs),
    prlist(Xs),
    writef(' */\n'),
    nl,
    %% and it is nice to see the pretty-printed one there too
    writef('/* This is the pretty-printed form\n'),
    print_plan(P),nl,
    writef('*/\n'),
    nl,
    writeq(proof_plan(H==>G,T,TimeTaken,P,Planner)),write('.'),nl,
    told,
    lib_writef(23,'Saved currently stored plan for %t\n',[T]).

lib_save(plan(T),_Dir) :-
    writef('There is no proof-plan for theorem %t currently stored.\n',[T]),!.

        % lib_save anythm in appropriate file
lib_save(anythm(T,Type),Dir) :- !,
    lib_fname(Dir,T,Type,File),
    (save_thm(T,File) -> true;
     (clam_user_error('Unable to save %t(%t) to %t\n',[Type,T,Dir]),fail)),
    lib_writef(23,'Saved %t(%t)\n',[Type,T]).
        % For saving definitions we first save the def (easy), and then
        % save all the eqns for that def.
lib_save(def(D),Dir) :- !,
    definition(D/_<==>_),
    lib_fname(Dir,D,'def',File),
    (save_def(D,File)  -> true;
     (clam_user_error('Unable to save def(%t) to %t\n',[D,Dir]),fail)),
    lib_writef(23,'Saved def(%t)\n',[D]),
    ( lib_present( synth(D) ) -> lib_save( synth(D), Dir ) ; true ),
    tryto lib_save(eqns(D),Dir).                % there may be some equations

lib_save(defeqn(D),Dir) :- !,
    lib_save(def(D),Dir),
    lib_writef(23,'Registering these definitions...',[]),nl,
    lib_load(def(D),Dir).

/* Pick up all thms that could be eqns for def(D), and save them. */
lib_save(eqns(D),Dir) :-
    lib_save_aux(D,Dir,1,Flag),
    Flag == saved,!.
/* The following is buggy; need to check that D really is an equation */
lib_save(eqn(D),Dir) :-
    oyster_problem(D,_),
    lib_save(anythm(D,eqn),Dir),!.

lib_save(mthd(_),_)  :- !,clam_warning('Cannot save methods (yet)\n').
lib_save(smthd(_),_) :- !,clam_warning('Cannot save methods (yet)\n').
lib_save(hint(_),_)  :- !,clam_warning('Cannot save hints (yet)\n').
lib_save(T,_) :- lib_error(T).

lib_save_aux(D,Dir,N,saved) :-
    indexed_equation_name(D,N, Eqn),
    oyster_problem(Eqn,_),!,
    lib_save(anythm(Eqn,eqn),Dir),
    M is N + 1,
    lib_save_aux(D,Dir,M,_).

lib_save_aux(_D,_Dir,_N,_).

/* lib_present(?Object) succeeds if Object is present in the current
 * environment.  Can be used to test for presence, or to generate the
 * entire contents of the currently loaded library if you feel like
 * it.  The order of the clauses below is significant: Defs create
 * eqns and eqns create thms, so the order is def;eqn;thm. This is so
 * that lib_delete(_) can use this predicate to generate the library
 * in a decent order for deleting things.  */
/* load lists of things */
lib_present(def(T)) :- definition(T/_<==>_).
lib_present(eqn(T)) :-
    recorded(theorem,theorem(_,eqn,_,T),_);
    rewrite_rule(_,_,_,_,T,_).
lib_present(wave(T)) :-                         % a wave-rule is a rewrite
    rewrite_rule(_,_,_,_,T,_).
lib_present(red(T)) :- reduction_rule(_,_,_,_,T,_).
lib_present(trs(default)) :-
    once((recorded(registry,registry(positive,_Tau,_Prec),_);
          recorded(registry,registry(negative,_Tau,_Prec),_))).
lib_present(cancel(T)) :- recorded(cancel,cancel(_,T:_),_).
lib_present(thm(T)) :- recorded(theorem,theorem(T,thm,_,_),_).
lib_present(lemma(T)) :- recorded(theorem,theorem(T,lemma,_,_),_).
lib_present(synth(T)) :- recorded(theorem,theorem(T,synth,_,_),_).
lib_present(scheme(T)) :- recorded(theorem,theorem(T,scheme,_,_),_).
lib_present(mthd(M)) :- list_methods(L), remove_dups(L,L1),member(M,L1).
lib_present(smthd(M)) :- list_submethods(L), remove_dups(L,L1),member(M,L1).
lib_present(hint(M)) :- list_hints(L), remove_dups(L,L1),member(M,L1).
lib_present(plan(T)) :- recorded(proof_plan,proof_plan(_,T,_,_,_),_).
lib_present(T) :-
    \+ var(T), T\==[], \+ functorp(T,.,2),\+ logical_object(T,_,_), lib_error(T).

        % lib_present prints out all objects currently in the library.
lib_present :- lib_present(O), write(O), nl, fail.
lib_present.

        % lib_delete(?Object) removes Object from the current
        % environment. Fails if Object is not present in the current
        % environment.
        % First clause makes that we can use mode lib_delete(_), which,
        % on backtracking, will delete the whole library.
lib_delete(Object) :- var(Object), !, lib_present(Object),lib_delete(Object).
lib_delete(Object) :-
    \+ var(Object),
    \+ functorp(Object,anythm,2), Object\==[], \+ functorp(Object,.,2),
    \+ logical_object(Object,_,_),
    !,lib_error(Object).
lib_delete(Object) :-
    logical_object(Object,_,_),
    \+ (Object=anythm(_,_); lib_present(Object)),
    lib_writef(24,'CLaM WARNING: %t not present, so cannot be deleted\n',[Object]),
    !,fail.
/* remove any existing registries, and make a fresh start with this
   base registry.  */

lib_delete(trs(default)) :-
    lib_present(trs(default)),
    if(lib_present(red(_)),lib_delete(red(_))),
    %% The default TRS is defined by two registries
    if(recorded(registry,registry(positive,_,_),Ref1), erase(Ref1)),
    if(recorded(registry,registry(negative,_,_),Ref2), erase(Ref2)),
    lib_writef(23,'Deleted trs(%t)\n',[default]).


lib_delete(thm(T)) :- lib_delete(anythm(T,thm)).
lib_delete(lemma(T)) :- lib_delete(anythm(T,lemma)).
lib_delete(wave(T)) :-
    findall(Ref,
            (rewrite_rule(_,_,_,_,T,Ref),
             erase(Ref),
             lib_writef(23,'Deleted rewrite/wave record for %t\n',[T])
            ),_),
    findall(Ref,
            (recorded(cancel,cancel(_,T:_),Ref),
             erase(Ref),
             lib_writef(23,'Deleted cancel record for %t\n',[T])
            ),_).
lib_delete(eqn(T)) :- lib_present(eqn(T)), lib_delete(anythm(T,eqn)).
lib_delete(eqns(T)) :- lib_delete_aux(T,1).
lib_delete(red(T)) :-
    findall(Ref,
            (reduction_rule(_,_,_,_,T,Ref),
             erase(Ref), lib_writef(23,'Deleted reduction record for %t\n',[T])
            ),_).
lib_delete(synth(T)) :-
    lib_present(synth(T)),
    lib_delete(anythm(T,synth)).
lib_delete(scheme(T)) :-
    lib_present(scheme(T)),
    findall(_,(recorded(scheme,scheme(T,_,_),Ref),erase(Ref)),_),
    lib_delete(anythm(T,scheme)).
        % anythm case does most work: delete theorem-, rewrite and
        % delete thm itself.
lib_delete(plan(T)) :-
    findall(Ref,
            (recorded(proof_plan,proof_plan(_,T,_,_,_),Ref),
             erase(Ref),
             lib_writef(23,'Deleted proof-plan record for %t\n',[T])
            ),_).
lib_delete(anythm(T,Type)) :-
    findall(Ref,
            %% remove any complementary sets mentioning T
            (recorded(comp_set,comp_set(Thms,_CS),Ref),
             member(T,Thms), erase(Ref),
             lib_writef(23,'Deleted complementary set record for %t\n',[Thms])
            ),_),
    if(lib_present(wave(T)),lib_delete(wave(T))),
    findall(Ref,
            (recorded(cancel,cancel(_,T:_),Ref),
             erase(Ref), lib_writef(23,'Deleted cancel record for %t\n',[T])
            ),_),
    if(lib_present(red(T)),lib_delete(red(T))),
    findall(Ref,
            (recorded(theorem,theorem(_,_,_,T),Ref),
             erase(Ref),
             lib_writef(23,'Deleted theorem record for %t\n',[T])
            ),_),
    ctheorem(T) := _ , lib_writef(23,'Deleted %t(%t)\n',[Type,T]).

        % For def's, for recursive definitions, we delete recursive
        % record, pick up all the equations and delete them, and finally
        % we delete def itself.
lib_delete(def(D)) :-
    lib_delete_aux(D,1),
    if(lib_present(synth(D)),lib_delete(synth(D))),
    if(lib_present(wave(D)),lib_delete(wave(D))),
    if(lib_present(red(D)),lib_delete(red(D))),
    if(definition(D/_<==>_), erase_def(D)),
    lib_writef(23,'Deleted def(%t)\n',[D]).

        % For (sub)methods we map into the code that handles the
        % (sub)method databases.
        % The calls to lib_present/1 are strictly speaking unnecessary
        % (since we already tested for presence of mthd(M/A) at the top
        % of lib_delete), but it serves to instantiate M/A properly if
        % lib_delete was called with a var argument.
lib_delete(mthd(M/A)) :-
    lib_present(mthd(M/A)),
    delete_method(M/A),
    lib_writef(23,'Deleted %t\n',[mthd(M/A)]).
lib_delete(smthd(M/A)) :-
    lib_present(smthd(M/A)),
    delete_submethod(M/A),
    lib_writef(23,'Deleted %t\n',[smthd(M/A)]).
lib_delete(hint(M/A)) :-
    lib_present(hint(M/A)),
    delete_hint(M/A),
    lib_writef(23,'Deleted %t\n',[hint(M/A)]).

        % iterative version:
lib_delete([]).
lib_delete([H|T]) :- lib_delete(H), lib_delete(T).

lib_delete_aux(D,N) :-
    indexed_equation_name(D,N,Eqn),
    lib_present(eqn(Eqn)),
    lib_delete(anythm(Eqn,eqn)),
    M is N + 1,!,
    lib_delete_aux(D,M).
lib_delete_aux(_D,_N).

        % lib_delete deletes all objects in the current library.
lib_delete :- lib_delete(_), fail.
lib_delete.

lib_sdir(X) :-
    saving_dir(X).

        % lib_set/1 can set some global parameters. Currently only the
        % default directory for library-loading and the editor called by
        % lib_edit.
lib_set(dir(D)) :-
    ground(D),
    is_list(D),!,
    lib_writef(23,'Setting library search path to %t.\n',[D]),
    remove_pred(lib_dir,1), assert(lib_dir(D)).
lib_set(sdir(D)) :- !,
    ground(D),
    \+ is_list(D),!,
    lib_writef(23,'Setting library save directory to %t.\n',[D]),
    remove_pred(saving_dir,1), assert(saving_dir(D)).
lib_set(editor(E)) :- !,
    lib_writef(23,'Setting editor to %t.\n',[E]),
    remove_pred(lib_editor,1), assert(lib_editor(E)).
lib_set(_) :-
    clam_user_error(
        'Argument to lib_set/1 must be one of dir([..]), sdir(.), editor(.)\n',[]),
    !,fail.

        % lib_edit(+Mthd) will edit Mthd (which is a (sub)method
        % specification of the form mthd(M/N) or smthd(M/N)). After
        % editing, Mthd will be loaded.
        % Optional second argument specifies directory where Mthd is to
        % be found, defaulting to the library directory.
        %
        % lib_edit/0 will edit most recently edited (sub)method.
:- dynamic lib_editor/1.
lib_edit(Mthd) :- lib_dir(Dir), lib_edit(Mthd,Dir).
lib_edit(Mthd,Dir) :- clause(lib_editor(Edit),_),!,lib_edit(Mthd,Dir,Edit).
lib_edit(Mthd,Dir) :-
    (environ('VISUAL', Edit)
     orelse environ('EDITOR', Edit)
     orelse Edit=vi
    ),
    assert(lib_editor(Edit)),
    lib_edit(Mthd,Dir).
lib_edit(Mthd,Dir,Edit) :-
    Mthd =.. [Type,M/_], member(Type,[mthd,smthd]),
    (recorded(lib_edit,_,Ref)->erase(Ref);true),
    recorda(lib_edit,(Mthd,Dir),_),
    concatenate_atoms([Edit,' ',Dir,'/',M,'.',Type],Command),
    unix(shell(Command)),!,
    lib_load(Mthd,Dir).
lib_edit(_,_,_) :-
    clam_warning('Can (currently) only edit mthd(M/N) or smthd(M/N)\n'),
    !,fail.
lib_edit :-
    recorded(lib_edit,(Mthd,Dir),_),!,lib_edit(Mthd,Dir).
lib_edit :-
    clam_warning('No previously edited object\n'),!,fail.


/* search down Path (a list of directories) for a directory Dir which
 * points to an object Type(D).  We don't use member/2 here since we
 * want to be sure to scan Path in the correct order.  The special
 * symbol '*' in a Path signifies the default system directory: this
 * cannot be changed by the user, it is defined at compile-time.  In
 * case of non-list path argument, expand into a singleton path.  */
lib_fname_exists(Directory, Dir,D, Type, File) :-
    \+ is_list(Directory),
    !,
    lib_fname_exists([Directory], Dir,D, Type, File).
lib_fname_exists([], _Dir,_D, _Type, _File) :- !,fail.
lib_fname_exists(['*'|_Path], Dir,D, Type, File) :-
    lib_dir_system(Dir),
    lib_fname(Dir,D,Type,File),                 % get the full name
    file_exists(File),!.
lib_fname_exists([Dir|_Path], Dir,D, Type, File) :-
    lib_fname(Dir,D,Type,File),                 % get the full name
    file_exists(File),!.
lib_fname_exists([_|Path], Dir,D, Type, File) :-
    lib_fname_exists(Path, Dir,D, Type, File).  % else recurse


/* simpler version for directory searching and a single filename */
lib_fname_exists([],_File,_AbsFile) :- !,fail.
lib_fname_exists(['*'|_Path],File,AbsFile) :-
    lib_dir_system(Dir),
    concatenate_atoms([Dir,'/',File],AbsFile1),
    lib_fname(AbsFile1,AbsFile),
    file_exists(AbsFile),!.
lib_fname_exists([D|_Path],File,AbsFile) :-
    concatenate_atoms([D,'/',File],AbsFile1),
    lib_fname(AbsFile1,AbsFile),
    file_exists(AbsFile),!.
lib_fname_exists([_D|Path],File,AbsFile) :-
    lib_fname_exists(Path,File,AbsFile).


        % Try to give decent error messages to user:
lib_error(AnyThing) :-
    \+ logical_object(AnyThing,_Str,_Args),
    findall(O-S-A,(logical_object(O,S,A),numbervars(O-A,1,_)),Os),
    clam_warning('Illegal specification of logical object: %t.\n',
                        [AnyThing]),
    writef('            Should be one of:\n'),
    lib_error_aux(Os),
    fail.

lib_error_aux([]).
lib_error_aux([O-A-S|Os]) :-
    tab(4),
    print(O), write(' --- '),
    writef(A,S),nl,
    lib_error_aux(Os).

        % transitive closure of the needs/2 relation. Can be used
        % both ways round! For example:
        %   needed(thm(t1),def(D)) finds all definitions needed for
        %   theorem t1, and
        %   needed(thm(T),def(d1)) finds all theorems that need
        %   definition d1.

needed(Needer,Needed) :-
    is_needed(Needer,N),
    member(Needed,N).
needed(Needer,Needed) :-
    is_needed(Needer,N),
    member(N1,N),
    needed(N1,Needed).
is_needed(A,B) :-
    (needs(A,B) -> true; B=[]).

/* uniq_recorda/3 is like recorda/3, except that it has specialised
 * knowledge about what kind of duplicate information should be
 * avoided in the various databases.  If it spots a potential
 * duplicate, it first removes the duplicate and calls itself again.
 * This means that we don't have to worry about duplicates in all the
 * places where we do record's, but we can leave it to this predicate
 * to take care of avoiding duplication.

 * Since this predicate uses unification to match existing records and
 * new records, it can happen (and does happen) that it gets caught
 * out by Prolog's lack of occur's check when records contain unbound
 * variables.  In those cases we therefore make the existing item
 * ground before unification (and then of course have to use double
 * negation to avoid variables in the new record to get bound).  */
uniq_recorda(theorem, theorem(Name,Type,_,Thm),_) :-
    recorded(theorem, theorem(Name,Type,_,Thm),OldRef),
    erase(OldRef),
    fail.
uniq_recorda(registry, registry(Reg,_,_),_) :-
    %% Removing the registry forces us to remove all reduction rules,
    %% otherwise a non-terminating system may result.
    recorded(registry, registry(Reg,_,_),OldRef),
    erase(OldRef),
    reduction_rule(_,_,_,_,_,RuleOldRef),
    erase(RuleOldRef),
    fail.
uniq_recorda(comp_set, comp_set(Thms,_CS),_) :-
    %% complementary sets are defined by a collection of rewrite rules
    %% (Thms), and we want to avoid duplication of these sets.
    recorded(comp_set, comp_set(Thms2,_),OldRef),
    subset(Thms2,Thms),
    erase(OldRef),
    fail.

/* It is conceivable that rewrites will one-day include quantifiers, so
   in that case we would parse x:t=>y:s=>P(x,y) as a rewrite P(X,Y)
   (as normal) and also the two other cases y:s=>P(X,y) and
   x:t=>P(x,Y).  Similarly, Clam currently uses p=>q=>r=>s as two
   rules, one conditional on p, the other on p=>q.

   In these cases, the Name/TypeDir is insufficient to pin-down the
   rewrite, so we need to check the LHS, RHS and Cond as well.
   Unification is ok since we do not want
   generalizations/specializations to be stored under the same name
   (in other words it boils down to alpha-convertibility).
 */
uniq_recorda(reduction, reduction(L,_,R,_,C,TypeDir,_,_,RuleName),_) :-
    reduction_rule(LL,RR,CC,TypeDir,RuleName,OldRef),
    unifiable(LL-RR-CC,L-R-C),
    erase(OldRef),
    fail.
uniq_recorda(rewrite,rewrite(L,_,R,_,C,TypeDir,_,Name),_) :-
    rewrite_rule(LL,RR,CC,TypeDir,Name,OldRef),
    unifiable(LL-RR-CC,L-R-C),
    erase(OldRef),
    fail.
uniq_recorda(scheme,scheme(A,B,C),_) :-
    /* erase all schemes less general than this one */
    recorded(scheme,scheme(AA,BB,CC),OldRef),
    \+ \+ (make_ground(scheme(AA,BB,CC)),
           scheme(AA,BB,CC) = scheme(A,B,C)),
    erase(OldRef),
    fail.
uniq_recorda(scheme,scheme(A,B,C),_) :-
    /* ... and only add this one if it is not an instance of an existing one */
    \+ \+ (make_ground(scheme(A,B,C)),
           recorded(scheme,scheme(A,B,C),_)),!.
uniq_recorda( method, _, _) :-
    recorded( method, _, OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( submethod, _, _ ) :-
    recorded( submethod, _, OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( hint, _, _ ) :-
    recorded( hint, _, OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( proof_plan, proof_plan(_,T,_,_,_), _ ) :-
    recorded( proof_plan, proof_plan(_,T,_,_,_), OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( Index, method(A,_ ), _ ) :-
    recorded( Index, method(A,_), OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( Index, submethod(A, _ ), _ ) :-
    recorded( Index, submethod(A,_), OldRef ),
    erase(OldRef),
    fail.
uniq_recorda( Index, hint(A, _ ), _ ) :-
    recorded( Index, hint(A,_), OldRef ),
    erase(OldRef),
    fail.
/* base clause does the real work (ie. if no duplicate is found,
 * possibly after duplicates have removed):  */
uniq_recorda(Index,Term,Ref) :- recorda(Index,Term,Ref).

/* Beginnings of a lib_create */
lib_create(trs(default)) :-
    if(lib_present(trs(default)),lib_delete(trs(default))),
    uniq_recorda(registry,registry(positive,[in/ms],[]-[]),_),
    uniq_recorda(registry,registry(negative,[in/ms],[]-[]),_).

lib_create(defeqn(Name)):-
    read_type(Name, Type),
    write('Enter equations for... ("eod." to finish)'),nl,
    read_equations(Name, Type, 1),
    writef('Use lib_save(defeqn(%t)) to save and parse your definition.',[Name]),nl.

read_type(Name, Dm => Rn):-
        writef('Enter type for %t: ',[Name]),
        readfile(user, Dm => Rn),
        generate_args(Dm, Args),
        concatenate_atoms([Name], NameSynth),
        NameArgs =.. [Name|Args],
        TermOfSynth =.. [term_of, NameSynth],
        generate_appl(TermOfSynth, Args, Defn),
        generate_synth_thm(Dm, Args, Rn, ThmSynth),
        add_thm(NameSynth, ThmSynth),
        record_thm(NameSynth, synth),
        add_def(NameArgs <==> Defn).

        % generate_synth_thm/4
        %
        %
generate_synth_thm(Dm, Args, Rn, []==>ThmSynth):-
        gen_synth_thm(Dm, Args, Rn, ThmSynth).

gen_synth_thm(Typ # Typs, [Arg|Args], RnTyp, Arg:Typ => Body):-
        gen_synth_thm(Typs, Args, RnTyp, Body).
gen_synth_thm(Typ, [Arg], RnTyp, Arg:Typ => RnTyp):-
        member(Typ, [int, list(int), pnat, list(pnat)]).

        % generate_args/2
        %
        %
generate_args(Type, Args):-
        generate_args_(Type, Args),
        make_ground(Args).
generate_args_(_ # Typs, [_|Args]):-
        generate_args_(Typs, Args).
generate_args_(_, [_]).

        % generate_appl/3
        %
        %
generate_appl(Func, [], Func).
generate_appl(Func, [Arg|Args], FuncApp):-
        generate_appl(Func of Arg, Args, FuncApp).

        % read_equations/3
        %
        %
read_equations(Eqn, Type, Cnt):-
    indexed_equation_name(Eqn, Cnt, EqnCnt),!,
    writef('%t: ', [EqnCnt]),
    read_equation(EqnCnt, Type, Equation),
    (Equation = eod
      -> writef("Defintion of %t completed.\n",[Eqn])
      ;  (NCnt is Cnt + 1,
          read_equations(Eqn, Type, NCnt))).
read_equations(_Eqn, _Type, _Cnt):-
    nl,write('Bad defintion (syntax?)'), nl.



        % read_equation/2
        %
        %
read_equation(EqnCnt, DmType => RnType, Equation):-
    readfile(user, Equation),
    (\+ Equation = eod
      -> ((Equation = (LHS = RHS)
            -> Cond = []        %empty Condition
            ;  Equation = (Cond => (LHS = RHS))),
          generate_bindings(DmType, Cond => (LHS = RHS), Bindings),
          (Cond = []
            -> matrix(Bindings, LHS = RHS in RnType, EqnThm)
            ;  matrix(Bindings, Cond => (LHS = RHS in RnType), EqnThm)),
          add_thm(EqnCnt, []==>EqnThm),
          record_thm(EqnCnt, eqn))
      ;  true).

        % generate_bindings/3
        %
        %
generate_bindings(Type, [] => LHS = RHS, Bindings):-
    freevarsinterm(LHS, VarsLHS),
    freevarsinterm(RHS, VarsRHS),
    subset(VarsRHS, VarsLHS),
    gen_bindings(Type, LHS, VarsLHS, Bindings).
generate_bindings(Type, Cond => LHS = RHS, Bindings):-
    \+Cond = [],
    freevarsinterm(LHS, VarsLHS),
    freevarsinterm(RHS, VarsRHS),
    freevarsinterm(Cond, VarsCond),
    (subset(VarsCond, VarsLHS)
      -> (subset(VarsRHS, VarsLHS)
          -> gen_bindings(Type, LHS, VarsLHS, Bindings)
          ;  writef("Freevariables of rhs %t are not subset of those in lhs %t\n",[RHS,LHS]))
      ; writef("Freevariables of condition %t are not subset of those in lhs %t\n",[Cond,LHS])).

        % gen_bindings/3
        %
        %
gen_bindings(Type, Term, Vars, VarTyps):-
        Term =.. [_|Args],
        type_terms(Type, Args, ArgsTyps),
        type_vars(ArgsTyps, Vars, VarTyps).

type_terms(Typ # Type, [Arg|Args], [Arg-Typ|ArgsTyps]):- !,
        type_terms(Type, Args, ArgsTyps).
type_terms(Typ, [Arg], [Arg-Typ]).

type_vars([], _, []).
        %
        % varibale case
        %
type_vars([Term-Typ|TermTyps], Vars, [Term:Typ|Bindings]):-
        member(Term, Vars),
        type_vars(TermTyps, Vars, Bindings).
        %
        % constant case
        %
type_vars([Term-Typ|TermTyps], Vars, Bindings):-
        oyster_type(Typ, _, [Term]),
        type_vars(TermTyps, Vars, Bindings).
        %
        % constructor case
        %
type_vars([Term-Typ|TermTyps], Vars, Bindings):-
        oyster_type(Typ, [Term], _),
        decomp_term_typs(Term, Typ, TTs),
        append(TTs, TermTyps, NewTermTyps),
        type_vars(NewTermTyps, Vars, Bindings).

decomp_term_typs(s(X), pnat, [X-pnat]).
decomp_term_typs(X::Y, Z list, [X-Z, Y-(Z list)]).

/* tell/1 but with error message */
tell_on_file(File) :-
    tell(File),!.
tell_on_file(File) :-
    clam_user_error('Unable to write to file %t\n',[File]),
    fail.

lib_writef(N,S,A) :-
           plantraced(N,writef(S,A)).

equation_index_separator('').                   %first one is preferred
equation_index_separator('.').                  %new style
indexed_equation_name(E,N,Root) :-
    equation_index_separator(EIS),
    concatenate_atoms([E,EIS,N],Root).


/* stuff to examine theories.  */

dump_thy(thm(T),Deps,Path) :-
    concatenate_atoms(['thy/',T,'.',thy],File),
    show_thy(thm(T),Path,Deps,File).
show_thy(thm(T),Path,Tree,File) :-
    lib_load_dep(thm(T),Tree,Path),
    ctheorem(T) =: problem([]==>G,_,_,_),
    tell(File),
    print(T:G),nl,
    show_thy_tree(Tree),
    told.

show_thy_tree(T) :-
    preorder_traversal(T,Trav),
    list_to_set(Trav,S),
    map_list_filter(S, def(X) :=> _,
                    show_rules(def(X)),_).

make_tar(thm(T),Deps,Path) :-
    concatenate_atoms(['tar/',T],File),
    make_tar(thm(T),Path,Deps,File).
make_tar(thm(T),Path,Tree,File) :-
    requires_tc_dep(thm(T),Tree,Path),
    tell(File),
    write('all.lib/'),write(thm),write('/'),write(T),nl,
    make_tar(Tree),!,
    told.

make_tar(T) :-
    preorder_traversal(T,Trav),
    list_to_set(Trav,S),
    map_list(S, X :=> _, make_tar(X),_).

make_tar(def(X)) :-
    write('all.lib/'),write(def),write('/'),write(X),nl,
    write('all.lib/'),write(eqn),write('/'),write(X),write('.'),write('*'),nl.
make_tar(synth(X)) :-
    write('all.lib/'),write(synth),write('/'),write(X),nl.
make_tar(thm(X)) :-
    write('all.lib/'),write(thm),write('/'),write(X),nl.
make_tar(eqn(X)) :-
    write('all.lib/'),write(eqn),write('/'),write(X),nl.

dump_all_thy([]).
dump_all_thy([T|Ts]) :-
    dump_thy(thm(T),['all.lib']),
    dump_all_thy(Ts).

/* Extract all defintions from a theory required for the statement of
   some conjecture T.

   This bypasses the needs machinery standard in Clam: the idea here
   is to examine each object as it is loaded for definitions which
   need to be present.
*/

theory(T,Ns,Os) :-
    findall(O,(exp_at(T,_,Tm),
               Tm =.. [F|Args],
               \+ member(F,Ns),
               lengtheq(Args,Brgs),
               Term =.. [F|Brgs],
               rewrite_rule(Term,RHS,_,_,_,_),
               (Term =.. [O|_]; theory(RHS,[F|Ns],O))),Os).


/* S3 is set of all symbols required to define T. this does not
   include induction schemes, only def(_) and synth(_).  */
requires_tc(T,S3,Path) :-
    requires_one_step(T,S1,Path),
    requires_tc_map(S1,S2,Path),
    union(S1,S2,S3).
requires_tc_map([],[],_).
requires_tc_map([S|Syms],S3,Path) :-
    requires_tc(S,S1,Path),
    requires_tc_map(Syms,S2,Path),
    union(S1,S2,S3).

/* like requires_tc_map, but S2 is a tree. level 0 is T; level 1 are
   symbols needed by T; level 2 are symbols needed by those symbols in
   level 1.  etc.  The accumlators are used as a memo table to avoid
   computing duplicate solutions. */
requires_tc_dep(T,S2,Path) :-
    requires_tc_dep(T,S2,Path,[],_).
requires_tc_dep(T,S2,_Path,Memo,Memo) :-
    memberchk(T-S2,Memo),!.
requires_tc_dep(T,S2,Path,Memo1,[T-S2|Memo2]) :-
    requires_one_step(T,S1,Path),
    requires_tc_dep_map(S1,S2,Path,Memo1,Memo2).
requires_tc_dep_map([],[],_,Memo,Memo).
requires_tc_dep_map([S|Syms],[S-S1|S3],Path,Memo1,Memo3) :-
    requires_tc_dep(S,S1,Path,Memo1,Memo2),
    requires_tc_dep_map(Syms,S3,Path,Memo2,Memo3).

requires_one_step(Obj,Syms,Path) :-
    Obj =.. [Thing,T],
    member(Thing,[thm,red,wave]),
    !,
    (lib_fname_exists(Path,_Dir,T,thm,File) -> true;
     clam_user_error('There is no %t(%t) in the library path: %t to make a %t\n',
                     [thm,T,Path,Thing]),fail),
    readfile(File,problem(_H==>G,_R,_E,_S)), parse_defs(G,Syms).
requires_one_step(synth(T),Syms,Path) :-
    !,
    (lib_fname_exists(Path,_Dir,T,synth,File) -> true;
     clam_user_error('There is no %t(%t) in the library path: %t\n',
                     [synth,T,Path]),fail),
    readfile(File,problem(_H==>G,_R,_E,_S)), parse_defs(G,Syms).
requires_one_step(lemma(T),Syms,Path) :-
    !,
    (lib_fname_exists(Path,_Dir,T,lemma,File) -> true;
     clam_user_error('There is no %t(%t) in the library path: %t\n',
                     [lemma,T,Path]),fail),
    readfile(File,problem(_H==>G,_R,_E,_S)), parse_defs(G,Syms).


/* definition */
%%% requires_one_step(def(D),NRSyms,Path) :-
%%%     !,
%%%     /* a definition requires the RHS of its definition, and things
%%%     appearing in the synthesis statement.  Eqns are also needed.
%%%     May also need to consider induction schemes too */
%%%     (lib_fname_exists(Path, Dir,D,'synth', _)
%%%       -> (requires_one_step(synth(D),SynthSyms,[Dir]),
%%%       SynthRequires=[synth(D)|SynthSyms])
%%%       ;   SynthRequires=[]),
%%%
%%%     (lib_fname_exists( Path, _, D,'def',File) -> true;
%%%      clam_user_error('There is no def(%t) in the library path: %t\n',
%%%                  [D,Path]),fail),
%%%     readfile(File,{D}<==>Body),
%%%     parse_defs(Body,DefSyms),
%%%     /* process consequtively numbered equations */
%%%     requires_eqn(D,Path,_,EqnSyms,1),
%%%     union(DefSyms,SynthRequires,SS),
%%%     union(SS,EqnSyms,Syms),
%%%     /* Since equations are typically recursive, remove any recursive
%%%     reference */
%%%     delete(Syms,{D},NRSyms).

requires_one_step(def(D),NRSyms,Path) :-
    !,
    /* a definition requires the RHS of its definition, and things
    appearing in the synthesis statement.  Eqns are also needed.
    May also need to consider induction schemes too */
    (lib_fname_exists(Path, Dir,D,'synth', _)
      -> (requires_one_step(synth(D),SynthSyms,[Dir]),
          SynthRequires=[synth(D)|SynthSyms])
      ;  SynthRequires=[]),

    (lib_fname_exists( Path, _, D,'def',File) -> true;
     clam_user_error('There is no def(%t) in the library path: %t\n',
                     [D,Path]),fail),
    readfile(File,Head<==>Body),
    ((Head = {Atom} -> Atom = D;
      Head =.. [D|_]) -> true;
     problem_here),
    parse_defs(Body,DefSyms),
    /* process consequtively numbered equations */
    requires_eqn(D,Path,_,EqnSyms,1),
    union(DefSyms,SynthRequires,SS),
    union(SS,EqnSyms,Syms),
    /* Since equations are typically recursive, remove any recursive
    reference */
    delete(Syms,def(D),NRSyms),!.
requires_one_step(_D,[],_).

requires_eqn(D,Path,Dir,AllSyms,N) :-
    var(Dir),                                   %still to find an eqn
    concatenate_atoms([D,'.',N],Root),
    lib_fname_exists(Path,Dir,Root,'eqn',File),!,
    readfile(File,problem([]==>Eqn,_,_,_)),
    parse_defs(Eqn,ESyms),
    M is N + 1,
    requires_eqn(D,Path,Dir,Syms, M),
    union(ESyms,Syms,AllSyms).
requires_eqn(D,Path,Dir,AllSyms, N) :-
    \+var(Dir),                                 % continue with the
                                                % same Dir
    concatenate_atoms([D,'.',N],Root),
    lib_fname_exists([Dir],_,Root,'eqn',File),!,
    readfile(File,problem([]==>Eqn,_,_,_)),
    parse_defs(Eqn,ESyms),
    M is N + 1,
    requires_eqn(D,Path,Dir,Syms, M),
    union(ESyms,Syms,AllSyms).
requires_eqn(_D,_Path,_Dir,[], _M) :- !.


parse_defs({T},[def(T)]) :-
    atomic(T),!.                                % subset types also have the form {...}
parse_defs({SST},Syms) :-
    !,
    parse_defs(SST,Syms).
parse_defs(T,[]) :-
    atomic(T),!.
parse_defs(T,Syms) :-
    compound(T),!,
    T =.. [F|Args],
    (my_oyster_functor(F) -> Syms1 = [];
     Syms1 = [def(F)]),
    parse_defs_map(Args,Syms2),
    union(Syms1,Syms2,Syms).

parse_defs_map([],[]).
parse_defs_map([A|Args],Syms3) :-
    parse_defs(A,Syms),
    parse_defs_map(Args,Syms2),
    union(Syms,Syms2,Syms3).


/* load an object according to the tree-dependancies.  Since the tree
   may contain identical subtrees, check before loading */
lib_load_dep(S,Requires,Path) :-
    requires_tc_dep(S,Requires,Path),
    preorder_traversal(Requires,
                       X^_^(if(\+ lib_present(X),lib_load(X,Path))),0),
    %% _tc is not reflexive, so need that here
    !,
    lib_load(S,Path).

/* Delete everything in the tree */
lib_delete_dep(Requires) :-
    preorder_traversal(Requires,
                       X^_^(once(if(lib_present(X),lib_delete(X)))),0).


my_oyster_functor(F) :-
    oyster_functor(F).
my_oyster_functor(u).                           % these are missing?
my_oyster_functor(s).

/* BodyX succeeds with X instantiated to each node of tree T, D
   instantiated to the depth of the node, for all nodes; traversal is
   preorder.  Assumes that D,X are only Prolog variables in BodyX.  */

preorder_traversal([],_,_Depth).                 % nil is empty tree
preorder_traversal([T1|Ts],X^D^BodyX,Depth) :-
    preorder_traversal(T1,X^D^BodyX,Depth),
    preorder_traversal(Ts,X^D^BodyX,Depth).
preorder_traversal(Node-Descendants,X^D^BodyX,Depth) :-
    NewDepth is Depth + 1,
    preorder_traversal(Descendants,X^D^BodyX,NewDepth),
    copy_term(X^D^BodyX,Y^DD^BodyY),
    DD = Depth,
    Y = Node,
    call(BodyY).

/* traverse T into list L */
preorder_traversal([],[]).
preorder_traversal([T1|Ts],Trav) :-
    preorder_traversal(T1,T1trav),
    preorder_traversal(Ts,Tstrav),
    append(T1trav,Tstrav,Trav).
preorder_traversal(Node-Descendants,Trav) :-
    preorder_traversal(Descendants,Dtrav),
    append(Dtrav,[Node],Trav).

% add_commuted_equations(+Def) (failure driven loop)
%
% If we have shown that the function defined by Def is commutative,
% then add equation records (which may subsequently be parsed as
% wave rules etc) for commuted versions of the (generally defining)
% equations for Def, where the original equation is of the form:
% f(A, B) => g(f(C, D)) and the added equation is of the form:
% f(B, A) => g(f(D, C)).
%
% This could be extended to equations where the LHS only contains f
% as a subexpression, where the LHS or RHS contains multiple occurrences of
% f, etc.
%
add_commuted_equations(def(O)) :-
        clam_info('Note, need to add code for tactics for commuted wave rules soon.\n',[]),
        rewrite_rule(L,_Ll, R,_Rl, Cond, Dir, TypeInfo, O, Rulename, _),
        member(Dir,[equ(_,D), equiv(D), imp(D)]),
        ((D = left, L =.. [O, X, Y], NL =.. [O, Y, X], RE =.. [O, RX, RY], exp_at(R, _, RE),
                    RE2 =.. [O, RY, RX], replace_alleqeq(RE, RE2, R, NR) ;
         D = right, R =.. [O, X, Y], NR =.. [O, Y, X], LE =.. [O, LX, LY], exp_at(L, _, LE),
                    LE2 =.. [O, LY, LX], replace_alleqeq(LE, LE2, L, NL)) ->
        \+ (X == Y)),
        rule_labelling(NL, Nll, NR, Nrr),
        clam_info('Added commuted wave rule (%t) for equation %t.\n', [Dir, Rulename]),
%        clam_info('New (direction %t) rule %t = %t.\n',[Dir, NL, NR]),
        uniq_recorda(rewrite,rewrite(NL,Nll,NR,Nrr,Cond,Dir,TypeInfo,O,Rulename),_),
        fail.

add_commuted_equations(def(_O)).

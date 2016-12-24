/*
 * @(#)$Id: methods.pl,v 1.13 1998/08/26 12:09:47 img Exp $
 *
 * $Log: methods.pl,v $
 * Revision 1.13  1998/08/26 12:09:47  img
 * unflawed_ind_strat/1 and cases/1 deleted and merged into ind_strat/1
 *
 * Revision 1.12  1998/05/13 12:53:49  img
 * Added experiemental unflawed induction method.
 *
 * Revision 1.11  1997/05/09 15:07:00  img
 * Replace elementary and sym_eval with base_case
 *
 * Revision 1.10  1997/01/14 10:44:20  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.9  1996/12/06 14:32:55  img
 * Remove _cs versions
 *
 * Revision 1.8  1996/07/05  10:21:09  img
 * load_ind_plan(5) added.
 *
 * Revision 1.7  1996/06/18  17:15:06  img
 * needs_normalize/1 removed (use lib_present in benchmarking code)
 *
 * Revision 1.6  1995/10/18  12:11:56  img
 * singleton variables removed
 *
 * Revision 1.5  1995/10/03  13:24:18  img
 * induction/2 changed to induction/1
 *
 * Revision 1.4  1995/09/21  11:37:15  img
 * needs_normalise/2 added to support benchmarking code.
 *
 * Revision 1.3  1995/05/17  02:17:47  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:25  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: methods.pl,v 1.13 1998/08/26 12:09:47 img Exp $').

/* There was a time when all the methods of CLaM lived happily together
 * in one big file, and I could put all my general comments about
 * methods there. However, things got too crowded, and it the situation
 * was too inconsistent to integrate with the other CLaM logical objects
 * and the CLaM library mechanism (where each object lives only the
 * lonely in a file of its own), so I decided to do the same to the
 * methods: each method and submethod lives in a file of its own, in the
 * library directory (defined by the lib_dir/1 predicate) in a file
 * ending in .mthd or .smthd.
 *
 * Question: where would I now put all my general comments about methods?
 * Answer: Here! Any general remarks about the method formalism etc
 * should live in this file.
 *
 * The only "code" that lives in this file are a few Prolog commands
 * that tell the system to load a standard set of methods.
 * These few commands live at the bottom end of all my rambling, which
 * follows first.
 *
 * All the comments applying to individual (sub)methods live in
 * the corresponding .mthd and .smthd files. 
 */


/* All this is originally based on AlanB's DAI Research Paper 349,
 * shorter version in CADE-9 (1988), long version in JAR.
 * Some of the code is subsequently based on the IJCAI paper.
 * 
 * The predicates and connectives used in pre- and post-conditions are
 * defined in the files method-pred.pl and method-conn.pl
 *
 * The format for methods is as follows:
 *	method(name(..Args..), 
 *	       Input,
 *	       [Preconditions], 	% list of conjuncts
 *	       [Postconditions],	% list of conjuncts
 *	       [Outputs],		% list of goals to prove
 *	       tactic(..Args..,Input)
 * 	      ).
 * Notice that all these components are allowed to share Prolog
 * variables.
 *
 * Differences with the format in DAI-RP-349:
 * 1. Output slot is now always a list, to indicate branching (even when
 *    there is only one branch).
 * 2. Input and elements of Output are no longer formulas, but sequents, ie:
 *    Hyps ==> Goal. This allows methods to add to the hypothesis list
 *    (see the induction method for an example).
 *
 * It is also possible to create submethods. These submethods will never
 * be used on their own in a proof plan, but can be called from within
 * other (sub)methods (by using the applicable_submethod/[1;2;3;4]
 * predicates).
 *
 * Instead of specifiying methods explicitly as (sub)method/6 terms, it
 * is also possible to construct (sub)methods by iterating other methods
 * exhaustively. Such methods are called iterators (explained in greater
 * detail in methodical.pl), and can be constructed using the following
 * commands:
 *
 * [1] iterator(method, MethodName, methods, MethodList)
 * [2] iterator(method, MethodName, submethods, SubMethodList)
 * [3] iterator(submethod, SubMethodName, methods, MethodList)
 * [4] iterator(submethod, SubMethodName, submethods, SubMethodList)
 * 
 *     [1] will construct a method which iterates other methods,
 *     [2] will construct a method which iterates other submethods,
 *     [3] will construct a submethod which iterates other methods,
 *     [4] will construct a submethod which iterates other submethds.
 *
 * The new MethodName is specified as an atom, the elements of the
 * MethodList are specified as skeletal functors. The resulting iterator
 * will be a (sub)method with as name MethodName of arity 1.
 *
 * The .mthd and .smthd files will be read by the predicates
 * load_(sub)method/[1;2;3] (or better still, through their uniform
 * lib_load/[1;2;3] iterface), which will transform these external
 * representations of methods into an internal representation in the
 * (sub)method database. Thus, these files are NEVER consulted directly as
 * a Prolog file, but always read through the load_(sub)method/[1;2;3]
 * predicates. (Actually this is true for all files in the library, with
 * the exception of the needs.pl file).
 * 
 * Some control knowledge can be encoded in the ordering of the
 * methods in a file: if there is more than 1 clause for a single
 * method, then these clauses will occur together in one file, and will
 * always be read into the database in the same order in which they
 * occur in their file.  
 *
 */
load_ind_plan(0).				% do nothing

% default benchmarking plan.
load_ind_plan(1):-
	delete_methods,delete_submethods,
	lib_load(mthd(base_case/1)),
	lib_load(mthd(generalise/2)),
        lib_load(mthd(normalize/1)),
	lib_load(mthd(ind_strat/1)),
	list_methods.
load_ind_plan(2):-
        delete_methods,delete_submethods,
        lib_load(mthd(base_case/1)),
        lib_load(mthd(step_case/1)),
        lib_load(mthd(generalise/2)),
        lib_load(mthd(normalize/1)),
        lib_load(mthd(induction/1)),       
        list_methods.
load_ind_plan(3):-
	delete_methods,delete_submethods,
	lib_load(mthd(base_case/1)),
	lib_load(mthd(generalise/2)),
	lib_load(mthd(ind_strat/1)),
	list_methods.
load_ind_plan(4):-
	delete_methods,delete_submethods,
        lib_load(mthd(base_case/1)),
        lib_load(mthd(step_case/1)),
        lib_load(mthd(generalise/2)),
        lib_load(mthd(induction/1)),
        list_methods.
load_ind_plan(5):-
	delete_methods,delete_submethods,
        lib_load(mthd(base_case/1)),
        lib_load(mthd(step_case/1)),
        lib_load(mthd(generalise/2)),
        lib_load(mthd(induction/1)),
        list_methods.
load_ind_plan(6):-
	delete_methods,delete_submethods,
	lib_load(mthd(decide/1)),
	lib_load(mthd(base_case/1)),
	lib_load(mthd(generalise/2)),
        lib_load(mthd(normalize/1)),
	lib_load(mthd(ind_strat/1)),
	list_methods.

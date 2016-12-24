/* Method configuration
 * @(#)$Id: methods.pl,v 1.11 2005/05/09 18:06:27 smaill Exp $
 *
 * $Log: methods.pl,v $
 * Revision 1.11  2005/05/09 18:06:27  smaill
 * load succlemma by default
 *
 * Revision 1.10  2005/04/30 14:30:38  smaill
 * *** empty log message ***
 *
 * Revision 1.9  2005/04/26 14:34:40  smaill
 * 2.8.3 real revisions
 *
 * Revision 1.8  1998/09/17 10:37:32  img
 * *** empty log message ***
 *
 * Revision 1.7  1998/07/27 13:06:48  img
 * using_presburger/0 switch added
 *
 * Revision 1.6  1997/10/09 15:00:23  img
 * load primitive induction by default
 *
 * Revision 1.5  1996/12/06 14:41:28  img
 * Removed defuct call to texoutput/0; Portray induction at level 99.
 *
 * Revision 1.4  1996/06/12 12:48:22  img
 * initialize any default registry; use ind_strat by default.
 *
 * Revision 1.3  1995/06/06  18:40:59  img
 * 	* junk comments removed
 *
 * Revision 1.2  1995/05/18  13:14:56  img
 * 	* changes for new "make" process
 *
 * Revision 1.1  1994/09/16  09:16:11  dream
 * Initial revision
 */
:- dynamic using_presburger/0.
%% using_presburger.                 % off by default.

load_default_env :-
    lib_load(scheme(pnat_primitive)),
    lib_load(lemma(succlemma)),
    lib_load(scheme(list_primitive)),
    lib_load(def(true)),
    lib_load(def(iff)),
    lib_delete(eqn(iff1)),
    lib_load(eqns(or)), lib_load(eqns(and)), lib_load(eqns(imp)),
    lib_load(eqns(equality)).


:- delete_methods, delete_submethods,
   lib_create(trs(default)),
   load_default_env,
   trace_plan(_,22),
   wfftacs(on),
   portray_level(induction(_),_,99),
   load_ind_plan(1).				% load default plan.















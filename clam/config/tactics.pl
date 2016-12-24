/* Tactic configuration
 * @(#)$Id: tactics.pl,v 1.8 1999/05/19 15:54:42 julianr Exp $
 *
 * $Log: tactics.pl,v $
 * Revision 1.8  1999/05/19 15:54:42  julianr
 * Added switch (by default off) for commutative function library processing.
 *
 * Revision 1.7  1998/08/26 15:12:23  img
 * *** empty log message ***
 *
 * Revision 1.6  1998/07/27 13:07:25  img
 * trans_proving/0 switch added
 *
 * Revision 1.5  1997/10/09 15:00:49  img
 * load basic lemmas explicitly
 *
 * Revision 1.4  1996/07/09 14:55:37  img
 * Wff tactic initialization from tactics_wf.pl
 *
 * Revision 1.3  1995/06/06  18:41:01  img
 * 	* junk comments removed
 *
 * Revision 1.2  1995/05/18  13:14:58  img
 * 	* changes for new "make" process
 *
 * Revision 1.1  1994/09/16  09:16:11  dream
 * Initial revision
 *
 */

/* try to show that certain relations are transitive */
?- dynamic trans_proving/0.
trans_proving.

% commuting of defining equations is off by default (because we don't
% yet have tactic support.
%
?- dynamic comm_proving/0.
comm_proving.

?- retractall(comm_proving).

:- lib_load(def(iff)).

%%% Switch autotactic off: having it on is more confusing than helpful.
:- defaultautotactic := idtac.
        
%%% Switch wfftacs on
:- wfftacs_status := on.
        
%% Initialise wfftacs
:- set_wfftac.

%% Load lemmas needed by tactics.pl
:- lib_load(lemma([arith1, arith2,arith3,
		   list1,plesssucc, plesssucc2,
		   succ_nonzero_left, succ_nonzero_right,
		   cnc_s_bis,
		   ipc_dp_imp_e2,ipc_dp_imp_e3,ipc_dp_imp_e4])).



/*
 * @(#)$Id: cancellation.pl,v 1.8 1998/07/27 12:12:37 img Exp $
 *
 * $Log: cancellation.pl,v $
 * Revision 1.8  1998/07/27 12:12:37  img
 * Conditional tracing messages
 *
 * Revision 1.7  1997/11/08 12:20:21  img
 * cosmetic changes
 *
 * Revision 1.6  1997/01/14 10:44:05  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.5  1996/05/29 20:30:27  img
 * cosmetic surgery
 *
 * Revision 1.4  1996/05/22  09:14:40  img
 * removed commented clause of is_a_cancel_rule/3; rearranged goals in
 * remaining clause for speed improvement.
 *
 * Revision 1.3  1995/05/17  02:17:20  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:01  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: cancellation.pl,v 1.8 1998/07/27 12:12:37 img Exp $').

/*
 * This file contains all the code needed to deal with cancellation rules.
 * Cancellation rules are rewrite rules which are particularly useful for
 * post-fertilization rippling.
 *
 * A cancellation rule corresponds to an instance of a substitution rule.
 *
 * Just as wave-rules, cancellation rules are stored at load time.
 * This is done by the predicate add_cancellation_rule/1, called from the
 * library mechanism in library.pl
 */

add_cancel_rule(RuleName) :-
    is_a_cancel_rule(RuleName,Exp,Rule),
    uniq_recorda(cancel,cancel(Exp,RuleName:Rule),_),
    lib_writef(23,'Added cancel-record for %t\n',[RuleName]).
add_cancel_rule(_).

        % A cancellation rule is a lemma which expresses how
        % a term may be whole or partly cancelled - replace by
        % an instance of a subterm non-trivially nested within it.
        % 
is_a_cancel_rule( RuleName, Lhs, MC => Lhs :=> Rhs ) :-
    recorded(theorem,theorem(_,_,Eq,RuleName),_),
    precon_matrix( Vars, C=> (LL = LR in LT)  => (RL = RR in RT), Eq ),
    exp_at(RL,[_|_],LL), 
    exp_at(RR,[_|_],LR),
    decolon_preconds( C, DC ),
    replace_universal_vars( Vars, [DC,LL,LR,RL,RR],[MDC,MLL,MLR,MRL,MRR] ),
    Lhs = (MRL = MRR in RT), Rhs = (MLL = MLR in LT),
    decolon_preconds( MC, MDC ).



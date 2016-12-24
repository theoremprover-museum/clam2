/*
 * @(#)$Id: needs.pl,v 1.27 2005/05/09 18:17:43 smaill Exp $
 *
 * $Log: needs.pl,v $
 * Revision 1.27  2005/05/09 18:17:43  smaill
 * seems to need extra dependencies
 *
 * Revision 1.26  2005/04/30 14:30:39  smaill
 * *** empty log message ***
 *
 * Revision 1.25  2003/01/22 15:59:01  smaill
 * for DICE
 *
 * Revision 1.24  1998/11/10 15:35:28  img
 * *** empty log message ***
 *
 * Revision 1.23  1998/09/17 10:36:31  img
 * *** empty log message ***
 *
 * Revision 1.22  1998/08/26 14:53:59  img
 * *** empty log message ***
 *
 * Revision 1.21  1998/07/27 13:10:07  img
 * *** empty log message ***
 *
 * Revision 1.20  1998/03/25 09:43:57  img
 * *** empty log message ***
 *
 * Revision 1.19  1998/03/06 09:18:31  img
 * relation stuff
 *
 * Revision 1.18  1997/11/11 17:24:36  img
 * *** empty log message ***
 *
 * Revision 1.17  1997/10/16 10:33:56  img
 * *** empty log message ***
 *
 * Revision 1.16  1997/10/09 15:09:45  img
 * minor simplifications
 *
 * Revision 1.15  1996/12/11 14:09:59  img
 * Merge mthd and smthd libraries.
 *
 * Revision 1.14  1996/12/06 15:11:20  img
 * dist_rev_app, qrev_correct_gen, qrev_correct added
 *
 * Revision 1.13  1996/12/04 13:05:40  img
 * schemes are needed explicitly by the theorem, not relying on the synth
 * required to prove the definitions.
 *
 * Revision 1.12  1996/11/02  14:01:00  img
 * Drop redundant argument in ripple/3.
 *
 * Revision 1.11  1996/07/10  09:12:45  img
 * plusind mods; added support for casesplit variants.
 *
 * Revision 1.10  1996/06/20  09:33:50  img
 * lessleq2 was missing.
 *
 * Revision 1.9  1996/06/19  10:28:31  img
 * Tidying up; some new thms added.
 *
 * Revision 1.8  1996/06/11  16:48:23  img
 * Reflect alterations made to reduction rule machinery---primarily, wave
 * rules are not loaded as reduction rules, and vice versa.  The
 * equations for leq, geq, less and greater have been made honest,
 * necessitating lemmas XXXzero to be used as reduction rules in certain
 * proofs.   scheme(twos) does not require plus.
 *
 * Revision 1.7  1995/11/28  19:50:27  img
 * app1right not needed for rotlen
 *
 * Revision 1.6  1995/10/03  12:50:04  img
 * greaterplus3 diverges without sim. ind.;  tcons diverges
 *
 * Revision 1.5  1995/07/12  21:04:56  img
 * Unnecessary reduction rules removed
 *
 * Revision 1.4  1995/05/03  15:08:21  img
 * 	* addded (lost?) RCS header
 *
 * Revision 1.1  1994/09/16  09:25:08  dream
 * Initial revision
 */

/* This file should contain all the needs/2 clauses to record
   dependencies between logical objects such as definitions, theorems,
   lemma's etc.  */

% Declare dynamic so that users can modify this database with their own
% clauses, using assert/retract.

:- multifile needs/2.   
:- dynamic needs/2.

/* relation things */
needs(def(tc), [def(tci)]).
needs(def(tci),[def(power)]).

needs(lemma(length_acc_wf),[def(length)]).
needs(synth(len_syn),[lemma(length_acc_wf)]).

needs(lemma(length_tc_acc_wf),[def(length)]).
needs(scheme(less_length),[def(less),lemma(length_tc_acc_wf)]).
needs(def(quicksort),[scheme(less_length),
                      def(ge),def(le),def(app),
                      lemma(declist),
                      lemma(ge_reduces_length),
                      lemma(le_reduces_length)]).

needs(def(ge),[thm(lessdec)]).
needs(def(le),[thm(lessdec)]).

needs(thm(ge_length_less), [def(ge),def(length),def(less)]).
needs(thm(le_length_less), [def(le),def(length),def(less)]).

needs(scheme(less_cv), [def(less)]).

needs(thm(less_double_mono), [def(less),def(double),scheme(pairs)]).
needs(thm(less_double_mono2), [def(less),def(double),scheme(pairs)]).


needs(scheme('double_p'),[def(double),
	scheme(less_cv),
	thm(less_double),
	thm(even_succ_odd),
	lemma(double_inverse),
	thm(less_double_mono2),
	thm(lesszero),
	thm(even_or_odd)]).

needs(thm(plusleq_succ), [def(leq),def(plus)]).
needs(thm(even_succ_odd), [def(even),def(odd)]).


needs(thm(even_or_odd), [def(even),def(odd)]).

needs(scheme(less_cv), [def(less), lemma(less_one),
	lemma(lessdec),lemma(less_succ_1)]).


needs(lemma(less_succ_1), [def(less)]).
needs(thm(less_double), [def(less),def(double),thm(lesstrans4)]).

needs(thm(ordered_sort_idempotent1),[def(ordered),def(sort)]).
needs(thm(ordered_sort_idempotent2),[def(ordered),def(sort)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(times),       	[def(plus)]).
needs(def(divides),     	[def(times)]).
needs(def(minus),       	[def(pred)]).
needs(def(prime),       	[def(posint),def(divides)]).
needs(def(prodl),       	[def(times)]).
needs(def(even),        	[def(true)]).
needs(def(odd),         	[def(true)]).
needs(def(half),        	[]).
needs(def(fac),         	[def(times)]).
needs(thm(assp),        	[def(plus),wave(cnc_s),eqn(equality1)]).
needs(thm(assm),        	[def(times)]).
needs(thm(comm),        	[def(times)]). 
needs(thm(commtwo),     	[def(times)]). 
needs(thm(plus1right),  	[def(plus)]).
needs(thm(plus2right),  	[def(plus)]).
needs(thm(times1right), 	[def(times)]).
needs(thm(times2right), 	[def(times)]).
needs(thm(commthree),   	[def(times),wave(disttwo),wave(times2right)]).
needs(thm(binom_one),   	[def(minus),def(binom),def(pred)] ).
needs(def(binom),               [def(plus)]).
needs(thm(comp),        	[def(plus)]).
needs(thm(comp2),       	[def(plus)]).
needs(thm(dist),        	[def(plus),def(times)]).
needs(thm(disttwo),     	[def(plus),def(times)]).
needs(synth(even),      	[scheme(twos)]).
needs(synth(odd),       	[scheme(twos)]).
needs(synth(half),      	[scheme(twos)]).
needs(def(leq),         	[def(true),synth(leq)]).
needs(def(geq),         	[def(true),synth(leq)]).
needs(thm(minmax),      	[def(min),def(max),def(leq),scheme(pairs)]).
needs(def(less),                [def(true),lemma(succlemma)]).
needs(synth(lessgreater),       [lemma(succlemma)]).
needs(def(greater),             [def(true),synth(lessgreater)]).
needs(thm(lesss),       	[def(less)]).
needs(thm(zeroplus),    	[def(plus)]).
needs(thm(zerotimes),   	[def(times),wave(zeroplus)]).
needs(thm(zerotimes1),  	[def(times)]).
needs(thm(zerotimes2),  	[def(times)]).
needs(thm(plusless),     	[def(plus),def(less)]).
needs(thm(geqnotlessp), 	[def(geq),def(less),red(lesszero),red(geqzero),
				 scheme(pairs)]).
needs(thm(lessleq1),   	        [def(less),def(leq),red(leqzero),
				 red(lesszero),scheme(pairs)]).
needs(thm(lessleq2),   	        [def(less),def(leq),red(leqzero),
				 red(lesszero),scheme(pairs)]).
needs(thm(lesstrich),   	[def(less),def(greater),wave(cnc_s),
                                 scheme(pairs)]).
needs(thm(geqtrans),            [def(geq),red(geqzero),scheme(pairs)]).
needs(thm(plusgeq),     	[def(plus),def(geq)]).
needs(thm(plusgeq2),    	[def(plus),def(geq),
                                  wave(plus2right),thm(geqtrans)]).
needs(thm(evendouble),  	[def(even),def(double)]).
needs(thm(even_plus),  	        [def(even),def(plus)]).
needs(thm(halfdouble),  	[def(half),def(double)]).
needs(thm(doublehalf),  	[def(half),def(even),def(double),wave(cnc_s)]).
needs(thm(doubletimes1),	[def(double),def(times),
				  wave(times2right),wave(cnc_s)]).
needs(thm(doubletimes2),	[def(double),def(times),wave(cnc_s)]).
needs(def(exp),         	[def(times)]).
needs(thm(expplus),     	[def(exp),def(plus),wave(disttwo),wave(dist),
				  scheme(plusind)]).
needs(thm(exptimes),    	[def(exp),def(times),scheme(plusind),
				  wave(expplus),wave(dist)]).
needs(thm(evenodd1),    	[scheme(twos),def(even),def(odd)]).
needs(thm(evenodd2),    	[scheme(twos),def(even),def(odd)]).
needs(thm(lesstrans1),  	[def(less),scheme(pairs)]).
needs(thm(lesstrans2),  	[def(less),def(leq),red(leqzero),
				 %% red(leqzero) is needed only for ind_strat
				 scheme(pairs)]).
needs(thm(lesstrans3),  	[def(less),red(lesszero),scheme(pairs)]).
needs(thm(notlesstrans),	[def(less),def(leq),red(lesszero),
				 red(leqzero),scheme(pairs)]).
needs(thm(notlesstrans2),	[def(less),def(leq),red(leqzero),
				 %% red(leqzero) only for ind_strat
				 scheme(pairs)]).
needs(thm(notlesstrans3),	[def(leq),red(leqzero),scheme(pairs)]).
needs(thm(notleqreflex),	[def(leq)]).
needs(thm(lesseq),      	[def(less),def(leq),red(lesszero),
				 red(leqzero),wave(cnc_s),scheme(pairs)]).
needs(thm(leqsucc),    	        [def(leq)]).
needs(thm(leqtrans),    	[def(leq),red(leqzero),scheme(pairs)]).
needs(thm(greatertrans),	[def(greater),def(iff),
				 red(greaterzero),scheme(pairs)]).
needs(thm(greatercons), 	[def(greater),def(length)]).
needs(thm(leqdupl),     	[def(leq),scheme(pairs)]).
needs(thm(leqdouble),   	[def(leq),def(double),thm(leqtrans)]).
needs(thm(leqhalf),     	[def(leq),def(half),scheme(twos)]).
needs(thm(leqhalfdouble),   	[def(leq),def(half),
                                  def(double),scheme(twos)]).
needs(thm(halfpnat),		[def(plus),def(half),wave(cnc_s),
                                 wave(cnc_half),red(cnc_s),red(cnc_half)]).
needs(thm(greaterplus), 	[def(greater),def(plus),scheme(pairs)]).
needs(thm(greaterplus2),	[def(greater),def(plus)]).
needs(thm(greaterplus3), 	[def(greater),def(plus),scheme(pairs)]). 
needs(thm(greatertimes),	[def(greater),def(times),
				 mthd(apply_lemma/_),thm(greaterplus),
                                 scheme(pairs)]).
needs(thm(greaters),    	[def(greater)]).
needs(thm(greaterss),    	[def(greater)]).
needs(thm(greaters2),    	[def(greater),scheme(pairs)]).
needs(thm(greatercancel),	[def(greater),def(times)]).
needs(thm(grsqsuc),		[def(greater),def(times)]).
needs(thm(geqhalf),		[def(geq),def(half),scheme(twos)]).
needs(thm(geqdouble),		[def(geq),def(double),thm(geqtrans)]).
needs(thm(geqdoublehalf),	[def(geq),def(double),def(half),
                                  scheme(twos)]).
needs(thm(cnc_pred),    	[def(pred)]).
needs(thm(minus_pred),   	[def(minus),wave(cnc_pred)]).
needs(thm(minus_succ),   	[def(minus),wave(cnc_pred)]).
needs(thm(minus_plus), 		[def(plus),def(minus),wave(cnc_pred)]).
				  % Previously wave(minus_succ)]).

needs(thm(times_less),   	[def(times),def(less)]).
needs(thm(fac_less),   	        [def(fac),def(less),wave(times_less)]).

needs(thm(multzero),            [def(times)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% primefac stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(evenp),       	[def(even),def(plus),scheme(twos)]).
needs(thm(evenm),       	[def(even),def(times),scheme(twos),
				 wave(times2right),wave(evenp)]).
needs(thm(prodl),       	[def(prodl),def(pnatapp),def(times),
				 mthd(apply_lemma/_),thm(assm)]).
needs(thm(prodlapp),       	[def(prodl),def(pnatapp),def(times)]).
needs(thm(prodlwave),   	[def(prodl),def(pnatapp),def(times)]).
needs(thm(identrm),   	        [def(times)]).
needs(lemma(not0lm),    	[def(times)]).
needs(lemma(not0rm),    	[def(times)]).

% NOTE: Can not prove primefac (version 1.4 or 1.5.1). I (AndrewS)
% am working on this - it requires a lot of middle-out stuff to be
% properly sorted: checking types of solution terms are sensible
% controlling symbolic evaluation, conditional fertilization ....
% Probably proper control of potential wave-fronts etc as well
%
%
%needs(thm(primefac),   [def(prime),def(prodl),scheme(primec),wave(prodlwave),
%                         red(identrm),lemma(not0lm),lemma(not0rm)]).
%
% NOTE: Existential rippling synthesizes primefac in the context of
% constructor style induction (see factors for more detail).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% list stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(rev),         	[def(app)]).
needs(thm(litapp),      	[def(app),def(lit)]).
needs(thm(apprev),      	[def(app),def(rev)]).
needs(thm(assapp),      	[def(app)]).
needs(thm(comapp),      	[def(app),def(length)]).
needs(thm(lenrev),      	[def(length),def(rev)]).
needs(thm(lenapp),      	[def(length),def(app)]).
needs(thm(lensum),      	[def(length),def(app),def(plus)]).
needs(def(member),      	[def(true),lemma(deceqint)]).
needs(thm(memapp1),             [def(member),def(app)]).
needs(thm(memapp2),     	[def(member),def(app)]).
needs(thm(memapp3),     	[def(member),def(app)]).
needs(thm(app1right),   	[def(app)]).
needs(thm(memrev),      	[def(member),def(rev),wave(memapp3)]).
needs(thm(revrev),      	[def(rev)]).
needs(thm(revqrev),     	[def(rev),def(qrev),wave(assapp)]).
needs(thm(qrevqrev),     	[def(rev),def(qrev),red(qrev_correct),
				 wave(dist_rev_app), wave(assapp)]).
needs(thm(qrev_correct_gen),    [def(rev),def(qrev),def(app)]).
needs(thm(qrev_correct),        [def(rev),def(qrev),def(app)]).
needs(thm(dist_rev_app),        [def(rev),def(app)]).
needs(thm(tailrev),     	[def(rev),def(app)]).
needs(thm(tailrev2),    	[def(rev),def(app)]).
needs(thm(singlerev),   	[def(rev)]).
needs(def(nth),         	[]).
needs(thm(nthnil),      	[def(nth)]).
needs(thm(nthmem),      	[scheme(nat_list_pair),def(nth),def(member)]).
%  NOTE: depth-first this plan is very fragile - the induction method
%  gets the right induction only by luck.  It would be interesting to 
%  see if you could analyse a solid principle to ensure the right 
%  induction is chosen.
needs(thm(nthapp),      	[def(nth),def(plus),scheme(nat_list_pair)]).
needs(def(flatten),     	[]).
needs(synth(flatten),   	[def(nestedlist),def(app)]).
needs(def(flattenmc),   	[]).
needs(synth(flattenmc), 	[def(nestedlist)]).  % NOT IMPLEMENTED (YET)
needs(def(tree),        	[def(node),def(leaf)]).
needs(def(maxht),       	[def(max)]).
needs(synth(maxht),     	[def(tree)]).
needs(def(minht),       	[def(min)]).
needs(synth(minht),     	[def(tree)]).
needs(scheme(treeind),  	[def(tree)]).
needs(thm(minmaxgeq),   	[def(min),def(max),def(geq),red(geqzero),
				 scheme(pairs)]).
needs(thm(maxhtminht),  	[synth(leq),def(maxht),def(minht),def(geq),
				 wave(minmaxgeq),scheme(treeind)]).
needs(def(ordered),             [def(true),scheme(list_double)]). 
needs(thm(ordered_cons),        [def(ordered),lemma(decless2),scheme(list_ind)]). 
needs(def(pairlist),    	[]).
needs(thm(mapcarapp),   	[def(mapcar),def(app)]).
needs(thm(lenmapcar),   	[def(mapcar),def(length),wave(cnc_s)]).
needs(thm(revmapcar),   	[def(mapcar),def(rev),wave(cnc_cons1)]).
needs(def(subset),      	[def(member),def(true)]).
needs(thm(subsetcons),  	[def(subset)]).
needs(def(intersect),   	[lemma(decmember)]).
needs(synth(intersect), 	[def(member),lemma(decmember)]).
needs(def(union),       	[def(member),lemma(decmember)]).
needs(synth(union),     	[def(member),lemma(decmember)]).
needs(def(insert),      	[def(less),lemma(decless2)]).
needs(def(sort),        	[def(insert)]).
needs(thm(lensort),     	[def(length),def(sort)]).
needs(thm(subsetunion), 	[def(subset),def(union)]).
needs(thm(subsetintersect),	[def(subset),def(intersect),wave(cnc_cons1)]).
needs(thm(memunion1),   	[def(member),def(union),lemma(decmember)]).
needs(thm(memunion2),   	[def(member),def(union)]).
needs(thm(memintersect),	[def(member),def(intersect)]).
needs(def(assoc),       	[lemma(deceqintlist)]).
needs(thm(leqnth),      	[scheme(nat_list_pair),def(leq),def(length),def(nth)]).
needs(thm(memins),		[def(member),def(insert)]).
needs(thm(meminsert1),  	[def(member),def(insert)]).
needs(thm(meminsert2),  	[def(member),def(insert)]).
needs(thm(memsort1),    	[def(member),def(sort)]).
% NOTE: This needs a lemma because it otherwise misses a necessary
% generalisation - sigh.
needs(thm(memsort2),    	[def(member),def(sort),
				 wave([meminsert1,meminsert2])]).  
needs(def(count),       	[lemma(deceqint)]).
needs(thm(countsort),   	[def(sort),def(count),wave(cnc_s)]).
needs(thm(cnc_app),		[def(app)]).
needs(def(rotate),       	[def(app),def(hd),def(tl)]).
needs(thm(rotlen),       	[def(rotate),def(app),def(length),
				  wave(assapp)]). 
needs(def(posint),		[def(greater)]).
needs(thm(cnc_posint_times),	[def(times),def(posint)]).
needs(thm(prod_times),	        [def(prod),def(times)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% factors synthesis proof (as presented in ``Turning Eureka Steps into
% Calculations in automatic program synthesis'', Bundy, Hesketh and Smaill,
% In proceedings of UK IT `90 (Andrew Ireland, July 91).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(factors),	        [def(posint),
				 def(prod),def(prime),
				 wave(cnc_posint_times),
				 wave(prod_times),
				 scheme(primescheme)]).

needs(thm(sqr),   	        [def(times),def(leq)]).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tcons (tail-cons) synthesis proof (as presented in blue book note 636).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(tcons),	 	[def(app),wave(cnc_cons1)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% induction scheme stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(lemma(dec_div),   	[def(divides)]).
needs(lemma(fstprime),  	[lemma(dec_div)]).
needs(scheme(primescheme),    	[def(times),def(prime),lemma(fstprime),
				 def(acc_ord)]).
needs(scheme(primec),   	[def(times),def(prime),lemma(primelem)]).
needs(scheme(twos),     	[]).
needs(scheme(plusind),  	[def(plus),lemma(succlemma3)]).
needs(scheme(pairs),            [def(pred),def(fst),def(snd),def(pairord)]).
needs(scheme(list_pairs),       [def(fst),def(snd),def(lpairord),
                                 lemma(declist)]). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fibonacci synthesis:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(fib),              []).
needs(synth(fib),            [def(plus),def(pred),lemma(predless)]).
needs(eqn(fib3),             [lemma(succlemma),lemma(rpnateq_fa),lemma(succlemma3)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic-geometric means:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(prod),        	[def(times)]).
needs(def(sum),         	[def(plus)]).
needs(scheme(exp2),     	[def(p),def(times)]).
 /* Cannot prove this yet. Real work remains to be done before this will
  * be possible. Currently deleted for benchmarking purposes.
  * needs(thm(means),    [def(sum),def(prod),def(exp),def(times),def(geq),
  *                       red(plus1right),red(plus2right),red(times1right),
  *                       red(times2right),
  *                       wave(exptimestwo),wave(exptimes),wave(evensum),
  *                       wave(timesexp),wave(timesexptwo),wave(assm),
  *                       % scheme(times2),      % <- still to do
  *                       wave(expprod)          % <- still to do
  *                      ]).
  */
needs(def(gcd), [def(minus),def(less)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% method dependencies:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(mthd(ind_strat/1),        [smthd(induction/1),
				 smthd(base_case/1),
				 smthd(step_case/1)]).
needs(mthd(step_case/1),	[smthd(ripple/2),
				 smthd(unblock_then_fertilize/2)]).
needs(smthd(step_case/1),	[smthd(ripple/2),
				 smthd(unblock_then_fertilize/2)]).

needs(mthd(base_case/1),	[smthd(elementary/1), smthd(sym_eval/1)]).
needs(smthd(base_case/1),	[smthd(elementary/1), smthd(sym_eval/1)]).

needs(mthd(sym_eval/1),        [smthd(equal/2),
				smthd(normalize_term/1),
				smthd(casesplit/1),
				smthd(existential/2)]).
needs(smthd(sym_eval/1),        [smthd(equal/2),
				smthd(normalize_term/1),
				smthd(casesplit/1),
				smthd(existential/2)]).
needs(smthd(ripple/2),          [smthd(wave/4 ),
				 smthd(casesplit/1),
				 smthd(unblock_then_wave/2)]).

needs(smthd(unblock_then_wave/2), [smthd(unblock_lazy/1),
				   smthd(wave/4)]).
needs(smthd(unblock_then_fertilize/2), [smthd(unblock_fertilize_lazy/1),
					smthd(fertilize/2)]).
needs(smthd(unblock_lazy/1), [smthd(unblock/3)]).
needs(smthd(unblock_fertilize_lazy/1), [smthd(unblock/3)]).
needs(smthd(fertilize/2),	[smthd(pwf_then_fertilize/2),
				 smthd(ripple_and_cancel/1)]).
needs(smthd(fertilization_weak/1),
      [smthd(fertilize_then_ripple/1),
       smthd(elementary/1)]).
needs(smthd(pwf_then_fertilize/2), [smthd(pw_fertilize/1),
				    smthd(fertilization_strong/1),
				    smthd(fertilize_left_or_right/1)]).

needs(mthd(normalize/1), 	[smthd(normal/1)]).
needs(smthd(normalize/1), 	[smthd(normal/1)]).
needs(smthd(normal/1),          [smthd(apply_lemma/1),
   			         smthd(backchain_lemma/1)]).

needs(smthd(fertilize_then_ripple/1),          
      [smthd(pwf_then_fertilize/2),
       smthd(ripple_and_cancel/1)]).

needs(smthd(pw_fertilize/1),          
      [smthd(pwf/1)]).

needs(smthd(pw_fertilize/1), [smthd(pwf/1)]).

needs(smthd(fertilize_left_or_right/1), [smthd(weak_fertilize/4)]).

%needs(smthd(weak_fertilize_left/1), [smthd(weak_fertilize/4)]).

%needs(smthd(weak_fertilize_right/1), [smthd(weak_fertilize/4)]).

needs(smthd(ripple_and_cancel/1), [smthd(cancellation/2),
				   smthd(wave/4),
				   smthd(unblock/3)]).


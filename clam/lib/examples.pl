/*
 * @(#)$Id: examples.pl,v 1.15 2005/05/09 18:08:41 smaill Exp $
 *
 * $Log: examples.pl,v $
 * Revision 1.15  2005/05/09 18:08:41  smaill
 * reflects current capabilities
 *
 * Revision 1.14  1998/08/26 14:54:39  img
 * *** empty log message ***
 *
 * Revision 1.13  1997/11/11 17:24:37  img
 * *** empty log message ***
 *
 * Revision 1.12  1997/10/09 17:21:12  img
 * updates
 *
 * Revision 1.11  1996/12/12 15:34:47  img
 * add try tag to prodlwave
 *
 * Revision 1.10  1996/12/06 15:13:03  img
 * dist_rev_app added
 *
 * Revision 1.9  1996/12/06 15:10:30  img
 * qrev_correct_gen added
 *
 * Revision 1.8  1996/12/04 13:06:13  img
 * qrevqrev, greaterss added
 *
 * Revision 1.7  1996/07/10  09:11:58  img
 * prod_times: needs normalization
 *
 * Revision 1.6  1996/06/20  09:33:29  img
 * lessleq2 was missing.
 *
 * Revision 1.5  1996/06/19  10:24:50  img
 * example/3: Use lists of attributes in third argument.
 *
 * Revision 1.4  1996/06/11  16:49:22  img
 * This version of Clam does not work on synthesis theorems, so don't try
 * those.
 *
 * Revision 1.3  1995/10/03  12:50:02  img
 * greaterplus3 diverges without sim. ind.;  tcons diverges
 *
 * Revision 1.2  1995/05/10  14:21:19  img
 * 	* some theorems seem undefined
 *
 * Revision 1.1  1994/09/16  09:25:19  dream
 * Initial revision
 *
 */

/*
 * Index to the corpus of example theorems      
 * currently planned and executed by the
 * Clam-Oyster automated proof system. 
 *
 * example/3 specifies the type and name of  
 * each example.
 */

/*
 * Verification examples 
 */

/* arith */
example(arith,   binom_one	,[try]).
example(arith,   assp	        ,[try]).
example(arith,   assm	        ,[try]).
example(arith,   comm	        ,[try]).
example(arith,   commtwo	,[try]).
example(arith,   plus1right	,[try]).
example(arith,   plus2right	,[try]).
example(arith,   times1right	,[try]).
example(arith,   times2right	,[try]).
example(arith,   identrm	,[try]).
example(arith,   commthree	,[try]).
example(arith,   comp	        ,[try]).
example(arith,   comp2	        ,[try]).
example(arith,   dist	        ,[try]).
example(arith,   disttwo	,[try]).
example(arith,   minmax	        ,[try]).
example(arith,   lesss	        ,[try]).
example(arith,   less_double_mono ,[try]).
example(arith,   less_double_mono2 ,[try]).
example(arith,   zeroplus	,[try]).
example(arith,   zerotimes	,[try]).
example(arith,   zerotimes1	,[try]).
example(arith,   zerotimes2	,[try]). 		
example(arith,   multzero	,[try]). 		
example(arith,   geqnotlessp	,[try]).
example(arith,   plusless	,[skip]). % diverges with depth-first, ID is OK
example(arith,   geqtrans	,[try]).
example(arith,   lesstrich	,[try]).  
example(arith,   plusgeq	,[try]).
example(arith,   plusgeq2	,[try]).
example(arith,   evendouble	,[try]).
example(arith,   halfdouble	,[try]).
example(arith,   doubletimes1	,[try]).
example(arith,   doubletimes2	,[try]).
example(arith,   expplus	,[try]).
example(arith,   exptimes	,[try]).
example(arith,   evenodd1	,[try]).
example(arith,   evenodd2	,[try]).
example(arith,   lesstrans1	,[try]).	
example(arith,   lesstrans2	,[try]).	
example(arith,   lesstrans3	,[try]).	
example(arith,   notlesstrans	,[try]). 
example(arith,   notlesstrans2	,[try]). 
example(arith,   notlesstrans3	,[try]).
example(arith,   notleqreflex	,[try]).
example(arith,   lesseq	        ,[try]).	
example(arith,   leqtrans	,[try]).	
example(arith,   leqsucc	,[try]).	
example(arith,   lessleq1	,[try]).
example(arith,   lessleq2	,[skip]). % problems with double negation
example(arith,   greatertrans	,[try]).	
example(arith,   greatercons	,[try]).
example(arith,   leqdupl	,[try]).
example(arith,   leqdouble	,[try]).
example(arith,   leqhalf	,[try]).
example(arith,   leqhalfdouble	,[try]).	
example(arith,   halfpnat	,[try]).
example(arith,   greaterplus	,[try]).
example(arith,   greaterplus2	,[skip]). % diverges with df plan, id plan is OK
example(arith,   greaterplus3	,[try]).	
example(arith,   greatertimes	,[skip]).
example(arith,   greaters	,[try]).
example(arith,   greaterss	,[try]).
example(arith,   greaters2	,[try]).
example(arith,   greatercancel	,[skip]). % infinite nesting of inductions
example(arith,   grsqsuc	,[skip]). % missed cancellation (?)
example(arith,   geqhalf	,[try]).
example(arith,   geqdouble	,[try]).
example(arith,   geqdoublehalf	,[try]).
example(arith,   doublehalf	,[try]).
example(arith,   evenp	        ,[try]).
example(arith,   evenm	        ,[try]).
example(arith,   prodl	        ,[try]).
example(lists,   prodlapp       ,[try]).
example(arith,   prod_times     ,[try,needs_normalize]).
example(arith,   prodlwave	,[try,needs_normalize]).
example(arith,   minus_pred	,[try]).
example(arith,	 minus_succ	,[try]).
example(arith,   minus_plus	,[try]).
example(arith,   times_less	,[try]).
example(arith,   fac_less	,[try]).

/* lists */
example(lists,   litapp	        ,[try]).
example(lists,   apprev	        ,[try]).
example(lists,   assapp	        ,[try]).
example(lists,   comapp	        ,[try]).
example(lists,   lenrev	        ,[try]).
example(lists,   lenapp	        ,[try]).
example(lists,   lensum	        ,[try]).
example(lists,   memapp1	,[try]).
example(lists,   memapp2	,[try]).
example(lists,   memapp3	,[try]).
example(lists,   app1right	,[try]).
example(lists,   memrev	        ,[try]).		
example(lists,   revrev	        ,[try]).
example(lists,   revqrev	,[try]).
example(lists,   qrevqrev	,[try]).
example(lists,   qrev_correct_gen,[try]).
example(lists,   dist_rev_app	,[try]).
example(lists,   tailrev	,[try]).
example(lists,   tailrev2	,[try]).
example(lists,   singlerev	,[try]).
example(lists,   nthnil	        ,[try]).     
example(lists,   nthmem	        ,[try]).     
example(lists,   nthapp	        ,[try]).	
example(lists,   minmaxgeq	,[try]).    
example(lists,   mapcarapp	,[try]).
example(lists,   lenmapcar	,[try]).
example(lists,   revmapcar	,[try]).
example(lists,   subsetcons	,[skip]).
example(lists,   lensort	,[try]).
example(lists,   subsetunion	,[try]).
example(lists,   subsetintersect,[try]).
example(lists,   memunion1	,[try]).
example(lists,   memunion2	,[try]).
example(lists,   memintersect	,[try]).
example(lists,   leqnth	        ,[try]).
example(lists,	 memins	        ,[try]).
example(lists,   meminsert1	,[needs_normalize]).
example(lists,   meminsert2	,[needs_normalize]).
example(lists,   memsort1	,[try]).
example(lists,   memsort2	,[try]).
example(lists,   countsort	,[try]).
example(lists,   rotlen	        ,[try]).

example(lists,   ordered_cons   ,[try]).

example(trees,   maxhtminht     ,[try]).


/*
 * Synthesis examples.
 */

/* arith */
example(arith,   factors	,[skip]).
example(arith,   sqr     	,[skip]).

/* lists */
example(lists,   tcons	        ,[skip]).

/*
 * @(#)$Id: tactics.pl,v 1.46 2008/05/21 14:14:14 smaill Exp $
 *
 * $Log: tactics.pl,v $
 * Revision 1.46  2008/05/21 14:14:14  smaill
 * update for sicstus4
 *
 * Revision 1.45  2005/05/09 18:28:59  smaill
 * elementary tactic needs to dequantify
 *
 * Revision 1.44  2005/05/06 19:23:39  smaill
 * fix tactics for pwf
 *
 * Revision 1.43  1999/02/25 18:18:58  img
 * decide_pa added for comfort
 *
 * Revision 1.42  1999/02/04 16:38:14  img
 * fertilization_strong/1 fixed
 *
 * Revision 1.41  1999/02/02 09:50:15  img
 * tactic support for pwf/1 etc.
 *
 * Revision 1.40  1999/01/11 11:03:59  img
 * tactics for pwf/1
 *
 * Revision 1.39  1998/11/10 16:03:44  img
 * elementart(fertilize(_)) added
 *
 * Revision 1.38  1998/09/17 08:33:59  img
 * unfold_iff/0: (added)
 *
 * Revision 1.37  1998/08/28 10:17:17  img
 * fertilization_strong/1: clause for repeated s.f.
 *
 * Revision 1.36  1998/08/27 07:36:56  img
 * singleton vars removed
 *
 * Revision 1.35  1998/08/26 12:26:00  img
 * fixes and new tactics.
 *
 * Revision 1.34  1998/07/27 12:12:40  img
 * Conditional tracing messages
 *
 * Revision 1.33  1998/06/10 08:23:59  img
 * Cut can prevent use of suitable lemma
 *
 * Revision 1.32  1998/05/13 13:00:06  img
 * New ind. rule added.  Deal with commutativity in certain places.
 *
 * Revision 1.31  1998/03/25 10:33:30  img
 * pass context to instantiate to support polymorphic rewriting
 *
 * Revision 1.30  1998/01/21 17:05:09  img
 * propositional/1 added
 *
 * Revision 1.29  1997/11/06 16:02:03  img
 * induction/1: extra information dumped prior to do_induction/_
 *
 * Revision 1.28  1997/10/09 15:03:38  img
 * induction: nat_list_pair scheme aligned with variable choice of
 * method.  fail_tac/1 not enabled by default.  Since propositional/_ no
 * longer treats quantifiers, use (elementary or propositional) (and
 * sometimes wfftacs).
 *
 * Revision 1.27  1997/10/08 15:14:22  img
 * Added failure clauses for each tactic (debgging aid).  Replaced
 * perm(-,+)/2 with permutation(-,?)/2.
 *
 * Revision 1.26  1997/09/26 14:59:00  img
 * load_lemmas/0 removed (now done via needs file);  New tactics:
 * normalize_term(cancel(...)), casesplit(datatype(...)) [old casesplit
 * is now casesplit(disjunction(...))], identity_equiv,
 * rewrite_hyp_at_pos, forward_chain.
 *
 * Revision 1.25  1997/06/05 10:39:13  img
 * Extra argument to equ/1 tag on equational rewrites to record type; propositional/0 added; elim_on_thin/_ added.
 *
 * Revision 1.24  1997/05/07 17:12:17  img
 * rewrite_at_pos/4 equiv(right) bug fix.
 *
 * Revision 1.23  1997/04/07 11:42:25  img
 * added: beta_normalized_term/2.
 *
 * Revision 1.22  1997/01/14 10:44:29  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.21  1996/12/11 14:15:55  img
 * Tactics for unblock_then_...
 *
 * Revision 1.20  1996/12/06 14:32:18  img
 * Tactics for simple arithmetic
 *
 * Revision 1.19  1996/12/04 12:38:36  img
 * beta_reduce_plus/[0,1]: added: transitive closure of beta-reduction.
 * Bug fix in rewrite_at_pos for <=>.
 *
 * Revision 1.18  1996/07/09 14:50:57  img
 * guess_type/2 -> guess_type/3: new arguments is context.  This is an
 * improved version of type guessing, based on guess_type/2, but (i)
 * crazy bugs removed, and (ii) additional argument provides context that
 * can also be typed.  Use of meta_try/1 is an attempt to return as much
 * information about the type as possible.  For example, we have
 * guess_type(lambda(u,lambda(v,member(u,v))),[],int=>int list=>u(1)).
 *
 * wfftacs/0 has also been strengthed, exploiting new guess_type/3.
 *
 * non-wfftacs related code removed to tactics.pl from tactics_wf.pl.
 *
 * Revision 1.17  1996/07/05  10:20:32  img
 * clam_arith tactics for <*; other non-clam-related stuff.
 *
 * Revision 1.16  1996/06/20  10:45:08  img
 * Support for casesplit variants of base-case and sym-eval.
 *
 * Revision 1.15  1996/06/18  17:18:52  img
 * Add support for tree induction.  During weak fertilization, ensure
 * that variables unbound by instantiate/3 are instantiated (ie, use
 * instantiate/4).
 *
 * Revision 1.14  1996/06/11  16:41:30  img
 * Upgrades for rewriting using <=>.
 *
 * Revision 1.13  1996/05/24  09:29:10  img
 * normalize_term/1 tactic added; rationalize the token used in the first
 * argument of unblock/3.
 *
 * Revision 1.12  1995/10/18  12:12:08  img
 * singleton variables removed
 *
 * Revision 1.11  1995/10/03  13:28:48  img
 * induction/2 changed to induction/1 and associated changes.  rename_hyp
 * needed whenever a lemma is used to justify the induction.  Slight
 * change to do_induction for nat_list_pair so that variables agree with
 * scheme/4.
 *
 * Revision 1.10  1995/09/21  11:34:52  img
 * added better alignment of tactic/method for rewriting when fewer
 * variables appear on the right of a rule than on the left.  this arose
 * with weak-fertilization.
 *
 * Revision 1.9  1995/08/30  15:01:49  img
 * added universe argument to dequantify
 *
 * Revision 1.8  1995/07/18  12:58:28  img
 * identity tactic to use equality rather than repeat intro
 *
 * Revision 1.7  1995/07/03  18:24:58  img
 * 	* intro and elim for <=>
 *
 * Revision 1.6  1995/05/17  02:17:57  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.5  1995/05/12  15:56:52  img
 * 	* show me the disjunction you couldn't prove
 *
 * Revision 1.4  1995/05/12  15:42:12  img
 * 	* added clause to wave/4 for complementary tag;
 * 	  unblock(meta_ripple..) added
 * 	* list2disj/2 (casesplit) stripped list nesting to bring into
 * 	  line with casesplit/complementary rewrite format
 *
 * Revision 1.3  1995/03/01  04:14:40  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.2  1995/02/28  00:25:54  img
 * 	* extra argument(s) to wave and ripple tactics
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: tactics.pl,v 1.46 2008/05/21 14:14:14 smaill Exp $').

/*
 *
 *  IND_STRAT TACTIC
 *
 */

ind_strat(Tac):- apply(Tac).
unflawed_ind_strat(Tac):- apply(Tac).

/*=======================================================================
 * Code to apply arbitrary induction schemes.
 * There should be induction/2 clauses for every scheme defined via
 * scheme/5 
 */ 

	% induction(+S,+V) applies induction scheme S to variable V.
	% First mess around with the quantifiers (if any), and then
	% apply the actual induction:
        % first case: induction var occure free (QQ what if bound also??)
        % second case: pull apart (too much, here)
induction(_INFO-[(Var:Type)-IT]):- goal(G),freevarinterm(G,Var),
	  do_induction([(Var:Type)-IT]).
induction(_INFO-[(Var:Type)-IT]):-
    quantifier_to_front(Var:Type)
        then try dequantify_once
	    then do_induction([(Var:Type)-IT]).

        % Alan Smaill's support for simultaneous induction
induction(_INFO-[(V1:T1)-IT1,(V2:T2)-IT2]):-
    goal(G),
    freevarinterm(G,V2),freevarinterm(G,V1),
    !, do_induction([(V1:T1)-IT1,(V2:T2)-IT2]).
induction(_INFO-[(V1:T1)-IT1,(V2:T2)-IT2]) :-
    goal(G),
    freevarinterm(G,V2),!,
    quantifier_to_front(V1:T1)
        then try dequantify_once
        then do_induction([(V1:T1)-IT1,(V2:T2)-IT2]).
induction(_INFO-[(V1:T1)-IT1,(V2:T2)-IT2]):-
    goal(G),
    freevarinterm(G,V1),!,
    quantifier_to_front(V2:T2)
        then try dequantify_once
        then do_induction([(V1:T1)-IT1,(V2:T2)-IT2]).
induction(_INFO-[(V1:T1)-IT1,(V2:T2)-IT2]):- 
    quantifier_to_front(V2:T2)
     then quantifier_to_front(V1:T1)
        then try dequantify_once
         then try dequantify_once
            then do_induction([(V1:T1)-IT1,(V2:T2)-IT2]).

        % Induction with step F(x,y) ==> F(s(x),s(y))
induction(Ind) :-
    fail_tac(induction(Ind)).

% Special version of free to support tactic called with Prolog vars
hypfree([],_).
hypfree([X|L],H):-var(X),!,genvar(X),hypfreevar(X,H),hypfree(L,[X:_|H]),!.
hypfree([X|L],H):-ttvar(X),hypfreevar(X,H),hypfree(L,[X:_|H]).

hypfree(X,H,HH):-hypfree(X,H),extend(X,H,HH).
hypfreevar(X,H):- make_hyps_ground(H), freevar2(X,H).
freevar2(X,H):- decl(X:_,H),!,fail.
freevar2(X,H):- member(D<==>_,H),functor(D,X,_),!,fail.
freevar2(_,_).

vnvelts(X,Y,Z) :- velts(X,[],[],(Y,Z)).
velts([X:_|T],A,B,Y) :- var(X), !, velts(T,[X|A],B,Y).
velts([H|T],A,B,Y) :- velts(T,A,[H|B],Y).
velts([],A,B,(A,B)).
make_hyps_ground(X) :- vnvelts(X,V,NV), reverse(V,VV),free(VV,NV).

/* rename_hyp avoids a problem of renaming of binding variables in the
   induction schemes.  When the goal being induced upon contains bound
   variables of the same name as those which happen to appear in the
   induction scheme, those variables (in the goal) are renamed to
   avoid capture.  The meta-level does not know about such goings-on
   and so the result is that the induction sub-goals are out by alpha
   conversion.   End result is that Clam's variable names are all
   wrong.  rename_hyp simply ensures that all variable names in the
   cut-in lemma are different from all those in the context/goal at
   the time of the induction, and so all substitutions are
   capture-avoiding without renaming.  */ 

do_induction([(V3:pnat)-s(V0),(V4:pnat)-s(V1)]) :-
    Lemma=pairs,
    %% WARNING: names of freevars might be out of sync with those
    %% used in the corresponding induction scheme (in schemes.pl).
    %% (correction, by ian green: the above comment still holds, but
    %% should be less of a problem with the new scheme database).
    goal(G),hyp_list(H),
    matrix(Gvars,_,G),
    append(Gvars,H,GvarsH),
    hfree([Vbase],GvarsH),			%same Vbase in each base case
    hypfree([V2,U1,U1orig,U2,U3,U4,U5,U6,U7],[V0:_,V1:_|GvarsH]), !,
    apply(lemma(Lemma,new[U1orig]) then
	  rename_hyp(U1orig,H==>G,U1) then 
    elim(U1,on(lambda(V3,lambda(V4,G))),new[U2]) then
        [try(wfftacs), 
         beta_reduce(hyp(U2)) then beta_reduce(hyp(U2)) then
            elim(U2,on(V3),new[U3]) then 
               [try wfftacs,
                elim(U3,on(V4),new[U4]) then
                  [try wfftacs,
                   elim(U4,new[U5]) then
                      [intro(new[Vbase]) then [idtac, wfftacs],   % previously idtac
                       elim(U5,new[U6]) then
                         [intro(new[Vbase]) then [idtac,wfftacs], % previously idtac
                          elim(U6,new[U7]) then
                             [intro(new[V0]) then
                               [intro(new[V1]) then
                                   [intro(new[V2]) then [idtac,try wfftacs],
                                    try wfftacs
                                   ],
                                try wfftacs
                                ],
                              try hyp(U7)
                             ]
                         ]
                      ]
                  ]
               ]
        ])
       then thin([U1,U2,U3,U4,U5,U6,U7]).

do_induction(Scheme) :-
    set_equal([(V4:int list)-V0::V1,(V3:pnat)-s(V2)],Scheme),
    Lemma=nat_list_pair,
    goal(G),hyp_list(H),
    hypfree([VIH,U1orig,U1,U2,U3,U4,U5,U6,U7],[V0:_,V1:_,V2:_|H]), !,
  apply(lemma(Lemma,new[U1orig]) then
	    rename_hyp(U1orig,H==>G,U1) then
    elim(U1,on(lambda(V3,lambda(V4,G))),new[U2]) then
        [wfftacs, 
         beta_reduce(hyp(U2)) then beta_reduce(hyp(U2)) then
            elim(U2,on(V3),new[U3]) then 
               [wfftacs,
                elim(U3,on(V4),new[U4]) then
                  [wfftacs,
                   elim(U4,new[U5]) then
                      [intro(new[V2]) then [idtac, wfftacs],  
                       elim(U5,new[U6]) then
                         [intro(new[V2]) then [idtac,wfftacs],
                          elim(U6,new[U7]) then
                             [intro(new[V2]) then
                               [intro(new[V0]) then
                                 [intro(new[V1]) then 
                                    [intro(new[VIH]) then [idtac,wfftacs],
                                     wfftacs],
                                  wfftacs],
                                wfftacs],
                              hyp(_)]]]]]])
         then thin([U1,U2,U3,U4,U5,U6,U7]).

% End of support for simultaneous induction
       

	% PRIMITIVE INDUCTION, for pnat and list:
do_induction([(X:pnat)-s(V0)]) :-
    atomic(V0),
    ground(V0),
    hyp_list(H), goal(G), matrix(Vs,_,G), append(Vs,[X:pnat|H],VsHs),
    free([V0,V2],VsHs),
    elim(X,new[V0,V2]) then try(wfftacs).
do_induction([(V:Type list)-H::T]) :-
    \+ T = (_ :: _),				% dont confuse with list_ind
    hyp_list(HypL), goal(G), matrix(Vs,_,G),
    append(Vs,[H:Type,T:Type list|HypL],VsHs),
    free([IndH],VsHs),
    elim(V,new[H,T,IndH]) then try(wfftacs).
	% PRIME-COMPOSITE INDUCTION
/* 
do_induction([(V:pnat)-times(V0,V1)]) :-
    Lemma=primec,
	% WARNING: names of freevars might be out of sync with those
	% used in the corresponding induction scheme (in schemes.pl).
    ground(V0-V1),
    goal(G), hyp_list(H),
    free([V2,V3,V4,U2,U3,U4,U5,U6,U7orig,U7,,U8],[V0:_,V1:_|H]), !,
    apply(lemma(Lemma,new[U7orig]) then
	      rename_hyp(U7orig,H==>G,U7) then 
    elim(U7,on(lambda(V,G)),new[U2]) then
        [try(wfftacs), 
         beta_reduce(hyp(U2)) then
            elim(U2,new[U3]) then 
               [idtac,
                elim(U3,new[U4]) then
		 [idtac,
		  elim(U4,new[U5]) then
                   [intro(new[V2]) then [idtac,try(wfftacs)], %idtac, 
                    elim(U5,new[U6]) then
                       [intro(new[V0]) then
                         [intro(new[V1]) then
			  [intro(new[V3]) then
			   [intro(new[V4]) then [idtac,try(wfftacs)],try(wfftacs)],
			   try(wfftacs)
			  ],
			  try(wfftacs)
			 ],
                        elim(U6,on(V),new[U8]) then [try(wfftacs),hyp(U8)]
		       ]
                   ]
		 ]
               ]
        ]) then thin([U7,U2,U3,U4,U5]).
*/
	% TWO-STEP INDUCTION on pnat:
do_induction([(V:pnat)-s(s(V0))]) :-
    Lemma=twos,
	% WARNING: names of freevars might be out of sync with those
	% used in the corresponding induction scheme (in schemes.pl).
    ground(V0),
    goal(G),hyp_list(H),free([V1,U1orig,U1,U2,U3,U4,U5,U6],[V0:dummy|H]), !,
    apply(lemma(Lemma,new[U1orig]) then
	      rename_hyp(U1orig,H==>G,U1) then 
    elim(U1,on(lambda(V,G)),new[U2]) then
        [try(wfftacs), 
         beta_reduce(hyp(U2)) then
            elim(U2,new[U3]) then 
               [idtac,
                elim(U3,new[U4]) then
                   [idtac,
                    elim(U4,new[U5]) then
                       [intro(new[V0]) then
		         [intro(new[V1]) then [idtac,try(wfftacs)],
			  try(wfftacs)
			 ],
                        elim(U5,on(V),new[U6]) then [try(wfftacs),hyp(U6)]
		       ]
                   ]
               ]
        ]) then thin([U1,U2,U3,U4]).
	% SIMPLE PRIME INDUCTION:
%/*
do_induction([(V:{posint})-times(P,V0)]) :-
    Lemma=primescheme,
	% WARNING: names of freevars might be out of sync with those
	% used in the corresponding induction scheme (in schemes.pl).
    goal(G),hyp_list(H),free([V1,U1orig,U1,U2,U3,U4,U6],[P:_,V0:_|H]), !,
    apply(lemma(Lemma,new[U1orig]) then
	      rename_hyp(U1orig,H==>G,U1) then 
    elim(U1,on(lambda(V,G)),new[U2]) then
        [try(wfftacs), 
         beta_reduce(hyp(U2)) then
            elim(U2,new[U3]) then 
               [idtac,
                elim(U3,new[U4]) then
                       [intro(new[P]) then
		        [intro(new[V0]) then
			  [intro(new[V1]) then [idtac,try(wfftacs)],
			   try(wfftacs)
			  ],
			 try(wfftacs)
			],
                        elim(U4,on(V),new[U6]) then [try(wfftacs),hyp(U6)]
		       ]
               ]
        ]) then thin([U1,U2,U3,U4]).
%*/
	% PLUS INDUCTION
do_induction([(V:pnat)-plus(V0,V1)]) :-
    Lemma=plusind,
	% WARNING: names of freevars ARE out of sync with those
	% used in the corresponding induction scheme (in schemes.pl).
    goal(G),hyp_list(H),matrix(Vs,_,G), append(Vs,H,HH),
    free([V2,V3,U1orig,U1,U2,U3,U4,U5],[V0:_,V1:_|HH]), !,
    apply(lemma(Lemma,new[U1orig]) then
	      rename_hyp(U1orig,H==>G,U1) then
    elim(U1,on(lambda(V,G)),new[U2]) then
        [try(wfftacs), 
         beta_reduce(hyp(U2)) then
            elim(U2,new[U3]) then 
               [idtac,
                elim(U3,new[U4]) then
                   [idtac,
                    elim(U4,new[U5]) then
                      [intro(new[V0]) then
		        [intro(new[V1]) then
			  [intro(new[V2]) then
			    [intro(new[V3]) then
			      [idtac,try(wfftacs)],
			       try(wfftacs)
			      ],
			   try(wfftacs)
			  ],
			 try(wfftacs)
	                ],
                       elim(U5,on(V),new[U6]) then [try(wfftacs),hyp(U6)]
                      ]
                   ]
               ]
        ]) then thin([U1,U2,U3,U4]).


do_induction([(V:T list)-V0::V1::V2]) :-
    %% T list induction with a singleton base case and access to the car
    %% and the cadr.
    Lemma=list_ind,
    goal(G),hyp_list(H),matrix(Vs,_,G), append(Vs,H,HH),
    free([V3,U1orig,U0,U1,U2,U3,U4,U5],[V0:_,V1:_,V2:_|HH]), !,
    apply(lemma(Lemma,new[U1orig]) then
	      rename_hyp(U1orig,H==>G,U0) then
	      elim(U0,on(T),new[U1]) then
	      [wfftacs,
	       elim(U1,on(lambda(V,G)),new[U2]) then
	      [try(wfftacs),
		    beta_reduce(hyp(U2)) then
			elim(U2,new[U3]) then
			[idtac,			% first base case
			 elim(U3,new[U4]) then
			     [intro(new[V0]) then [idtac,wfftacs],%second base case
			      elim(U4,new[U5]) then
				  [intro(new[V0]) then
				       [intro(new[V1]) then
					    [intro(new[V2]) then
						 [intro(new[V3]) then
						      [idtac,try(wfftacs)],
						  try(wfftacs)],
					     try(wfftacs)],
					try(wfftacs)],
				   elim(U5,on(V),new[U6]) then
				       [try(wfftacs),hyp(U6)]]]]]])
	then thin([U0,U1,U2,U3,U4]).


do_induction([(V:T tree)-node(Left,Right)]) :-
    Lemma = treeind,
    goal(G), hyp_list(H),
    matrix(Vs,_,G), append(Vs,H,HH),
    free([U1orig,U0,U00,U1,U2,U3,U4],[Left:_,Right:_|HH]), !,
    apply(lemma(Lemma,new[U1orig]) then
	      rename_hyp(U1orig,H==>G,U00) then
	      (elim(U00,on(T),new[U0])then thin([U00]))
	    then[try wfftac,
		 (elim(U0,on(lambda(V,G)),new[U1])then thin([U0]))
		     then[wfftacs,
			  beta_reduce(hyp(U1))
			      then (elim(U1,new[U2])then thin([U1])) then
			      %% DANGER: Right in the next line is the
			      %% argument of the leaf constructor: it
			      %% happens that the meta-level makes this choice!
			      [intro(new[Right])then
				   [idtac,wfftacs], % BASE CASE
			       (elim(U2,new[U3])then thin([U2])) then
				   [intro(new[Left])then
					[intro(new[Right]) then
					     [intro(new[_LeftProof]) then
						  [intro(new[_RightProof]) then
							[idtac,wfftacs],
						   wfftacs],
					      wfftacs],	% wfftacs-Right
					 wfftacs], %wfftacs-Left
				    elim(U3,on(V),new[U4]) then
					[wfftacs,hyp(U4)]]]]]).
do_induction([(V:T list)-less_length]) :-
    Lemma = less_length,
    goal(G), hyp_list(H),
    matrix(Vs,_,G), append(Vs,H,Context),
    free([L3,L0,L1,L2],Context),
    apply(lemma(Lemma,new[L0])then
		  (elim(L0,on(T),new[L1])then[wfftacs,idtac])then
		  (elim(L1,on(lambda(V,G)),new[L2])then
		       [wfftacs,
			beta_normalize(hyp(L2))])then
		  elim(L2,new[L3])then
		    [thin([V])then(intro(new[V])then[idtac,wfftacs])
			 then(intro(new[L3])then[idtac,wfftacs])then
			 idtac,
		     elim(L3,on(V),new[L4,_])
			 then[wfftacs,hyp(L4)]]).
    

/* beta_reduce/0 is a tactic that will replace any occurences of
   "lambda(_,_) of _" in the goal with the computed value for the
   lambda-expression. Beta_reduce/1 is the same, but for a designated
   hypothesis. They both call beta_reduce/2, which traverses a term
   and replaces all subterms of the form "lambda(_,_) of _" by [[1]],
   so that the result can be handed to compute.  (NB. beta_reduce(A,A)
   succeeds if A contains no redex; may want to use beta_reduce_plus
   instead.  */
beta_reduce :-
    goal(G), beta_reduce(G,G1),compute(G1).
beta_reduce(hyp(H)) :-
    hypothesis(H:Hyp),beta_reduce(Hyp,Hyp1),compute(hyp(H),Hyp1).
beta_reduce(lambda(_,_) of _, [[1]]) :- !.
beta_reduce([],[]) :- !.
beta_reduce([H|T],[H1|T1]) :- beta_reduce(H,H1),beta_reduce(T,T1).
beta_reduce(T,T) :- atomic(T),!.
beta_reduce(T1,T2) :- T1=..T1List, beta_reduce(T1List,T2List),T2=..T2List.


/* Apply a computation rule in the goal/hyps.  Can be used to unfold
   definitions of the form Def(...) <==> term_of(...)  of ... */

unfold_iff :-
    unfold_def_all(_ <=> _).
unfold_def_all(Term) :-
    repeat unfold_def(Term).

unfold_def(Term) :-
    unfold_def(Term,_).

unfold_def(Term,Pos) :-
    goal(G), 
    exp_at(G,Pos,Term),!,
    Term =.. [_F|Args],
    length(Args,N),
    expand_term_of_tag(N,[[expand]],TermOfExpandTag),
    replace(Pos,[[unfold]],G,UnfoldTag),
    replace(Pos,TermOfExpandTag,G,ExpandTag),
    apply(compute(UnfoldTag) then
	      try (compute(ExpandTag) then
		   repeat beta_reduce_plus_pos(Pos))).

fold_def(Term,Target) :-
    apply(fold_def(Term,Target,_Pos)).

fold_def(Term,Target,Pos) :-
    %% too hard to work backwards towards a fold, so cut in a separate
    %% proof, and unfold that.  Alas, Target must be a ground term
    %% (guessing parameters is too hard in practice, and impossible in
    %% general).  
    ground(Target),
    Target =.. [F|_Args],
    definition(F/_ <==> _),
    %% we need to show that RHS\sigma UNfolds to Term!
    goal(G), hyp_list(H),
    exp_at(G,Pos,Term),!,
    guess_type(Term,H,Type),
    replace(Pos,Z,G,OverTerm),
    %% pick a Z not in G/H; do not instantiate any vars in G/H!
    make_ground_term(Z,G-H),
    apply(subst(over(Z,OverTerm),Term=Target in Type) then
	      [ unfold_def(Target,[2,1])	% unfold Target
		    then identity,
		idtac,				% remainder of G
		wfftacs]).


unfold_def(hyp(H),Term,Pos) :-
    hypothesis(H:G), 
    exp_at(G,Pos,Term),!,
    Term =.. [_|Args],
    length(Args,N),
    expand_term_of_tag(N,[[expand]],TermOfExpandTag),
    replace(Pos,[[unfold]],G,UnfoldTag),
    replace(Pos,TermOfExpandTag,G,ExpandTag),
    apply(compute(hyp(H),UnfoldTag) then
	      try (compute(hyp(H),ExpandTag) then
	           repeat beta_reduce_plus_pos(hyp(H),Pos))).

expand_term_of_tag(0,T,T) :- !.			% for nullary constants
expand_term_of_tag(1,T,T of _) :- !.
expand_term_of_tag(N,T,TagNN of _) :-
    NN is N - 1,
    expand_term_of_tag(NN,T,TagNN).

/* unwrap term_of terms */    
expand_termof :-					
    goal(G), expand_termof(G,G1),!,\+(G=G1),compute(G1).
expand_termof(hyp(H)) :-
    hypothesis(H:Hyp),expand_termof(Hyp,Hyp1),compute(hyp(H),Hyp1).
expand_termof(term_of(_), [[expand]]) :- !.
expand_termof([],[]) :- !.
expand_termof([H|T],[H1|T1]) :- expand_termof(H,H1),expand_termof(T,T1).
expand_termof(T,T) :- atomic(T),!.
expand_termof(T1,T2) :- T1=..T1List, expand_termof(T1List,T2List),T2=..T2List.

expand_termof_reduce :- expand_termof then repeat beta_reduce_plus.

/* try to normalize a term */
beta_normalize :- repeat beta_reduce_plus.
beta_normalize(hyp(H)) :- repeat beta_reduce_plus(hyp(H)).

beta_normalized_term(U,W) :-
    beta_normalized_term_(U,V),
    (U == V -> W = V; beta_normalized_term(V,W)).

beta_normalized_term_(A,A) :- atomic(A),!.
beta_normalized_term_(lambda(~,T) of _,T) :- !.
beta_normalized_term_(lambda(V,T) of U,TUU) :-
    s(T,[U],[V],TU),!,
    beta_normalized_term_(TU,TUU).
beta_normalized_term_(T,U) :-
    T =.. [F|As],
    map_list(As,A:=>B,beta_normalized_term_(A,B),Bs),
    U =.. [F|Bs].


/* Like beta-reduce, but fail if there are no redices.  this means
   that repeat beta-reduce will terminate, if the term does. */
beta_reduce_plus :-
    goal(G),
    beta_reduce_plus(G,G1),
    compute(G1).
beta_reduce_plus_pos(Pos) :-  % reduce beneath Pos only
    goal(GG), 
    exp_at(GG,Pos,G),
    beta_reduce_plus(G,G1),
    replace(Pos, G1, GG, Gtag),
    compute(Gtag).
beta_reduce_plus_pos(hyp(H),Pos) :-  % reduce beneath Pos only
    hypothesis(H:GG), 
    exp_at(GG,Pos,G),
    beta_reduce_plus(G,G1),
    replace(Pos, G1, GG, Gtag),
    compute(hyp(H),Gtag).

beta_reduce_plus(hyp(H)) :-
    hypothesis(H:Hyp),
    beta_reduce_plus(Hyp,Hyp1),
    compute(hyp(H),Hyp1).

beta_reduce_plus(A,B) :-
    beta_reduce(A,B),!,
    \+ (A=B).

/*
 * Code for messing around with quantifiers:
 *
 * All this messing around with quantifiers greatly adds to the
 * complexity of the extract term. However, a few small extentions to
 * the evaluation mechanism allow all this extra complexity to be
 * removed by partially evaluating the extract term. The following
 * changes to the evaluation code of Oyster does the trick:
 * [1] add after the clauses for eval(lambda):
 *     eval(lambda(X,B),lambda(XX,BB)) :- eval(X,XX),eval(B,BB).
 * [2] change the clause for eval(p_ind) into:
 *     eval(p_ind(N,S,[X,Y,T]),C):-
 *        eval(N,NN), 
 *        (NN=0,eval(S,C);
 *         NN=s(A),eval(T,[A,p_ind(A,S,[X,Y,T])],[X,Y],C);
 *         evalcond(Y,T,TT),eval(S,SS),
 *         (\+ appears(X,TT), \+ appears(Y,TT), convertible(SS,TT)
 *          -> C = SS
 *          ; C=p_ind(NN,SS,[X,Y,TT])
 *         )
 *        ),!.
 * [3] change the clauses for evalcond/3 to:
 *     evalcond(V,T,TT) :- eval(T,TT).
 */

/*
 * Follows a whole bunch of de/re-quantifying predicates:
 * quantifier_to_front/1 moves the give variable to the front of the
 * 	quanitified vars in the goal.
 * dequantify/0 removes all universally quantified variables from the
 * 	goal, retaining their names.
 * dequantify/1 removes only the given universally quantified variables
 * 	from the goal, retaining their names where possible.
 * dequantify/2 removes only the given universally quantified variables
 * 	from the goal, but not retaining their names, and returning the
 * 	new names.
 * dequantify_all/2 removes all universally quantified variables from
 * 	the goal, but not retaining their names, and returning the new
 * 	names.
 * requantify/2 sticks in the given universally quantified variables as
 * 	the given names (inverse of dequantify_all/2).
 */

quantifier_to_front(Var:Type) :- goal(Var:Type=>_),!.
quantifier_to_front(Var:Type) :- hypothesis(Var:Type),!.
quantifier_to_front(Var:Type) :-
    dequantify_all(Vars,Frees)
        then (nth1(N,Vars,Var:Type,RestVars),
	      nth1(N,Frees,FreeVar,RestFrees),
	      requantify([Var:Type|RestVars],[FreeVar|RestFrees])).

dequantify_once(at(U)) :-
    goal(_:_=>_),
    intro(at(U)) then [idtac,try(wfftacs)].

dequantify :- repeat dequantify_once.
dequantify_once :- goal(_:_=>_), intro then [idtac,try(wfftacs)].

dequantify(at(U)) :-
    repeat dequantify_once(at(U)).
dequantify([]).
dequantify([Var:Type|Rest]) :-
    goal(Var:Type=>_), !,
    dequantify_once then dequantify(Rest).
dequantify([Var:Type|Rest]) :-
    quantifier_to_front(Var:Type)
       then dequantify([Var:Type|Rest]).

dequantify([],[]).
dequantify([Var:Type|Vars],[Free|Frees]) :-
    goal(Var:Type=>_), !,
    genvar_and_check(Free),
    intro(new[Free])
        then [dequantify(Vars,Frees),
	      try(wfftacs)].
dequantify([Var:Type|Vars],[Free|Frees]) :-
    quantifier_to_front(Var:Type)
        then dequantify([Var:Type|Vars],[Free|Frees]).    

dequantify_all(Vars,Frees) :-
    goal(G), matrix(Vars,_,G),
    dequantify(Vars,Frees).



requantify([],[]) :- !.
requantify(Vars,Frees) :-
    goal(G), untype(Vars,Vs), s(G,Vs,Frees,NewG), quantify(Vars,NewG,QNewG),
    hyp_list(H), free([Seq],H),
    seq(QNewG,new[Seq])
        then [thin(Frees),
	      elim_on(Seq,Frees,Last)
	          then hyp(Last)
	     ].

	% istrue/0: true is defined as int (in u(1)).
	% Used in elementary code.
istrue :- compute([[unfold]]) then intro(0).

	% clam_arith/1.
	% Simulate the bare bones of what one would expect Oyster's
	% arith to do.
clam_arith(N:s(X)=0 in pnat) :- 
        check_lemma_present(arith1),
        strip_meta_annotations(X,XX),
        apply(lemma(arith1,new[New])) 
           then elim(New,on(XX),new[Con])
             then [wfftacs,
                   elim(Con,new[Void])
                       then [hyp(N),
                             elim(Void)]].
 
clam_arith(_:0=s(X) in pnat) :-  
        check_lemma_present(arith1),
        strip_meta_annotations(X,XX),
        apply(lemma(arith1,new[New])) 
           then elim(New,on(XX),new[Con])
             then [wfftacs,
                   elim(Con,new[Void])
                       then [equality then wfftacs,
                             elim(Void)]].
clam_arith(N:s(X)=X in pnat) :-  
        check_lemma_present(arith2),
        strip_meta_annotations(X,XX),
        apply(lemma(arith2,new[New])) 
           then elim(New,on(XX),new[Con])
             then [wfftacs,
                   elim(Con,new[Void])
                       then [hyp(N),
                             elim(Void)]].
clam_arith(_:X=s(X) in pnat) :-  
        check_lemma_present(arith2),
         strip_meta_annotations(X,XX),
       apply(lemma(arith2,new[New])) 
           then elim(New,on(XX),new[Con])
             then [wfftacs,
                   elim(Con,new[Void])
                       then [equality then wfftacs,
                             elim(Void)]].
clam_arith(N:H::T=nil in L list) :- 
        check_lemma_present(list1),
        strip_meta_annotations(H::T,HH::TT),
        apply(lemma(list1,new[New])) 
           then elim_on(New,[L,HH,TT],Last)
             then elim(Last,new[Void])
                          then [hyp(N),
                                elim(Void)].
clam_arith(_:nil=H::T in L list) :- 
        check_lemma_present(list1),
        strip_meta_annotations(H::T,HH::TT),
        apply(lemma(list1,new[New])) 
           then elim_on(New,[L,HH,TT],Last)
             then elim(Last,new[Void])
                          then [equality then wfftacs,
                                elim(Void)].
clam_arith(_:X<*s(X)) :- 
        check_lemma_present(plesssucc),
        strip_meta_annotations(X,XX),
        apply(lemma(plesssucc,new[New])) 
           then (elim(New,on(XX),new[Inst]) then thin([New]))
             then [try wfftacs,
		   hyp(Inst)].
clam_arith(_:X<*s(s(X))) :- 
        check_lemma_present(plesssucc2),
        strip_meta_annotations(X,XX),
        apply(lemma(plesssucc2,new[New])) 
           then (elim(New,on(XX),new[Inst]) then thin([New]))
             then [try wfftacs,
		   hyp(Inst)].
/*
clam_arith(_:X<*X) :- 
        check_lemma_present(arith4),
        strip_meta_annotations(X,XX),
        apply(lemma(arith4,new[New])) 
           then (elim(New,on(XX),new[Inst]) then thin([New]))
             then [try wfftacs,
		   hyp(Inst)].
*/
clam_arith(V:X<*0) :-
        check_lemma_present(arith3),
        strip_meta_annotations(X,XX),
        apply(lemma(arith3,new[New])) 
           then (elim(New,on(XX),new[Inst]) then thin([New]))
             then [try wfftacs,
		   (elim(Inst,new[Inst2]) then thin([Inst]))
		       then [hyp(V),
			     elim(Inst2)]].
clam_arith(N:s(L)=s(R) in pnat) :-
    hyp_list(H),
    check_lemma_present(cnc_s_bis),
    hfree([L2,L1],H),
    apply(lemma(cnc_s_bis,new[L1])then (elim(L1,on(L),new[L2])then thin([L1])then wfftacs)then (elim(L2,on(R),new[L1])then thin([L2])then wfftacs)then (elim(L1,new[L2])then thin([L1]))then[hyp(N),idtac]).

check_lemma_present(L) :-  lib_present(lemma(L)) -> true
                         ; clam_warning('lemma %t should be loaded.\n',[L]),
                           fail.

/*
 * EXISTENTIAL TACTIC:
 *
 * copes with existential quantifier inside universal,
 * but not inside existential
 *
 */

existential(V:T,Value) :- goal(V:T#_),
    apply(intro(Value) then [try(wfftacs),apply(idtac),try(wfftacs)]).
existential(_,Value) :- goal(_:_=>_),
    dequantify_all(Vars_and_Types,Frees) then
        (untype(Vars_and_Types,Vars),
	 s(Value,Frees,Vars,NewValue),
	 existential(_,NewValue)) then
    requantify(Vars_and_Types,Frees).


/*
 * WAVE TACTIC:
 */

%% first, hack to cope with disparity of pos when goal \exists quantified
%% adjustpos(Pos,_:_=>Rest,Newpos):- adjustpos(Pos,Rest,PP),
%%                                   append(PP,[2,2],Newpos),!.
adjustpos(Pos,_:_#Rest,Newpos):- adjustpos(Pos,Rest,PP),
                                 append(PP,[2,2],Newpos),!.
adjustpos(Pos,_,Pos).


wave(Pos,[Rule,Dir]) :- goal(_:_#Rest),
			adjustpos(Pos,_:_#Rest,Newpos),
		        rewrite_at_pos(_,Newpos,Rule,Dir).
wave(Pos,[Rule,Dir]) :-
    dequantify_all(Vars,Frees)
       then rewrite_at_pos(_,Pos,Rule,Dir)
          then requantify(Vars,Frees).
        % Could have done these two also by stating rhs in tactic slot
        % of method:
wave(Pos,split(Rule,Dir)) :- wave(Pos,[Rule,Dir]),!.
wave(Pos,join(Rule,Dir))  :- wave(Pos,[Rule,Dir]),!.
wave(A,B) :- fail_tac(wave(A,B)).

/* case for complementary tag on wave */
wave(Kind,Pos,[Rule,complementary,Dir],S) :-
    wave(Kind,Pos,[Rule,Dir],S).
wave(_Kind,Pos,[Rule,Dir],[]) :- 
     dequantify_all(Vars,Frees) 
       then wave(Pos,[Rule,Dir])
	  then requantify(Vars,Frees).
wave(_,Pos,[Rule,Dir],Wit):-
    wave_(Pos,[Rule,Dir],Wit).
wave(A,B,C,D) :- fail_tac(wave(A,B,C,D)).
wave(Pos,split(Rule,Dir),SubstL):-
	wave(Pos,[Rule,Dir],SubstL).
wave(Pos,join(Rule,Dir),SubstL):-
	wave(Pos,[Rule,Dir],SubstL).
wave(_,ident,_) :- apply(idtac).

wave(A,B,C) :- fail_tac(wave(A,B,C)).

wave_(Pos,[Rule,Dir],[]) :-
	wave(Pos,[Rule,Dir]).
% next for \exist ripples (just one \exists for moment)
% must be generalised (needs unification and not just matching)
wave_(Pos,[Rule,imp(_)],[_:_,Witness]) :-
     theorem(Rule,Statement,_),
     goal(U:_=>V:T#V=R in Type),
     dequantify_once,hyp_list(HL),
     hyp(_IH:U:_, HL),
     instantiate(HL,Statement,_=RR in _=>_=R in _,_),
     hyp_list(HL),free([New1,New2],HL),
     dequantify_once then
        seq(V:T#V=RR in Type,new[exhyp]) then
          [idtac,
           elim(exhyp,new[New1,New2,_]) then intro(Witness) then try wfftacs
              then wave(Pos,[Rule,imp(_)]) then hyp(New2)
       ].
wave_(Pos,[Rule,imp(_)],[_:_,Witness]) :-
     theorem(Rule,Statement,_),
     goal(V:T#V=R in Type), hyp_list(HL),
     instantiate(HL,Statement,_=RR in _=>_=R in _,_),
    free([New1,New2],HL),
     seq(V:T#V=RR in Type,new[exhyp]) then
       [idtac,
        elim(exhyp,new[New1,New2,_]) then intro(Witness) then try wfftacs
        then wave(Pos,[Rule,imp(_)]) then hyp(New2)
       ].
wave_(Pos,[Rule,imp(_)],[_:_,Witness]) :-
    theorem(Rule,Statement,_),
    goal(V:_#VV:TT#LG=RG in Type), s(LG,[_],[V],NewLG),
    hyp_list(HL),
    instantiate(HL,Statement,LL=RR in _=>NewLG=RG in _,_),
    seq(VV:TT#LL=RR in Type,new[exhyp])
	then [idtac,
	      intro(Witness) then try wfftacs
		  then wave(Pos,[Rule,imp(_)]) then try hyp(_)].
wave_(Pos,[Rule,imp(_)],[_:_,Witness]) :-
    theorem(Rule,Statement,_),
    goal(V:T#LG=RG in Type),      hyp_list(HL),
    instantiate(HL,Statement,_LL=RR in _=>_=RG in _,_),
    free([New1,New2],HL),
    seq(V:T#LG=RR in Type,new[exhyp])
	then [idtac,
	      elim(exhyp,new[New1,New2,_]) then intro(Witness) then try wfftacs
		  then wave(Pos,[Rule,imp(_)]) then try hyp(New2) ].
wave_(Pos,[Rule,equ(_,left)],[_:WType,Witness]) :-
    theorem(Rule,Statement,_),
    goal(_:_#_=GR in Type),      hyp_list(HL),
    instantiate(HL,Statement,L=R in _,_),
    L=..[_,Witness],
    freevarsinterm(Witness,Newvars),
    ex_close(Newvars,WType,Witness,R=GR in Type,Seqwff),
    free([New1,New2,New3,New4,New5,New6],HL),
     seq(Seqwff,new[exhyp])
     then [idtac,
           elim(exhyp,new[New1,New3,New4]) then try wfftacs then
           elim(New3,new[New2,New5,New6]) then try wfftacs then
             intro(Witness) then 
                [try wfftacs,
		 wave(Pos,[Rule,equ(_,left)]) then try hyp(New5),
                 try wfftacs
                ]
          ].


% construct existential closure of formula wrt var/type list
% first, get types of vars
find_type(Var,Var,WType,WType).
find_type(Var,Var::_,WType list,WType).
find_type(Var,_::Var,WType,WType).
ex_close([],_,_,Wff,Wff).
ex_close([Var|T],WType,Witness,Inwff,Var:Type#Wff):-
         find_type(Var,Witness,WType,Type),
         ex_close(T,WType,Witness,Inwff,Wff).


/* GENERALISE TACTIC: */
generalise(Exp,V:Type) :-
    goal(G), hyp_list(H),free([Seq],H),
    s(G,[V],[Exp],Gengoal),
    seq(V:Type=>Gengoal,new[Seq])
        then [idtac, 
	      dequantify_all(Vars,Frees)
	       then (untype(Vars,Vs),s(Exp,Frees,Vs,NewExp),
	          elim_on(Seq,[NewExp|Frees],NewHyp)) then hyp(NewHyp)  
             ],!.
generalise(A,B) :- fail_tac(generalise(A,B)).

/* EQUALITY TACTIC: */
equal(Hyp,right) :- rewrite(Hyp) then thin([Hyp]),!.
equal(Hyp,left) :- hypothesis(Hyp:X=Y in T), 
                   rewrite(Y=X in T) then thin([Hyp]),!.
equal(A,B) :- fail_tac(equal(A,B)).

/* EVAL_DEF TACTIC: */
eval_def(Pos,RuleDir) :- 
    wave(Pos,RuleDir).
eval_def(A,B) :- fail_tac(eval_def(A,B)).

/* REDUCTION TACTIC: */
reduction(Pos,RuleDir) :- wave(Pos,RuleDir). 
reduction(A,B) :- fail_tac(reduction(A,B)).

normalize_term(cancel(Pos,A,B)) :-			% unary f
    goal(G),
    matrix(Vars,_,G),
    matrix(Vars,B=>A,Seq),
    polarity_compatible(G,Pos,imp(right)),
    apply((seq(Seq,new[L])
	      then [repeat intro then wfftacs,		% enough for constructors?
		    dequantify_all(Vars,Frees) then
			rewrite_at_pos(Frees,Pos,L,imp(right)) then
			   requantify(Vars,Frees)])then thin([L])),!.

normalize_term(TacList) :-
    is_list(TacList),
    list_to_tactic(TacList,Tac),
    apply(Tac),!.
normalize_term(A) :- fail_tac(normalize_term(A)).

/* UNBLOCK: */
unblock(meta_ripple,_,_) :- apply(idtac),!.
unblock(weaken,_,_) :- apply(idtac),!.
unblock(sink,P,RuleDir)  :- wave(P,RuleDir),!.
unblock(wave_front,P,RuleDir)  :- wave(P,RuleDir),!.
unblock(reduction,P,RuleDir) :- wave(P,RuleDir),!.
unblock(A,B,C) :- fail_tac(unblock(A,B,C)).

/* UNBLOCK THEN WAVE */
unblock_then_wave(_,Tac) :-
    apply(Tac),!.
unblock_then_wave(A,B) :- fail_tac(unblock_then_wave(A,B)).

/* UNBLOCK THEN WAVE */
unblock_then_fertilize(_,Tac) :-
    apply(Tac),!.
unblock_then_fertilize(A,B) :- fail_tac(unblock_then_fertilize(A,B)).

/* RIPPLE TACTIC: */
ripple(_,R) :- apply(R),!.
ripple(A,B) :- fail_tac(ripple(A,B)).

ripple(R) :- apply(R),!.
ripple(A) :- fail_tac(ripple(A)).

/* Fertilize TACTIC: */
fertilize(strong,Plan):- dequantify then apply(Plan),!.
fertilize(weak,Plan):- apply(Plan),!.
fertilize(A,B) :- fail_tac(fertilize(A,B)).

pw_fertilize(Plan) :- apply(Plan).
pwf(i_fert(imp,VV,V,W)) :-
    intro(new[V]) then
       [elim(VV,new[W]) then wfftacs,wfftacs].
pwf(i_fert('\\',VV,V1,V2)) :-
    (	(elim(VV,new[V1,V2,N1,N2]) then thin([N1,N2]))
         then [intro(left) then [idtac,wfftacs], intro(right) then [idtac,wfftacs]]).
pwf(i_fert('#',VV,V1,V2)) :-
    (	(elim(VV,new[V1,V2,N1]) then thin([N1]))
         then intro).
pwf(and_i_cfert) :- intro. % then try wfftacs. ??
pwf(or_i_fert(left)) :- intro(left) then [idtac,wfftacs].
pwf(or_i_fert(right)) :- intro(right) then [idtac,wfftacs].
pwf(and_e_fert(left,VV,V)) :- elim(VV,new[V,VB,W]) then thin([VB,W]).
pwf(and_e_fert(right,VV,V)) :- elim(VV,new[VB,V,W]) then thin([VB,W]).
pwf(imp_ir_fert) :- intro(new[Y]) then [thin([Y]),wfftacs].
pwf(imp_e_fert(VV,V)) :- elim(VV,new[V]) then [idtac,wfftacs].

pwf_then_fertilize(_,Plan) :- apply(Plan).

/* alpha convertible */
fertilization_strong(X) :- \+ is_list(X),hyp(X). %, !. %% former cut here???
/* instance */
fertilization_strong(X) :-
    \+ is_list(X),
    goal(G),hyp_list(HL),
    hypothesis(X:H),
    instantiate(HL,H,G,Vals),
    elim_on(X,Vals) then hyp(_),!.
/* multiple s.f.'s */
fertilization_strong([]).
fertilization_strong([X-Pos|Xs]) :-
    hypothesis(X:Xt),
    apply((seq(Xt<=>{true},new [L]) then
           [propositional,
	    (rewrite_at_pos([],Pos,L,equiv(left)) then thin([L]))]) then
	  fertilization_strong(Xs)).


fertilization_strong(A) :- fail_tac(fertilization_strong(A)).

strong_fertilize(X) :- hyp(X), !.
strong_fertilize(X) :- goal(G),hypothesis(X:H),
    hyp_list(HL),
    instantiate(HL,H,G,Vals),
    elim_on(X,Vals) then hyp(_),!.
strong_fertilize(A) :- fail_tac(strong_fertilize(A)).

fertilization_weak(M) :- apply(M),!.
fertilization_weak(A) :- fail_tac(fertilization_weak(A)).

fertilize_then_ripple(M):- apply(M),!.
fertilize_then_ripple(A) :- fail_tac(fertilize_then_ripple(A)).

:- dynamic fertilize_left_or_right/1.
fertilize_left_or_right(Ms):- apply_list(Ms),!.
fertilize_left_or_right(A) :- fail_tac(fertilize_left_or_right(A)).

:- dynamic ripple_and_cancel/1.
ripple_and_cancel(M) :- apply_list(M),!.
ripple_and_cancel(A) :- fail_tac(ripple_and_cancel(A)).

weak_fertilize(_,Ms) :- apply_list(Ms),!.
weak_fertilize(A,B) :- fail_tac(weak_fertilize(A,B)).

apply_list([]).
apply_list([H|T]) :- apply(H) then apply_list(T).
	% weak_fertilize/4: first clause deals with fertilization on
	% equalities, and just uses rewrite rules.
	% The second clause etc, do generalised weak fertilization for
	% transitive connectives.
weak_fertilize(Dir,(in),P,H) :- 
    (Dir = right
     -> append(P,[2,1],Pos)
     ;  (Dir=left,append(P,[1,1],Pos))
    ),

    %% To keep the method and the tactic aligned in terms of variable
    %% names, weak_fertiliztion requires the Frees to be passed down
    %% into rewrite_at_pos.  This allows the tactic to replicate the
    %% `skeleton preservation' property that might be exploited later
    %% in the plan.  For example, in weak fertilizing the sequent:
    %%
    %% v0:t, x:tt=>p(x,v0)=q(v0) ==> x:tt=p'(x,v0)=q(v0) 
    %%

    %% the hyp is not a proper rewrite (since x does not appear on
    %% rhs).  However, smthd(weak_fertilize/4) assumes that the
    %% variable name in the resulting requantified goal is the same as
    %% the bound variable in the hypothesis (read: Clam is brain-dead
    %% alpha-convertability wise!).  So continuing the example, we get
    %% goal x:tt=p'(x,v0)=p(x,v0) and not x:tt=p'(x,v0)=p(xx,v0)
    %% (where xx is something of type tt that happens to be lying in
    %% the context).  So far, this has not been implemented for =>
    dequantify_all(Vars,Frees)
       then rewrite_at_pos(Frees,Pos,H,equ(_,Dir))
          then requantify(Vars,Frees),!.
weak_fertilize(Dir,C,OldinS,H) :-
    C \= (in), !,
    dequantify_all(Vars,Frees)
      then do_weak_fertilize(Frees,Dir,C,OldinS,H)
        then requantify(Vars,Frees).
weak_fertilize(A,B,C,D) :- fail_tac(weak_fertilize(A,B,C,D)).

% first, a hack to deal with => case -
% propositional can take forever if there is other prop structure
% around, and mono and trans are redundant if prop is used anyway.
% Whole tactic should be rationalised.
do_weak_fertilize(Frees,D,=>,OldinS,H) :- !,
    hyp_list(Hl), hypothesis(H:Hyp), goal(G),
    free([NewH1],Hl),
    (  D=right->(XinG=[1], SinG=[2], ElimL1=[X,SofNew,S],ElimL2=[New,Old])
    ; (D=left,   XinG=[2], SinG=[1], ElimL1=[S,SofNew,X],ElimL2=[Old,New])),
    	% Figure out Old (the term to be replaced),
	%            S   (the term wrapping Old),
	%            X   (the term to remain the same):
    append(OldinS,SinG,OldinG),
    exp_at(G,OldinG,Old),
    exp_at(G,SinG,S), 
    exp_at(G,XinG,X), 
	% Figure out New (the term to replace Old), by matching with the
	% fertilizing hypothesis:
    Inst=..[=>,_,_],exp_at(Inst,XinG,New),exp_at(Inst,SinG,Old),
    instantiate(Hl,Frees,Hyp,Inst,Vals),
    	% Figure out the new goal (old goal with Old replaced by New)
    replace(OldinG,New,G,NewG),
        % Figure out the new version of the wrapping term (old wrapping term
	% with Old replaced by New).
    replace(OldinS,New,S,SofNew), % should be the same as
				  % exp_at(NewG,SinG,SofNew)
            seq(NewG,new[NewH1])
	      then [idtac,
                    elim_on(H,Vals) then (propositional or elementary) then
			wfftacs
	           ].
do_weak_fertilize(Frees,D,C,OldinS,H) :-
    hyp_list(Hl), hypothesis(H:Hyp), goal(G),
    free([U,V,W,TransH,MonotonH,NewH1],Hl),
    	% Guess type of arguments of C. Both args must be the same type:
	% guess type is not very good with propositions, so we cheat.
	% (We may have to cheat more here in the future (e.g. #?)).
    (C = (=>)
     -> T=u(1)
     ; CF =.. [C,F1,F2], exp_at(G,_,CF),
     guess_type(F1,Hl,T),
     guess_type(F2,Hl,T)),
    	% Construct transitivity axiom for C:
    CUV=..[C,U,V],CVW=..[C,V,W],CUW=..[C,U,W],
    Trans=(U:T=>V:T=>W:T=>(CUV#CVW)=>CUW),
    	% Instantiate position specifiers dependend on direction of
	% fertilization:
    (  D=right->(XinG=[1], SinG=[2], ElimL1=[X,SofNew,S],ElimL2=[New,Old])
    ; (D=left,   XinG=[2], SinG=[1], ElimL1=[S,SofNew,X],ElimL2=[Old,New])),
    	% Figure out Old (the term to be replaced),
	%            S   (the term wrapping Old),
	%            X   (the term to remain the same):
    append(OldinS,SinG,OldinG),
    exp_at(G,OldinG,Old),
    exp_at(G,SinG,S), 
    exp_at(G,XinG,X), 
	% Figure out New (the term to replace Old), by matching with the
	% fertilizing hypothesis:
    Inst=..[C,_,_],exp_at(Inst,XinG,New),exp_at(Inst,SinG,Old),
    instantiate(Hl,Frees,Hyp,Inst,Vals),
    	% Figure out the new goal (old goal with Old replaced by New)
    replace(OldinG,New,G,NewG),
        % Figure out the new version of the wrapping term (old wrapping term
	% with Old replaced by New).
    replace(OldinS,New,S,SofNew), % should be the same as
				  % exp_at(NewG,SinG,SofNew)
	% Construct monotonicity axiom for wrapping term:
    replace(OldinS,n,S,Sn), replace(OldinS,m,S,Sm),
    Cnm=..[C,n,m], CSnSm=..[C,Sn,Sm],
    Monoton=(n:T=>m:T=>Cnm=>CSnSm),
    	% and off we go:
	% sequence in transitivity and monotonicity,
	% and do appropriate eliminations.
    seq(Trans,new[TransH])
      then [prove_trans(C),
            seq(NewG,new[NewH1])
	      then [thin([TransH,NewH1]),
	            seq(Monoton,new[MonotonH])
		      then [prove_monoton(C,OldinS),
		            elim_on(H,Vals)
			      then elim_on(TransH,ElimL1)
			         then elim_on(MonotonH,ElimL2)
				   then (elementary or propositional)
		           ]
	           ]
           ].
	% prove transitivity and monotonicity when we can, otherwise
	% prove by intimidation:
prove_trans((=>)) :- !, dequantify then (elementary or propositional).
prove_trans(C) :-
    apply(apply_lemma(_)) -> true
  ; clam_warning('proving transitivity of %t by intimidation.\n',[C]),
    apply(because).
prove_monoton((=>),_) :-  !, dequantify then (elementary or propositional).
prove_monoton(_,[]) :- !, dequantify then (elementary or propositional).
prove_monoton(_,_) :-
    goal(G),matrix(_,M,G),
    clam_warning('proving monotonicity by intimidation: %t.\n',[M]),
    apply(because).

/*
 * CASE SPLIT METHOD:
 */


/* as it stands will go wrong when dequantified var already occurs
   in hyp list - the method needs to take account of this too       */
cases(X) :- casesplit(X).

casesplit(disjunction(Conds)) :-
    goal(G), matrix(Vars,_,G),
    listof(V:T,P^(member(V:T,Vars),exp_at(Conds,P,V)),BoundVars),
    hyp_list(H), append(BoundVars,H,AllH),free([H1,H2],AllH),
    list2disj(Conds,Disj),
    apply(dequantify(BoundVars) 
	      then seq(Disj,new[H2])
	      then [(elementary or apply_lemma(_)),
		    elim_disj(H2,H1) ])
	orelse (print('Could not prove casesplit: '),
		print(Conds),nl,fail),!.

casesplit(datatype([V:pnat,s(VV)])) :-
    goal(G), matrix(Vars,_,G),
    member(V:pnat,Vars),!,
    apply(dequantify([V:pnat]) then casesplit(datatype([V:pnat,s(VV)]))).

casesplit(datatype([V:pnat,s(VV)])) :-
    /* Casesplit on variable V of (recursive) type T */
    hyp_list(H),
    hfree([L2,L],[VV:dummy|H]),
    apply((decide(V=0 in pnat,new [L]) then wfftacs) then
	      [rewrite(L) then thin([L]),
	       expand_s(V,VV) then thin([L,L2])]),!.
casesplit(datatype(nothin([V:pnat,s(VV)]))) :-
    goal(G), matrix(Vars,_,G),
    member(V:pnat,Vars),!,
    apply(dequantify([V:pnat]) then casesplit(datatype(nothin([V:pnat,s(VV)])))).

casesplit(datatype(nothin([V:pnat,s(VV)]))) :-
    /* Casesplit on variable V of (recursive) type T */
    hyp_list(H),
    hfree([L2,L],[VV:dummy|H]),
    apply((decide(V=0 in pnat,new [L]) then wfftacs) then
	      [rewrite(L) then thin([L]),
	       expand_s_nothin(V,VV) then thin([L,L2])]),!.
casesplit(datatypef(I)) :- casesplit(datatype(I)).
casesplit(A) :- fail_tac(casesplit(A)).


	% eliminate an n-ary disjunction in hypothesis Hyp. The eventual
	% subnodes will all have one disjunct in hypothesis FinalHyp.
	% This silly messing around with hyp-names to get them in sync
	% with the methods (as in the base-clause below) sometimes just
	% drives me nuts!! 
elim_disj(Hyp,FinalHyp) :-
    hypothesis(Hyp:H), H\=(_\_),!,
    seq(H,new[FinalHyp]) then [hyp(Hyp), thin([Hyp])].
elim_disj(Hyp,FinalHyp) :-
    hyp_list(H), free([H1,H2,H3,H4],[FinalHyp:dummy|H]),
    elim(Hyp,new[H1,H2,H3,H4])
      then [thin([H3,Hyp]) then elim_disj(H1,FinalHyp),
            thin([H4,Hyp]) then elim_disj(H2,FinalHyp)
	   ].



% SYM_EVAL TACTIC

        % elememtary(+Tactic) is a dummy predicate to apply the Tactic
        % computed by elementary/2, since we want a predicate with the same
        % name as the method, for convenience. We also mop up any
        % wff-leftovers.
elementary(FT) :-
    \+ var(FT),
    FT = fertilize(Hyp),!,
    dequantify then fertilization_strong(Hyp).

elementary(Tactic) :- \+ var(Tactic), apply(Tactic) then try(wfftacs),!.
        % elementary/0 just spots the tautology and proves it.
        % Sometimes useful in other tactics.
elementary(A) :- fail_tac(elementary(A)).

elementary :- hyp_list(Ht), goal(Gt), elementary(Ht==>Gt,I), apply(I).

identity:- equality then try wfftacs,!.
identity :- fail_tac(identity).

identity_equiv:- intro_iff then [repeat intro,repeat intro],!.
identity_equiv :- fail_tac(identity_equiv).

contradiction :- 
    goal(_=>void),
    intro(new [V]) then [wfftacs,contradiction(V)].
contradiction(V) :-
    hypothesis(V:A=B in pnat),
    /* A and B are differnt constant terms */
    strip_ses(V:A=B in pnat),!.

strip_ses(V:s(A)=s(B)in pnat) :-
     rewrite_hyp_at_pos(hyp(V),left,[],cnc_s_bis) 
     then    strip_ses(V:A=B in pnat).   
strip_ses(V:0=s(_)in pnat) :-
     rewrite_hyp(V,left,succ_nonzero_left)
     then elim(V).
strip_ses(V:s(_)=0in pnat) :-
     rewrite_hyp(V,succ_nonzero_right)
     then elim(V).

/*
contradiction(_) :- apply(because),
    clam_warning('Disequality of constructor ground terms not fully implemented.').
*/
/*
 * LEMMA TACTIC:
 */

      % apply_lemma(Lemma) applies Lemma. Lemma is name of Lemma, and
      % Lemma must exist as a theorem.
      % We could have got away with just calling
      % 	apply(lemma(Lemma) then univ_elim)
      % but this would force univ_elim to plough through all hypotheses
      % while we know which hypothesis we want to elim on (namely the
      % recently introduced lemma). Thus, we unfold some of the code of
      % univ_elim in place here. 
      % Needs to be improved to deal (eg) associativity of disjunction
      % and conjunction.
apply_lemma(Lemma) :-
    goal(G), 
    hyp_list(H),free([V],H),
    theorem(Lemma,LemmaGoal,_),
    matrix(_,Matrix,G),
    Matrix =.. [Op,G1,G2],
    once((Op = '\\' ; Op = '#')),
    (instantiate(H,_,LemmaGoal, Matrix, Vallist)
      -> (lemma(Lemma,new[V])
	      then dequantify
	      then elim_on(V,Vallist,_) then hyp(_))
      ; ((NM =.. [Op,G2,G1],
         instantiate(H,_,LemmaGoal, NM, Vallist)) -> 
	 (commute_conn then
          lemma(Lemma,new[V]) then dequantify
	      then elim_on(V,Vallist,_) then hyp(_)))).
apply_lemma(Lemma) :-
    goal(G), hyp_list(H),free([V],H),
    theorem(Lemma,LemmaGoal,_),
    matrix(_,Matrix,G),
    (instantiate(H,_,LemmaGoal, Matrix, _)
     -> can_elim(LemmaGoal,[],Matrix,Vallist)
     ;  (Matrix=(L=R in T),can_elim(LemmaGoal,[],R=L in T,Vallist))
    ),    
    lemma(Lemma,new[V])
       then dequantify
         then elim_on(V,Vallist,_)
	    then hyp(_),!.

apply_lemma(A) :- fail_tac(apply_lemma(A)).

/* commutes the goal if it is either a conjunction or a disj  */
commute_conn :-
    goal(A\B),
    apply(seq(B\A,new[S])then
	      [idtac,
	       elim(S,new[A1,B1,_A2,_B2]) then
		   [intro(right) then [hyp(A1),wfftacs],
		    intro(left) then [hyp(B1),wfftacs]]]).
commute_conn :-
    goal(A#B),
    apply(seq(B#A,new[S])then
	      [idtac,
	       elim(S,new[S1,S2,_]) then
		   intro then 
		   [hyp(S2), hyp(S1)]]).
/*
 * BACKCHAIN_LEMMA TACTIC:
 * (this is a merger/generalisation of AlanSs back_lemma/1 and
 *  back2_lemma/1 tactics)
 *
 * Pitty we have to reconstruct the substitution that links current goal
 * and lemma (Vallist). We had this during the method, and now we have
 * to figure it out again... I guess we could pass it on as an argument,
 * but this seems somewhat baroque...
 */

backchain_lemma(Lemma) :-
    goal(G),hyp_list(H), free([V],H),
    theorem(Lemma,LemmaGoal),
    matrix(_,Matrix,G),
    instantiate(H,_,LemmaGoal,C=>Matrix,Vallist),
    conjunction2list(C,Conjs),
    map_list(Conjs,Conj:=>Hc,hyp(Hc:Conj,H),_),
    apply(lemma(Lemma,new[V])
              then dequantify
	          then elim_on(V,Vallist,Last)
	              then elim(Last)
	                  then elementary 
         ),!.
backchain_lemma(A) :- fail_tac(backchain_lemma(A)).

conjunction2list(C,[C]) :- \+ functorp(C,#,2).
conjunction2list(C1#C2,[C1|C2l]):- conjunction2list(C2,C2l).



/*
 *
 *  CANCELLATION TACTIC
 *
 */
cancellation(Pos,Rn):- wave(Pos,[Rn,imp(right)]),!.
cancellation(A,B) :- fail_tac(cancellation(A,B)).

/*
 * NORMALISE TACTIC
 *
 * Separate clauses for each of the normal/1 submethods
 */
normalize(List) :- apply_list(List).
normal(univ_intro) :- intro then [idtac,try(wfftacs)].
normal(imply_intro):- intro then [idtac,try(wfftacs)].
normal(imply_elim(H,Lemma)) :-
    elim(H)
      then [complete (hyp(Lemma)
              or apply_lemma(Lemma)
	      or backchain_lemma(Lemma)),
            thin([H])
           ].
normal(conjunct_elim(ConjH,[New1,New2])) :-
    elim(ConjH,new[New1,New2,_]) then thin([ConjH]).
        
/* Stap and base cases */ 
step_case(Tac) :- apply(Tac),!.
step_case(A) :- fail_tac(step_case(A)).

base_case(Tac) :- apply(Tac),!.
base_case(A) :- fail_tac(base_case(A)).

sym_eval(Tac) :- apply(Tac),!.
sym_eval(A) :- fail_tac(sym_eval(A)).

/* a couple of rules for <=> */
intro_iff :-
    goal(_<=>_),
    compute([[unfold]]) then
	intro.
elim_iff(Hyp) :-
    hypothesis(Hyp:_<=>_),
    compute(hyp(Hyp),[[unfold]]) then
	elim(Hyp).

/* rename all bound variables in Hyp away from each other and from all
   atoms/variables in Term  (errghh!)  */
rename_hyp(Hyp,Term,NewHyp) :-
    hypothesis(Hyp:H),
    rename_apart(H,NewH,Term),
    apply(seq(NewH,new[NewHyp]) then [hyp(Hyp), thin([Hyp])]).

/* (+,-,+) S is alpha equivalent to S but all binders in S are renamed
   to be away from the bindings in B  */
rename_apart(T,S,All) :-
    rename_apart_(T,S),
    make_ground_term(S,All).
rename_apart_(A,A) :-
    (atomic(A);var(A)),!.
rename_apart_(rec(X,A), rec(XX,AAA)) :-
    !,
    s(A,[XX],[X],AA), rename_apart_(AA,AAA).
rename_apart_(lambda(X,A), lambda(XX,AAA)) :-
    !,
    s(A,[XX],[X],AA), rename_apart_(AA,AAA).
rename_apart_(X:B#A, XX:B#AAA) :- 
    !, 
    s(A,[XX],[X],AA), rename_apart_(AA,AAA).
rename_apart_(X:B=>A, XX:B=>AAA) :- 
    !, 
    s(A,[XX],[X],AA), rename_apart_(AA,AAA).
rename_apart_({X:B\A},{XX:B\AAA}):- 
    !,
    s(A,[XX],[X],AA), rename_apart_(AA,AAA).
rename_apart_(A///[X,Y,T],A///[XX,YY,TTT]):- 
    !,
    s(T,[XX,YY],[X,Y],TT), rename_apart_(TT,TTT).
rename_apart_(T,TT) :-
    T =.. [F|A],
    rename_aparts_(A,AA),
    TT =.. [F|AA].
rename_aparts_([],[]).
rename_aparts_([A|As],[B|Bs]) :-
    rename_apart_(A,B),
    rename_aparts_(As,Bs).



%****************
%*
%*  intro_hyps   - Introduce as hypotheses and expand conjuncts for all
%*               implications remaining in goal.  EF is the filter
%*               for the expansion/computation of the hypotheses as the
%*               are introduced.
%*
%*
%****************

?-if(\+ noprove =: _).
intro_hyps( EF ) :-
    ( goal( T => _ );
      goal( _ : T => _ )
    ),
    univ_level( T, L ),
    noise( 150, '$' ),
    do( apply(intro(at(L),new _))
        then
          [ 2-( prove_mem ),
            1-( hyp_list( Hyps ),
                append( _, [Last], Hyps ),
                decl( Name:_, [Last]),
                explode_hyp( EF, Name ),
                intro_hyps(EF) )
          ]
      ).
intro_hyps(_).

?-endif.

check_status( Name, P, S ) :-
    \+ noprove =: _,
    \+ status0(P, S),
    write( 'Status of theorem ' ),
    write( Name ),
    write( ' is not ' ),
    write( S ),
    write( '.' ),
    nl,
    debug_abort.

check_status( _, _,_ ).

?-if(\+ noprove =: _).

smart_prove_wff( _ ) :-
    unsound_smart_wff_check =: _,
    ( ( goal( Tm=TT in Type),
        convertible(Tm,TT)
      );
      goal( Tm in Type )
    ),
    hyp_list(HL),
    noise( 100, 'U' ),
    ( guess_tt_type( pure, HL, Tm, Type ) ;
      ( noise( 100, 'F' ),
        stopleap
      )
    ),
    !,
    apply(because).
smart_prove_wff( WffHyps ) :-
    apply( repeat (from_wff_hyp( WffHyps) or prove_mem_step) ).

from_wff_hyp( WffHyps ) :-
    goal( Tm ),
    member( H:WffHyp, WffHyps ),
    match_term( WffHyp, Tm, Match ),
    hypothesis(H:WffHypTempl ),
    noise(100,'w'),
    apply( seq( WffHypTempl , new _ )
           then
             [ hyp(H),
               inst_func_type_last( Match, [sloppy] ) then hyp(_)
             ]
         ).

%******************
%*
%*      apply_ralemma( +Kind )
%*      -  Prove the current goal by applying a matching lemma of
%*      kind Kind.
%*
%******************

apply_ralemma( K ) :- 
    proof_thru_lemma( K, noask, _, _ ),
    !.

apply_ralemma( Kind ) :-
    goal(G),
    nl,
    write( 'Could not find lemma of kind: ' ),
    write( Kind ),
    nl,
    write( 'To prove goal: ' ),
    write( G ),
    nl,
    debug_abort.

%***** Stuff beyond this point should gradually be phased out of use
%***** in favour of proof_thru_lemma.

apply_ralemma( Kind, Flags ) :-
    \+ member( norec, Flags ),
    goal(G),
    tuple( Kind, [Name,Patt|_] ),
    match_term( Patt, G, LemVarInsts ),
    do(   apply( lemma(Name, new _) )
        then
          ( inst_func_type_last( LemVarInsts, [norec|Flags] ),
            apply( hyp( _ ) )
          )
      ).

apply_ralemma( Kind, Flags ) :-
    \+ member( norec, Flags ),
    member( ask, Flags ),
    goal(G),
    hyp_list(H),
    get_new_lemma( Kind, H, G ).

apply_ralemma( Kind, Flags ) :-
    member( abort, Flags ),
    goal(G),
    nl,
    write( 'Could not find lemma of kind: ' ),
    write( Kind ),
    nl,
    write( 'To prove goal: ' ),
    write( G ),
    nl,
    debug_abort.


cut_in_using_lemma( Goal, Name ) :-
    apply( seq( Goal, new _ )
           then
             [ proof_thru_lemma( _, noask, Name, _ ),
               idtac
             ]
         ).

cut_in_with_lemma( Goal, Kind ) :-
    apply( seq( Goal, new _ )
           then
             [ proof_thru_lemma( Kind, noask, _, _ ),
               idtac
             ]
         ).




inst_func_type_last( I ) :- inst_func_type_last( I, [abort] ).
inst_func_type_hyp( H, I ) :- inst_func_type_hyp( H, I, [abort] ).

inst_func_type_last( Insts, Flags ) :-
    last_hyp( Hyp ),
    inst_func_type_hyp( Hyp, Insts, Flags ).

inst_func_type_hyp( _, [], _ ) :- !.

inst_func_type_hyp( Hyp, Insts, Flags ) :-
    member( explicit, Flags ),
    !,
    Insts = [Inst|RestInsts],
    rhypothesis( Hyp:(_:_=>_) ),
    noise( 200, '$' ),
    do( apply( elim(Hyp,on(Inst), new _) )
        then
          [
            prove_mem,
              apply(thin([Hyp]))
            then
              inst_func_type_last( RestInsts, Flags )
          ]
      ).

inst_func_type_hyp( Hyp, Insts, Flags ) :-
    rhypothesis( Hyp:(Var:_=>_) ),
    member( (Var-_), Insts ),
    !,
    selectchk( (Var-Inst), Insts, RestInsts ),
    noise( 200, '$' ),
    do( apply( elim(Hyp,on(Inst), new _) )
        then
          [
            prove_mem,
              apply(thin([Hyp]))
            then
              inst_func_type_last( RestInsts, Flags )
          ]
      ).

inst_func_type_hyp( Hyp, Insts, Flags ) :-
    rhypothesis( Hyp:(_:Type=>_) ),
    noise( 200, '$' ),
    do(   apply( seq( Type ) )
        then
          [
            apply_ralemma( precond_lemma, Flags ),
            ( rhypothesis(SV:Type),
              do( apply( elim(Hyp,on(SV), new _) )
                  then
                  [
                    prove_mem,
                    apply(thin([Hyp]))
                    then
                    inst_func_type_last( SV, Insts, Flags )
                  ]
                )
            )
          ]
      ).

inst_func_type_hyp( _, L, Flags ) :-
    member( abort, Flags ),
    write( 'INTERNAL ERROR: ' ),
    write( 'inst_func_type_hyp: could not use all instantiations.' ),
    nl,
    write( 'Left over: ' ),
    write( L ),
    nl,
    debug_abort.

inst_func_type_hyp( _, _, Flags ) :-
    member( sloppy, Flags ).



rec_induction_cases( ElHyp ) :-
    rhypothesis( ElHyp:(_\_) ),
    !,
    noise( 200,'$' ),
    do( apply(elim(ElHyp, new _))
        then
          [ % **** Deal with the left cases
            ( 
              hyp_list( LHyps ),
              append( _, [LEHyp:_,_], LHyps ),
              rec_induction_cases( LEHyp ) ),

            % **** Deal with right cases
            ( 
              hyp_list( RHyps ),
              append( _, [REHyp:_,_], RHyps ),
              rec_induction_cases( REHyp ) )
          ] ).

rec_induction_cases( ElHyp ) :-
    rhypothesis( ElHyp:(_#_) ),
    !,
    noise( 200,'$' ),
    do( apply(elim(ElHyp, new _))
        then
          ( hyp_list( Hyps ),
            append( _, [REHyp:_,LEHyp:_,_], Hyps ),
            rec_induction_cases( REHyp ),
            rec_induction_cases( LEHyp )
          )
      ).

rec_induction_cases( ElHyp ) :-
    rhypothesis( ElHyp:unary ),
    !,
    noise( 200,'$' ),
    apply(elim(ElHyp )).


rec_induction_cases( _ ) :-
    noise( 200, '$' ).




intro_type_hyps_upto( Name ) :-
    goal( Name : _ => _ ),
    noisenl( 200, 'Done.' ),
    do( apply(intro(at(_),new _))
        then
          [ 2-prove_mem, 1-true ]
      ).

intro_type_hyps_upto( Name ) :-
    goal( _ : T => _ ),
    noise( 200, '$' ),
    univ_level( T, L ),
    do( apply(intro(at(L),new _))
        then
          [ 2-prove_mem, 
            1-intro_type_hyps_upto( Name )
          ]
      ).

intro_type_hyps_upto( Name ) :-
    nl,
    write( 'intro_type_hyps_upto: Ill-formed goal hyp. ' ),
    write( Name ),
    write( ' not encountered.' ),
    nl,
    debug_abort.


%************************
%*
%* str_case_anal - Apply a structural case-analysis lemma to the
%* hypothesis H (this assumes H is of defined recursive type.
%* 
%************************

str_case_anal( H ) :-
    hypothesis( H:Type),
    goal( G ),
    noise( 200, '$' ),
    do( apply( seq( lambda( H, G) of H, _ ) ) 
        then
          [2-(last_hyp(LH),
              apply(compute(hyp(LH),using(_),not([[unfold,_]]))
                    then
                    hyp(_))
             ),
           1-(apply_caselemma( Type ))
          ]

      ).

apply_caselemma( Type ) :-
    tuple( str_case_lemma, [CaseLemma,_,Hyps|_] ),
    rmember( (_:LType), Hyps ),
    match_term( LType, Type, _ ),
    noise( 200, '$' ),
    do( apply(lemma(CaseLemma, _ ))
          then
        inst_caselemma( Type )
      ).

inst_caselemma( Type ) :-
    lhypothesis( IL:(_:(Type=>u(_))=>_) ),
    goal( Inst of _ ),
    noise( 200, '$' ),
    do( apply(elim(IL,on(Inst),_))
        then
          [ prove_mem,
            do( apply(thin([IL])) then inst_caselemma( Type ) )
          ]
      ).

inst_caselemma( IType ) :-
    lhypothesis( IL:(_:Type=>_) ),
    hypothesis( Inst:Type ),
    noise( 200, '$' ),
    do( apply(elim(IL,on(Inst),_))
        then
          [ apply(hyp(Inst)),
            do( apply(thin([IL])) then inst_caselemma( IType ) )
          ]
      ).

inst_caselemma( _ ) :-
    lhypothesis( IL:(_:_ => _ of _ ) ),
    noise( 200, '$' ),
    do( apply(elim(IL,_)) 
          then
            [ do( apply(thin([IL])) then
                  apply(intro_conjuncts) then 
                  apply(compute(using(_),not([[unfold,_]]))) then
                  intro_hyps( [[unfold,_]] )
                ),
                apply(hyp(_))
            ]
      ).
  

intro_conjuncts :-
    goal( _ # _ ),
    do( apply(intro) then intro_conjuncts ).
intro_conjuncts.
       
    

inst_exist_vars( CaseInst ) :-
    goal( V:_#_ ),
    noise( 200, '$' ),
    member( (V-Inst), CaseInst ),
    do( apply(intro(Inst,new _)) 
        then 
          [prove_mem, inst_exist_vars(CaseInst), prove_mem ] 
      ).

inst_exist_vars( [] ).
    

%******************
%*
%*
%*      wf_induction( WfMeasure ) 
%* - Apply well-founded induction based on the justifying measure
%* WfMeasure.  WfMeasure is a list representing a tuple.
%*
%*******************

wf_induction( IndVars, MeasureTuple, Measure_Hyps ) :-
    do_wf_induction( IndVars, MeasureTuple, Measure_Hyps  ).

do_wf_induction( IndVars, [Measure|RestMeasureTuple],
                 [Measure-IndHyp|RestMeasure_Hyps] ) :-
    findall( Hyp, 
           (hypothesis(V:T), member(V,IndVars),Hyp=(V:T) ),
           Hyps
         ),
    Hyps \= [],
    findall( V, 
            (hypothesis(V:_), member(V,IndVars)),
           HypInsts
         ),
    HypInsts \= [],
    freevarsinterm(Measure,MeasHere),         
    subtract(IndVars,MeasHere, RestIndVars),

    goal( Goal ),
    hyp_list(HL),
    new_free_var( 'm', [M1,M2,LV], HL ), 
    new_free_var( 'ih', [IndHyp], HL ),
    curry_type([M1:pnat|Hyps], LV:(M1=Measure in pnat)=>Goal, IndGoal ),

    % **** Introduce induction/recursion scheme:
    % **** CUT IN: M1:pnat=> <existing hyps> => M1 = WfMeasure => <goal>
    % **** I.E. Carry the measure, plus the arguments of the recursion
    % **** through the induction that synthesises it.

    do( apply( seq( IndGoal ) )
        then
          [ % **** Prove existing formula by instantiation of cut in one
            % **** with measure, and existing hypotheses.

            2-( inst_func_type_last( [Measure|HypInsts], [explicit,abort] ),
                do(  ( last_hyp(LH1),
                       apply(elim(LH1, new _ ))
                     )
                   then
                     [ prove_mem, 
                       ( last_hyp(IIH),
                         apply( hyp(IIH) )
                       ) 
                     ]
                 )
              ),
              
            % **** Throw away now redundant original argument hypotheses
            1-do(   apply(thin(IndVars))
                  then
                    apply(intro(at(_),new _ ))
                  then
                    [  do( apply(elim(M1,cv,new[IndHyp,_,M2]))
                         then
                           apply(intro_type_hyps_upto(LV))
                         then
                           ( hypothesis(IndHyp:Tm),
                             instantiated(Tm,[M2-'z$$'],OverTm),
                             univ_level(Tm,UL),
                             apply(subst(at(UL),hyp(IndHyp),over('z$$',OverTm),
                                   M2=Measure in pnat)
                                   )
                           )
                         then
                           [ 1-apply(hyp(_)),
                             3-prove_mem,
                             2-do( apply(thin([M1,M2])) 
                                 then 
                                   do_wf_induction( RestIndVars,
                                                RestMeasureTuple,
                                                RestMeasure_Hyps)
                                 )
                           ]
                         ),
                      prove_mem
                    ]
                 )
         ]
     ).


do_wf_induction(_,[],[]).

?-endif.

list_to_tactic([T],T).
list_to_tactic([T|Ts],T then Tacs) :-
    list_to_tactic(Ts,Tacs).


expand_s_norewrite(V,VV) :-
    check_lemma_present(succlemma),
    hyp_list(H),goal(G),
    hfree([Lemma,LemmaA,L2,L3,L4],[VV:dummy|H]),
    apply((lemma(succlemma,new[LemmaA]) then rename_hyp(LemmaA, H==>G,Lemma) then thin([LemmaA]))then
	      (elim(Lemma,on(V),new[L2]) then thin([Lemma])) then
	         [thin([L2]) then try wfftacs,
		  (elim(L2,new[L3]) then thin([L2])) then
		      [ hyp(_),
			(elim(L3,new[VV,L4,_]) then thin([L3]))]]).
expand_s(V,VV) :-
    check_lemma_present(succlemma),
    hyp_list(H),goal(G),
    hfree([Lemma,LemmaA,L2,L3,L4],[VV:dummy|H]),
    apply((lemma(succlemma,new[LemmaA]) then rename_hyp(LemmaA, H==>G,Lemma) then thin([LemmaA]))then
	      (elim(Lemma,on(V),new[L2]) then thin([Lemma])) then
	         [thin([L2]) then try wfftacs,
		  (elim(L2,new[L3]) then thin([L2])) then
		      [ hyp(_),
			(elim(L3,new[VV,L4,_]) then thin([L3])) then
			    ((rewrite(L4)then thin([L4])) then try wfftacs)]]).
expand_s_nothin(V,VV) :-
    check_lemma_present(succlemma),
    hyp_list(H),goal(G),
    hfree([Lemma,LemmaA,L2,L3,L4],[VV:dummy|H]),
    apply((lemma(succlemma,new[LemmaA]) then rename_hyp(LemmaA, H==>G,Lemma) )then
	      (elim(Lemma,on(V),new[L2])  ) then
	      [ try wfftacs,
		(elim(L2,new[L3])) then
		    [ hyp(_),
		      (elim(L3,new[VV,L4,_])) then
			  ((rewrite(L4)) then try wfftacs)]]).

expand_ss(V) :-
    check_lemma_present(succlemma3),
    apply(lemma(succlemma3,new[Lemma]) then
	      (elim(Lemma,on(V),new[L2]) then thin([Lemma])) then
	         [thin([L2]) then try wfftacs,
		  (elim(L2,new[L3]) then thin([L2])) then
		      [ hyp(_),
			(elim(L3,new[L4]) then thin([L3])) then
			    [ hyp(_),
			      (elim(L4,new[_,L6,_]) then thin([L4])) then
				  (rewrite(L6) then try wfftacs)]]]).


univ_elim :- univ_elim(_).
univ_elim(H) :-
    goal(Goal),
    elimable(H,Goal,Vallist), !,
    elim_on(H,Vallist,_) then (hyp(_) or equality) then wfftacs.

elimable(H,Goal,Vallist) :-
    hypothesis(H:Hyp),
    can_elim(Hyp,[],Goal,Vallist).

can_elim(Z,List,Goal,Vallist) :-
    (Goal=(L=R in T)
     -> (s(Z,Revvallist,List,L=R in T)
         ;
	 s(Z,Revvallist,List,R=L in T)
	)
    ; s(Z,Revvallist,List,Goal)
    ),
    reverse(Revvallist,Vallist).

can_elim(X:_=>Z,L,Goal,Vallist) :-
    can_elim(Z,[X|L],Goal,Vallist).

/* eliminate existentials */
elim_on(H) :-
    hypothesis(H:(_:_#_)),
    apply(elim(H,new [_,H1,H2]) then
	      (thin([H,H2]) then elim_on(H1))).	       
elim_on(H) :-
    \+ hypothesis(H:(_:_#_)).

/* do elims and thin all but the last, leaving its inhabitant as V */
elim_on_thin(V,ON) :-
    append(Pre,[Last],ON),
    elim_on(V,Pre,NewV) then
	thin([V]) then
	   (elim(NewV,on(Last),new [V]) then wfftacs) then thin([NewV]).

elim_on(H,Vallist) :- elim_on(H,Vallist,_).
elim_on(H,[],H) :- !.
elim_on(H,Vallist,Last) :-
    do_elim_on(H,Vallist,[H|HypList])
        then (append(IntermediateHyps,[Last],HypList),
              thin(IntermediateHyps)
             ).

    /* changed by AlanS but I'm not convinced this is right: */
    /* wfftacs then try hyp(_). */
    /* There are definitely places where the try hyp(_) is not a good */
    /* idea (eg. in the proof of doublehalf), thus: back to my version: */
do_elim_on(H,[],[H]) :-
    wfftacs.
    % First clause check if we are accidently elim-ing on a Prolog var.
    % If so, we replace Val by a random object of the correct type, and
    % try again. 
do_elim_on(H,[Val|Vallist],[H|HypList]) :- var(Val), !,
    hypothesis(H:_:T=>_),
    hypothesis(Val:T), do_elim_on(H,[Val|Vallist],[H|HypList]).
do_elim_on(H,[Val|Vallist],[H|HypList]) :-
    (hyp_list(HList),free([New],HList),
     NewList=[New], 
     elim(H,on(Val),new NewList)
    )
    then [wfftacs,try (hypothesis(New:_), do_elim_on(New,Vallist,HypList))].

thinelim(V) :- hyp_list(H),free([_,_,C,D],H),elim(V) then thin([C,D]).

%  generate a new entity and check it's not in Hyps or Goal

genvar_and_check(New) :-
         goal(Goal),
	 hyp_list(Hyps),
         genvar(New),
         \+ contains_term(New,Hyps),
         \+ contains_term(New,Goal).

/*=======================================================================
 * Using equations for rewriting:
 */

	% rewrite/1 comes in various flavours:
	% - rewrite(L=R in T) rewrites all occs of L to R in the current goal
	% - rewrite(Hyp) uses Hyp of the form L=R in T.
	% - rewrite(L) uses lemma L of the form universally quantified L=R in T
	% - rewrite(Pos,_,Dir) is as any of the above but only rewriting at
	%   the specified Pos in given Direction.
rewrite(H) :-
    goal(_:_=>_),				% strip any quantification
    !,
    dequantify_all(A,B) 
	then rewrite(H)
	then requantify(A,B).	

rewrite(H) :-
    hypothesis(H:X=Y in T),!,
    rewrite(X=Y in T).
rewrite(X=Y in T):- 
    goal(G), hyp_list(H),
    (hypothesis(Eq:X=Y in T) ; hypothesis(Eq:Y=X in T)),
    once((genvar(V), free([V],H), \+ appears(V,G), \+ appears(V,Y))),
    s(G,[V],[X],GG), \+ G == GG,
    top_univ_level(G,I),II is I+1,
    subst(at(II),over(V,GG),X=Y in T)
        then [univ_elim(Eq), idtac, wfftacs].
	% can also give name of lemma-rewrite-rule:
rewrite(L) :-
    \+ hypothesis(L),
    theorem(L,LG,_),
    goal(G),hyp_list(HL),
    exp_at(G,_,Exp),
    instantiate(HL,_,LG,Exp= _ in _,_),
    can_elim(LG,[],Exp= _ in _,Vals),
    apply(lemma(L,new[L])
        then elim_on(L,Vals,Last)
	   then rewrite(Last)
	       then thin([L,Last])).

normalize_hyp(hyp(H),Rules) :-
    member(R,Rules),
    apply(rewrite_hyp_at_pos(hyp(H),left,_,R) then
	      normalize_hyp(hyp(H),Rules)),!.
normalize_hyp(_,_).

rewrite_hyp_at_pos(hyp(H),Dir,Pos,L) :-
    \+ hypothesis(L),
    theorem(L,LG,_),
    hypothesis(H:G),
    exp_at(G,Pos,Exp),
    hyp_list(HL), instantiate(HL,_,LG,Exp= _ in _,Vals),
%    can_elim(LG,[],Exp= _ in _,Vals),  CAN I DROP THESE?
    apply(lemma(L,new[LL])
        then elim_on(LL,Vals,Last)
	   then rewrite_hyp(Last,Dir,H)
	       then thin([L,LL,Last])).

rewrite_hyp_at_pos(hyp(H),Dir,Pos,L) :-
    \+ hypothesis(L),
    theorem(L,LG,_),
    hypothesis(H:G),
    exp_at(G,Pos,Exp),
    hyp_list(HL), instantiate(HL,_,LG,Exp=> _,Vals),
%    can_elim(LG,[],Exp=> _,Vals),
    apply(lemma(L,new[LL])
        then elim_on(LL,Vals,Last)
	   then rewrite_hyp(Last,Dir,H)
	       then thin([L,LL,Last])).
rewrite_hyp_at_pos(hyp(H),Dir,Pos,L) :-
    hypothesis(L:LG),
    hypothesis(H:G),
    exp_at(G,Pos,Exp),
    hyp_list(HL), instantiate(HL,_,LG,Exp= _ in _,Vals),
%    can_elim(LG,[],Exp= _ in _,Vals),  CAN I DROP THESE?
    elim_on(L,Vals,Last)
	   then rewrite_hyp(Last,Dir,H).

forward_chain(hyp(H),L) :-
    rewrite_hyp_at_pos(hyp(H),left,[],L).

	% rewrite_hyp/3	is a subset of rewrite/1 working on a hypothesis.
	% Currently we only support rewrite_hyp for the simple case
	% (i.e. given another hypothesis which is an equality).
rewrite_hyp(Hyp,Lemma) :-
    apply(lemma(Lemma,new[L]) then rewrite_hyp(L,_,Hyp)).
rewrite_hyp(Eq,D,Hyp) :-
    hypothesis(Eq:L=R in T),
    rewrite_hyp(L=R in T,D,Hyp).
rewrite_hyp(Eq,D,Hyp) :-
    hyp_list(HL),
    hypothesis(Eq:EQ),
    \+ EQ = (_ = _ in _),
    \+ EQ = (_ => _),
    hypothesis(Hyp:Term),
    once((instantiate(HL,[],EQ,Term = _ in _,Vals);
	  instantiate(HL,[],EQ,Term => _,Vals))),
    (elim_on(Eq,Vals,H1) then thin([Eq])) then
	rewrite_hyp(H1,D,Hyp).
rewrite_hyp(Eq,D,Hyp) :-
    hypothesis(Eq:L=>R),
    rewrite_hyp(L=>R,D,Hyp).
rewrite_hyp(L=R in T,right,H) :-
    rewrite_hyp(R=L in T, left,H).
rewrite_hyp(L=R in T,left,H) :-
    goal(G), hyp_list(Hl), hypothesis(H:Hyp),
    (hypothesis(Eq:L=R in T) ; hypothesis(Eq:R=L in T)),
    genvar(V), free([V],Hl), \+ appears(V,G), \+ appears(V,R),
    s(Hyp,[V],[L],HHyp),
    subst(hyp(H),over(V,HHyp),L=R in T)
    	then [univ_elim(Eq), idtac, wfftacs].
rewrite_hyp(L=>R,left,H) :-
    goal(G), hyp_list(Hl), 
    hypothesis(Eq:L=>R),
    member(H:Ty,Hl),
    genvar(V), free([V],Hl), \+ appears(V,G), \+ appears(V,R),
	!,
	apply(seq(Ty, new [V]) then [hyp(H),
	thin([H]) then
    ((elim(Eq,new [H]) then [hyp(V),thin([V])]) then thin([Eq]))]).

	% rewrite at given Pos in given direction.
	% Assume goal is already dequantified.
	%
	% We can also deal with =>-based rewrites.  We can currently
	% only do this if the rewrite is at the top of the goal, or main
	% connective in the goal is a => and the rewrite is at the top
	% of the rhs of the => in the goal (This is exactly the case for
	% fertilization after inductions on => goals).	This is dealt
	% with by the first clause. If the fertilization happens
	% anywhere nested in the rhs of the => in the goal, we would
	% have to do different things depending on what connectives the
	% subterm is nested in.  This is too difficult to write at the
	% moment, so we just use a shortcut using "because"...  (The
	% third clause).
	%
	% First clause for rewrites at the top of the goal.
	%
	% NOTE: now that we have a new generalised weak fertilization
	% method, a lot of the below is no longer needed (in particular,
	% rewriting =>s).
rewrite_at_pos(help) :-
    print('rewrite_at_pos(Frees,Pos,H,Type(Dir))'),nl.

/* Using L <=> R in direction Dir.  If Dir is left, use
   L=>R/imp(left) at -ve polarity, L=>R/imp(right) at +ve
   polarity.  Vice-versa when Dir is right. In summary:
   Dir==left:  L=>R/imp(left) ; L=>R/imp(right)
   Dir==right: R=>L/imp(left) ; R=>L/imp(right)
 */
rewrite_at_pos(Frees,Pos,H,equiv(left)) :-
    hypothesis(H:Eq), !,
    goal(G),
    exp_at(G,Pos,Exp),
    hyp_list(HL),
    (polarity_compatible(G,Pos,imp(right))
      -> (instantiate(HL,Frees,Eq, Exp <=> _,Vals),
	  elim_on(H,Vals,H1)
	      then compute(hyp(H1),[[unfold]])
                   then elim(H1,new[HH,Hp,HHH])
	                then rewrite_at_pos([],Pos,Hp,imp(right))
	                     then thin([H1,HH,Hp,HHH]))
      ;  (instantiate(HL,Frees,Eq, Exp <=> _,Vals),
	  elim_on(H,Vals,H1)
	      then compute(hyp(H1),[[unfold]])
                   then elim(H1,new[Hp,HH,HHH])
	                then rewrite_at_pos([],Pos,Hp,imp(left))
	                     then thin([H1,HH,Hp,HHH]))).

rewrite_at_pos(Frees,Pos,H,equiv(right)) :-
    hypothesis(H:Eq),!,
    goal(G),
    exp_at(G,Pos,Exp),
    hyp_list(HL),
    (polarity_compatible(G,Pos,imp(left))
      -> (instantiate(HL,Frees,Eq, _ <=> Exp,Vals),
	  elim_on(H,Vals,H1)
	      then compute(hyp(H1),[[unfold]])
                   then elim(H1,new[HH,Hp,HHH])
	                then rewrite_at_pos([],Pos,Hp,imp(right))
	                     then thin([H1,HH,Hp,HHH]))
      ;  (instantiate(HL,Frees,Eq, _ <=> Exp,Vals),
	  elim_on(H,Vals,H1)
	      then compute(hyp(H1),[[unfold]])
                   then elim(H1,new[Hp,HH,HHH])
	                then rewrite_at_pos([],Pos,Hp,imp(left))
	      	             then thin([H1,HH,Hp,HHH]))).

rewrite_at_pos(Frees,[],H,imp(_)) :-
    hypothesis(H:Impl), 
    goal(Matrix),hyp_list(HL),
    instantiate(HL,Frees,Impl,_ => Matrix,Vals), !,
    elim_on(H,Vals,H1)
       then [(free([H2],HL), elim(H1,new[H2]))
                then [thin([H1,H2]),
		      hyp(H2)
		     ]
	    ].
	% Second clause for rewrites in rhs of top =>
rewrite_at_pos(Frees,[2],H,imp(_)) :-
    hypothesis(H:Impl), 
    goal(Matrix),
    exp_at(Matrix,[2],Sub),
    hyp_list(HL),
    instantiate(HL,Frees,Impl,NewSub=>Sub,Vals), !,
    replace([2],NewSub,Matrix,NewMatrix),
    free([Seq],HL),
    seq(NewMatrix,new[Seq])
       then [idtac,
             elim_on(H,Vals,_)
	        then (elementary or propositional)
	    ].
        % added clause to deal with existential quantifiers (AlanS)
rewrite_at_pos(Frees,[2,2],H,imp(_)) :-
    hypothesis(H:Impl), 
    goal(Var:Type#Form),
    hyp_list(HL), instantiate(HL,Frees,Impl,Ante => Form,_), !,
    free([H1,H2],HL),
    seq(Var:Type#Ante,new[H1]) then 
      [idtac,
       elim(H1,new[H2,_,_]) then 
       intro(H2) then 
          [try wfftacs,
           rewrite_at_pos(Frees,[],H,imp(_)) then try hyp(_),
           try wfftacs
          ]
      ].
	% Third clause is the short-cut for other => rewrites (right-to-left) ...
rewrite_at_pos(Frees,Pos,H,imp(right)) :- Pos\=[2], hypothesis(H:Impl), !,
    goal(Matrix),
    exp_at(Matrix,Pos,Sub),
    hyp_list(HL), instantiate(HL,Frees,Impl,NewSub=>Sub,Vals),
    replace(Pos,NewSub,Matrix,NewMatrix),
    seq(NewMatrix,new[New])
       then [idtac,
             elim_on(H,Vals,H1) then
                 justify_imp_rewrite(New,right,H1)].
        % Fourth clause is the short-cut for other 
        %    => rewrites (left-to-right) ...
rewrite_at_pos(Frees,Pos,H,imp(left)) :- Pos\=[2], hypothesis(H:Impl), !,
    goal(Matrix),
    exp_at(Matrix,Pos,Sub),
    hyp_list(HL),instantiate(HL,Frees,Impl,Sub=>NewSub,Vals),
    replace(Pos,NewSub,Matrix,NewMatrix),
    seq(NewMatrix,new[New])
            then [idtac,
                  elim_on(H,Vals,H1) then 
                     justify_imp_rewrite(New,left,H1)].
	% Fifth clause: simulate right-to-left rewriting by
	% left-to-right rewriting:
rewrite_at_pos(Frees,Pos,L=R in T,equ(_,right)) :- 
    rewrite_at_pos(Frees,Pos,R=L in T,equ(_,left)).
	% Sixth clause: deal with non-universally quantified equalities.
rewrite_at_pos(_Frees,Pos,L=R in T,equ(_,left)) :-
    goal(G),hyp_list(Hl), (hypothesis(Eq:L=R in T) ; hypothesis(Eq:R=L in T)),
    genvar(V), free([V],Hl), \+ appears(V,G), \+ appears(V,R),
    replace(Pos,V,G,Gv),
    top_univ_level(G,I),II is I+1,
    subst(at(II),over(V,Gv),L=R in T)
       then [univ_elim(Eq), idtac,wfftacs].
	% Seventh clause: map named hypothesis into non-universally
	% quantified equality:
rewrite_at_pos(Frees,Pos,H,Dir) :-
    hypothesis(H:X=Y in T),!,
    rewrite_at_pos(Frees,Pos,X=Y in T,Dir).
	% Eighth clause: as sixth clause, but for conditional rewrites. 
rewrite_at_pos(Frees,Pos,H,Dir) :-
    hypothesis(H:_=>X=Y in T), !,
    hyp_list(HL), free([EqH],HL),
    elim(H,new[EqH])
     then [(elementary or propositional),         % propositional??
           rewrite_at_pos(Frees,Pos,X=Y in T,Dir) then thin([EqH])
	  ].
	% Ninth clause: map universally quantified hypothesis into
	% non-universally quantified equality:
rewrite_at_pos(Frees,Pos,H,Dir) :-
    hypothesis(H:Eq), Eq=(_:_=>_),!,
    goal(G), exp_at(G,Pos,Exp),
    hyp_list(HL),
    (Dir=equ(_,left)
     -> (instantiate(HL,Frees,Eq,Exp = _ in _,Vals)
         orelse
	 instantiate(HL,Frees,Eq,_ => Exp = _ in _,Vals)
	)
     ;  (instantiate(HL,Frees,Eq,_ = Exp in _,Vals)
         orelse
	 instantiate(HL,Frees,Eq,_ => _ = Exp in _,Vals)
	)
    ),
    elim_on(H,Vals,Last)
        then rewrite_at_pos(Frees,Pos,Last,Dir)
	   then thin([Last]).
	% Tenth clause: map unmentioned hypothesis (lemma) into
	% universally quantified hypothesis:
rewrite_at_pos(Frees,Pos,L,Dir) :-
    \+ hypothesis(L),
    theorem(L,_,_),
    apply(lemma(L,new[L])
        then rewrite_at_pos(Frees,Pos,L,Dir)
	    then thin([L])).

/*
 *  Procedure builds sub-proofs to justify rewrites based
 *  on implication.  Arguments are hyp id, direction of rewrite, 
 *  and hyp id of the implication
 */

justify_imp_rewrite(New,right,H) :-
    hypothesis(New:NewSub), hypothesis(H:NewSub=>Sub), goal(Sub), !,
    elim(H,new[NewH]) then [hyp(New),hyp(NewH)].
justify_imp_rewrite(New,left,H) :-
    hypothesis(New:Sub), hypothesis(H:NewSub=>Sub), goal(NewSub), !,
    write('CLaM ERROR: Rewriting => rule  used with wrong polarity.'),nl,
    fail.
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:A#_),goal(A#_),
    elim(New,new[Ha,Hb,_]) then
      intro then
        [hyp(Ha),justify_imp_rewrite(Hb,Dir,H)].
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:_#B),goal(_#B),!,
    elim(New,new[Ha,Hb,_]) then
      intro then
        [justify_imp_rewrite(Ha,Dir,H),hyp(Hb)].
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:A=>_),goal(A=>_),!,
    intro(new[NewH]) then
       [elim(New,new[NewH2]) then 
           [hyp(NewH),justify_imp_rewrite(NewH2,Dir,H)],
        wfftacs].
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:_=>B),goal(_=>B),opposite_dir(Dir,Dir2),!,
    intro(new[NewH]) then
       [elim(New,new[NewH2]) then 
           [justify_imp_rewrite(NewH,Dir2,H),hyp(NewH2)],
        wfftacs].
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:A\_),goal(A\_),!,
    elim(New,new[Ha,Hb,_,_]) then
      [intro(left) then
          [hyp(Ha),wfftacs],
       intro(right) then
          [justify_imp_rewrite(Hb,Dir,H),wfftacs]
      ].
justify_imp_rewrite(New,Dir,H) :-
    hypothesis(New:_\B),goal(_\B),!,
    elim(New,new[Ha,Hb,_,_]) then
      [intro(left) then
          [justify_imp_rewrite(Ha,Dir,H),wfftacs],
       intro(right) then
          [hyp(Hb),wfftacs]
      ].    
opposite_dir(right,left).
opposite_dir(left,right).

propositional :-
    goal(G), hyp_list(H),
    matrix(Vs,M,G), append(H,Vs,Ctx),
    propositional(Ctx==>M,Tac),!,
    dequantify then apply(Tac).
propositional(T) :-
    dequantify then apply(T).

/* following is enabled for debugging */
fail_tac(Tac) :-
    fail,					%comment this for debugging
    hyp_list(H), goal(G),
    write('Could not apply '),nl,
    write(Tac),nl,
    write('to '),nl,
    write(H==>G),nl,
    fail.



/* hack to enable (brief!) comment in Oyster proof tree */
comm(Atom) :-
    apply(pure(seq(atom(Atom) in atom,new[V])
		   then [pure(intro),
			 thin([V])])).
comment(Atom) :-
    apply(comm(Atom)).

presburger :-
    clam_warning('Tactics for Presburger arithmetic are not implemented.'),
    clam_warning('(please re-plan with using_presburger/0 retracted.'),
    fail.

decide_pa :-
    hyp_list(H),
    goal(G),
    presburger_context(H,Arith),
    precon_matrix([],Arith=>G,ArithGG),
    universal_closure(H,ArithGG,Gclosed),
    to_basic_presburger(Gclosed,AA),
    lpa_dp(AA,yes).

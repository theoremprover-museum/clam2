% $Id: go.pl,v 1.10 1995/05/28 17:48:46 armando Exp $
%
% $Log: go.pl,v $
% Revision 1.10  1995/05/28 17:48:46  armando
% Renaming nflip/flip and flip/swap
%
% Revision 1.9  1995/05/25  16:15:50  armando
% Upgrading
%
% Revision 1.8  1995/05/24  17:08:48  armando
% Upgrading
%
% Revision 1.7  1995/05/18  14:21:19  armando
% Miscellaneous extensions
%
% Revision 1.6  1995/05/12  17:13:14  armando
% A lot of stuff changed.
%
% Revision 1.5  1995/04/03  16:01:52  armando
% Loading of 'src/simplify_pre.pl' added
%
% Revision 1.4  1995/04/03  14:21:22  armando
% Upgrading to status with eval_nflip working
%
% Revision 1.3  1995/03/29  14:14:51  armando
% CVS Header added
%
:- no_style_check(all).

:- lib_set(dir('.')).
:- lib_set(sdir('.')).

:- ['src/util.pl'].
:- ['needs.pl'].

%:- op(850,xfy,['<=>']).

% Strengthened version of elementary (rule for elimination of
% universal quantification introduced).
:- ['../meta-level-support/elementary.pl'].

% Customized Clam output
:- ['../proof-planning/util.pl'].
:- ['../proof-planning/plan_df.pl'].

% - Change to hfree.
% - Changed definition of canonical to recognize as canonical
%   also equalities of canonical terms
:- ['../meta-level-support/method_pre.pl'].
% scheme([v0::v1]... added clause preventing applicability to
% case v0::v1::v2
:- ['../meta-level-support/schemes.pl'].

% Defining some predicated for debugging purposes only
:- ['src/debug_pred.pl'].

% I want see the hypotheses during the tracing
:- ['../proof-planning/applicable.pl'].

% Loading code for the precondition of the case_split mthd
:- ['src/case_split_pre.pl'].
:- ['src/case_split_and_simplify_pre.pl'].
% Loading Brigitte's case_split method.
:- lib_load(smthd(equal/_)).
:- lib_load(mthd(case_split_and_simplify/1),after(induction/2)).
:- lib_load(smthd(casesplit/_)).

% Loading the patched ripple smthd
:- lib_load(smthd(ripple/3)).
:- lib_load(mthd(step_case/_)).

% Preventing the generalisation of terms of type u(_)
:- lib_load(mthd(generalise/2)).

% Loading the wave smthd extended to deal with condition set rules
:- lib_load(smthd(wave/4)).

% guess_type: added clause for the dependent function type
:- ['../meta-level-support/tactics_wf.pl'].
% Loading the tactics.
:- ['../meta-level-support/tactics.pl'].

go(eval_flipl_nil):-
	lib_load(lemma(eval_flipl_nil)),
	select(eval_flipl_nil),
	dplan, !,
	apply_dplan.

go(eval_nflip):- 
	lib_load(lemma(eval_nflip)),
	select(eval_nflip),
	dplan,!,
	apply_dplan.

go(evenlist):-
	lib_load(lemma(evenlist)),
	select(evenlist),
	repeat intro,
	down(2), wfftacs,
	up, down(3), wfftacs,
	up, down(1), dplan, !, apply_dplan,
	top, display.

%%%%%%%%%%
% Not yet working. 
%

% Only rippling in the step case is currently working.
go(declemma) :-
	lib_load(lemma(declemma)),
	select(declemma),
	dplan(_,[Base,Step]),
	dplan(Step,_,[]).

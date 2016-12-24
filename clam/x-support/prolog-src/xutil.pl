/* General (additional) planning utilities for XCLaM 
 * @(#)$Id: xutil.pl,v 1.1 1994/09/16 09:45:29 dream Exp $
 *
 * $Log: xutil.pl,v $
 * Revision 1.1  1994/09/16 09:45:29  dream
 * Initial revision
 *
 */

/*
 * writef/3 provides the user interface for
 * targeting output to particular windows
 * in the context of xclam. The argument to
 * writef is a flag; currently one of: dialog,
 * plan and proof.
 * NB. writef switches back to the dialog window after
 * this means that an unqualified write will always go to the dialog
 * window.
 */
writef(Flag,Text,Control):-
    ww(Flag),
    writef(Text,Control).
ww(Window):-
    write('change_window'),write(Window),nl.

clear_ripple_window :-
    writef(ripple,'clear\n',[]).

print_nllist(Flag,L):- print_nllist(Flag,L,0,'|').
print_nllist(_,[],_,_).
print_nllist(Flag,[H|T],C,Ch) :-
    annotations(_,_,HH,H),
    writef(Flag,'%r%t\n',[Ch,C,HH]),
    print_nllist(Flag,T,C,Ch).

/*
 * toggle_ripple/0 and run_free/0 provide a mechanism
 * for swithing on and off the ripple window interrupt 
 */
:- dynamic run_free/0.

toggle_ripple:-
	run_free,
	retract(run_free).
toggle_ripple:-
	assert(run_free).
/*
 * Portray clauses for pretty printing come in a few flavours:
 * [1] few clauses suppress longwinded arguments to methods and
 *     methodicals.
 *     Portray/1 needs to be dynamic so we can assert extra clauses
 *     at runtime for iterated methods. For each iterator it/1 there
 *     will be portray-clauses:
 *         portray(it(L)) :- (var(L);L==[]), !, write(it(L)).
 *         portray(it(_)) :- write(it('[...]')).
 * [2] Pretty print wave-fronts
 * [3] (optional) pretty print defined Oyster terms.
 *
 * This is quite different for XCLaM since we want to use
 * fancy X11 fonts etc in the various graphics windows.
 * The communication between Prolog and the X interface is via
 * ESCAPE sequences.  All special commands are ESCAPED;  to send a
 * literal ESCAPE, send ESCAPE ESCAPE.
 *  
 * See init_colour.c for how these ESCAPES are interpreted, and for
 * how to add new ESCAPE commands.  Currently, there are escapes to 
 * change into a font containing symbols (eg \lambda, \forall) and
 * for changing the size of the text (for exponents etc).
 * Main use however is for printing wave-fronts. Currently this is
 * via colours only: in future we'll have boxes and holes.
 *
 * ESCAPE sequence is '$'
 * 
 * portray/1 is dependant upon whether we are writing in the 
 * ripple window, hence ripple_portraying/1.
 */
chr_write(N) :- name(A,[N]), ((A == '$', write(A), write(A)); write(A)).
chr_write_math(N) :-
    write('$m'),
    chr_write(N),
    write('$n').

:- dynamic portray/1.
        % [1]: methods etc:
portray('$') :- ripple_portraying(yes),!,write('$$').
portray(delta) :- ripple_portraying(yes),!,write('$md$n').
portray(epsilon) :- ripple_portraying(yes),!,write('$me$n').
portray(lambda(V,T)) :-
    ripple_portraying(yes),!,write('$ml$n'),write('('),
    print(V),write(','),print(T),write(')').
portray(X:T1=>T2) :- 
    ripple_portraying(yes),!,
    write('$m'), 
    chr_write(34), 
    write('$n'), 
    print(X),
    write('.'), 
    print(T2).
portray(X:T1#T2) :- 
    ripple_portraying(yes),!,
    write('$m'), chr_write(36), write('$n'), print(X), write('.'), print(T2).
portray((A = B in T)=>void) :- 
    ripple_portraying(yes),!,print(A) , 
    write('$m'),chr_write(185), 
    write('$n'), print(B).
portray(A = B in T) :- ripple_portraying(yes),!,print(A) , write(' = '), print(B).
portray(A => void) :-
    ripple_portraying(yes),!,
    write('$m'),chr_write(216), write('$n'), print(A).
portray(A => B) :-
    ripple_portraying(yes),!,
    print(A), write(' '),chr_write_math(174), write(' '), print(B).
portray(A # B) :-
    ripple_portraying(yes),!,
    print(A), write(' '),chr_write_math(217), write(' '),print(B).
portray(A \ B) :-
    ripple_portraying(yes),!,
    print(A), write(' '),chr_write_math(218), write(' '),print(B).

portray(base_case(I)) :-  write('base_case([...])').
portray(base_case(I)) :-  write('base_case('),
			  print(I),
			  write(')').

portray(step_case(I)) :-  write('step_case([...])').
portray(step_case(I)) :-  write('step_case('),
			  print(I),
			  write(')').

portray(ripple_and_cancel(Ms)) :- write('ripple_and_cancel([...])').
portray(ripple_and_cancel(Ms)) :- write('ripple_and_cancel('),
				  print(Ms),
				  write(')').

portray(tautology(_)) :- write('tautology(...)').
portray(tautology(T)) :- write(tautology(T)).

portray(elementary(_)) :- write('elementary(...)').
portray(elementary(T)) :- write(elementary(T)).

portray(sym_eval(I)) :-  write('sym_eval(...)').
portray(sym_eval(I)) :-  write(sym_eval(I)).

portray(normalize(L)) :- length(L,N),writef('normalize([%r])',['.',N]).
portray(normalize(L)) :- write(normalize(L)).

portray(fertilize(T,_)) :- write(fertilize(T,'[...]')).
portray(fertilize(T,Ms)) :- write('fertilize('),
			    write(T),write(','),
			    print(Ms),
			    write(')').

portray(fertilize_then_ripple(P)) :- print(P).
portray(fertilize_then_ripple(P)) :- write('fertilize_then_ripple('),
				     print(P),
				     write(')').


portray(fertilize_left_or_right(_,L)) :- write('fertilize('),
					 print(L),
					 write(')').
portray(fertilize_left_or_right(D,L)) :- write('fertilize_left_or_right('),
					 write(D),write(','),
					 print(L),
					 write(',').

portray(weak_fertilize(Dir,L)) :-
    length(L,N),writef('weak_fertilize(%t,[%r])',[Dir,'.',N]).
portray(weak_fertilize(Dir,L)) :- write(weak_fertilize(Dir,L)).

portray(ripple(_)) :- write('ripple(...)').
portray(ripple(Ms)) :- write('ripple('),print(Ms),write(')').

portray(ind_strat(induction(S,V) then _)) :- write(ind_strat(S,V)).
portray(ind_strat(induction(S,V) then CaseTacs)) :- 
			write(induction(S,V)),write('then'),print(CaseTacs). 

portray(ind_strat_I(induction_I(S,V) then _)) :- write(ind_strat_I(S,V)).
portray(ind_strat_II(induction_II(S,V) then _)) :- write(ind_strat_II(S,V)).

portray('$VAR'(N)) :- number(N),N1 is 64 + (N mod 26), name(C,[N1]),write(C).

portray(ih:[ihmarker(_,_),X]) :- write(X).

/* mods by img to simplify the parsing of xclam annotated colour terms
 * rather than writing out the colour after the term, write it before so
 * that re-parsing in C code (init_colour.c) is easier
 */
portray('@wave_var@'(Term)) :-
    ripple_portraying(yes),!,
    write('${[red];'),print(Term),write('$}').

/* ditto for fronts too.  Token after `` indicates
 * hard/soft front
 */
portray('@wave_front@'(hard,Dir,Term)) :-
    ripple_portraying(yes),!,
    write('$`'),
    write(Dir),
    write(';'),
    print(Term),
    write('$''').
portray('@wave_front@'(soft,_,Term)) :- 
    ripple_portraying(yes),!,
    write('"'),
    print(Term),
    write('"').
portray('@sink@'(Term)) :- 
    ripple_portraying(yes),!,
    chr_write_math(235),print(Term),chr_write_math(251).
/* and the old ones too */
portray('@wave_var@'(Term)) :-
    write('{'),print(Term),write('}').
portray('@wave_front@'(hard,Dir,Term)) :- 
    write('``'),
    print(Term),
    write(''''''),
    write('<'),
    write(Dir),
    write('>').
portray('@wave_front@'(soft,_,Term)) :- 
    write('"'),
    print(Term),
    write('"').
portray('@sink@'(Term)) :-
    write('\'),print(Term),write('/').



        % [3] (optional) pretty print some defined terms in the
        % object-level logic: 
portray('{}'(X)) :- print(X).

/* portray(plus(X,Y))   :- make_term(plus(X,Y),T),    print(T). */
portray(minus(X,Y))  :- make_term(minus(X,Y),T),   print(T).
/* portray(times(X,Y))  :- make_term(times(X,Y),T),   print(T). */
portray(leq(X,Y))    :- make_term(leq(X,Y),T),     print(T).
portray(geq(X,Y))    :- make_term(geq(X,Y),T),     print(T).
portray(less(X,Y))   :- make_term(less(X,Y),T),    print(T).
portray(greater(X,Y)):- make_term(greater(X,Y),T), print(T).
portray(exp(X,Y))    :- make_term(exp(X,Y),T),     print(T).

portray(X ^ Y) :-
    ripple_portraying(yes),!,print(X),write('$u'),print(Y),write('$d').
make_term(X,X) :- var(X),!.
/* make_term(plus(X,Y),XX+YY)   :- !, make_term(X,XX),make_term(Y,YY). */
make_term(minus(X,Y),XX-YY)  :- !, make_term(X,XX),make_term(Y,YY).
/* make_term(times(X,Y),XX*YY)  :- !, make_term(X,XX),make_term(Y,YY). */
make_term(leq(X,Y),XX=<YY)   :- !, make_term(X,XX),make_term(Y,YY).
make_term(geq(X,Y),XX>=YY)   :- !, make_term(X,XX),make_term(Y,YY).
make_term(less(X,Y),XX<YY)   :- !, make_term(X,XX),make_term(Y,YY).
make_term(greater(X,Y),XX>YY):- !, make_term(X,XX),make_term(Y,YY).
make_term(exp(X,Y),XX^YY)    :- !, make_term(X,XX),make_term(Y,YY).
make_term(X,X).

/*
 * Same as in CLAM/proof-planning/util.pl
 * only uses xdplan rather that dplan 
 * This really ought to be parameterized
 */
plan(Thm):-
	lib_load(thm(Thm)),
	slct(Thm),
	xdplan.
plan_all:-plan_all_with_normalize.

plan_all_with_normalize:-plan_all_with_normalize(_).

plan_all_with_normalize(Type):-
        load_ind_plan(2),
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,(example(Type,Thm,Status),
	             (\+ (Status=skip))),
                Thms),
        benchmark_plan(xdplan,Thms,noapply).

%% Now a new clause for benchmarking without normalize
%% Theorems whose status is given as needs_normalize in examples.pl
%% will not be attempted.

plan_all_without_normalize(Type):-
        load_ind_plan(4),           % induction; NOT normalize
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,
                 (example(Type,Thm,Status),
                  \+ Status=skip, \+ Status=needs_normalize),
                Thms),
        benchmark_plan(xdplan,Thms,noapply).


plan_from(First):- plan_from(_,First).
plan_from(Type,First):-
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
    	findall(Thm,(example(Type,Thm,Status),\+ Status=skip),Thms),
    	append(_,[First|Rest],Thms),
    	benchmark_plan(xdplan,[First|Rest],noapply).
plan_to(Last):- plan_to(_,Last).
plan_to(Type,Last):-
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
    	findall(Thm,(example(Type,Thm,Status),\+ Status=skip),AllThms),
    	append(From,[Last|_],AllThms),
	append(From,[Last],Thms),
    	benchmark_plan(xdplan,Thms,noapply).
prove(Thm):-
        plan(Thm),
	apply_plan.
%% This clause is for backwards compatibility
%%% prove_all_with_normalize/{0;1} is the old prove_all/{0;1}
prove_all:-prove_all_with_normalize.

prove_all_with_normalize:-prove_all_with_normalize(_).
prove_all_with_normalize(Type):-
        load_ind_plan(1),  % load default plan for benchmarking
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,(example(Type,Thm,Status),
                     \+ Status=skip),
                Thms),
        benchmark_plan(xdplan,Thms,apply).

%% Now a new clause for benchmarking without normalize
%% Theorems whose status is given as needs_normalize in examples.pl
%% will not be attempted.

prove_all_without_normalize:-prove_all_without_normalize(_).
prove_all_without_normalize(Type):-
        load_ind_plan(3),  % ind_strat; NOT normalize
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,(example(Type,Thm,Status),\+ Status=skip, \+ Status=needs_normalize),Thms),
        benchmark_plan(xdplan,Thms,apply).

prove_and_save_all:-
    prove_and_save_all_without_normalize(_),
    prove_and_save_all_with_normalize(_).

prove_and_save_all_without_normalize(Type):-
        load_ind_plan(3),  % ind_strat; NOT normalize
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,(example(Type,Thm,Status),\+ Status=skip, \+ Status=needs_normalize),Thms),
        benchmark_plan(xdplan,Thms,save).

prove_and_save_all_with_normalize(Type):-
        load_ind_plan(1),  % ind_strat and normalize
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
        findall(Thm,(example(Type,Thm,Status), Status==needs_normalize),Thms),
        benchmark_plan(xdplan,Thms,save).

prove_from(First):- prove_from(_,First).
prove_from(Type,First):-
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
    	findall(Thm,(example(Type,Thm,Status),\+ Status=skip),Thms),
    	append(_,[First|Rest],Thms),
    	benchmark_plan(xdplan,[First|Rest],apply).
prove_to(Last):- prove_to(_,Last).
prove_to(Type,Last):-
	lib_dir(Dir),
	concat_atom([Dir,'/','examples.pl'],File),
	file_exists(File),
	consult(File),
    	findall(Thm,(example(Type,Thm,Status),\+ Status=skip),AllThms),
    	append(From,[Last|_],AllThms),
	append(From,[Last],Thms),
    	benchmark_plan(xdplan,Thms,apply).

xprove_all:- run_free,
	     prove_all.
xprove_all:- assert(run_free),
	     prove_all.

apply_xdplan :-
    xdplan=:P,
    cthm=:Thm,!,
    writef(proof,'\n\nProof construction for %t:\n\n',[Thm]),
    apply_plan(P),
    ww(dialog).


do_one_benchmark(Planner,Thm,Dir,Apply) :-
    lib_load(thm(Thm),Dir),
    slct(Thm),
    (status(complete) ;
     writef(dialog,'CLaM WARNING: saved thm for %t incomplete\n',[Thm])
    ),
    Command =.. [Planner,Plan,[]], 
    !,
    (call(Command) 
      -> (writef(dialog,'\nPLANNING for %t COMPLETE. %f', [Thm] ),nl,nl,
	  print_plan(Plan),
	  assert(success(plan,Thm)),!,
	  nl,
	  ((Apply=apply;Apply=save)
	    -> ( apply_plan(Plan), 
		 ((status(complete);
		   status(complete(because)))
		   -> (writef(dialog,'\nPROOF for %t COMPLETE.\n', [Thm]),nl,
		       assert(success(proof,Thm)),
		       (Apply=save 
			 -> lib_save(thm(Thm),              % saves thm 
				     '~dream/meta-level/clam/clam.v2.1/lib-save')   % in buffer area
			 ; true 
		       ))
		   ; writef(proof,
			    '\nCLaM WARNING benchmark failed while executing plan on %t\n',[Thm]),
		  assert(failure(proof,Thm))
		 )
	   )
	    ; nl
	  )
     )
      ; writef(dialog,'CLaM WARNING benchmark failed while constructing plan on %t\n', [Thm]),
     assert(failure(plan,Thm))
    ), !.
/*
 * write a wave-rule underneath the sequent in the ripple window 
 */

/* ... but only if it is switched on */
:- dynamic wr_ripple/1.
wr_ripple(yes).

start_wr_ripple :-
    \+ wr_ripple(yes),
    retractall(wr_ripple(X)),
    asserta(wr_ripple(yes)).
stop_wr_ripple  :-
    \+ wr_ripple(no),
    retractall(wr_ripple(X)),asserta(wr_ripple(no)).

write_colour_wave_rule(Name,C=>L:=>R) :-
    wr_ripple(yes),
    ripple_portray_start,
    writef(ripple,'\n%t: %t -> %t ==> %t\n',
           [Name,C,'@wave_var@'(L),'@wave_var@'(R)]),
    ripple_portray_stop,
    delay_ripple.

write_colour_wave_rule(_,_).  /* no print if switched off */

toggle_colour :-
    wr_ripple(yes),
    !,stop_wr_ripple.
toggle_colour :-
    wr_ripple(no),
    !,start_wr_ripple.

plan_thm(Planner,Thm):-
    select(Thm),!,
    Planner.
plan_thm(Planner,Thm):-
    lib_load(thm(Thm)),
    select(Thm),
    Planner.

/*
 * unfold or fold the structure of a plan in the plan window
 */
toggle_formats_in_plan(Planner,Pos):-
    Planner =: Plan,
    method_at(Plan,Pos,Method),
    functor(Method,MName,MArity),
    toggle_format(MName/MArity),
    writef(dialog,'rewrite%t\n',[Method]),
    toggle_format(MName/MArity).

method_at(Method then _,[],Method).
method_at(_ then Methods,[Pos|PosL],Method):-
    nth1(Pos,Methods,SubMethods),
    method_at(SubMethods,PosL,Method).
method_at(Method,[],Method).


/*
 * this is a quick-and-dirty interface to the colouring
 * part of the c-parser.  Since we want both the hypothesis and
 * the non-in-hole part of the skeleton of the IC to be the same colour
 * (and we cant see it easily from the top-level) I construct a ColourList
 * containing all the colours present.  The mixing of these colours is 
 * done in XClam (init_colour.c), as usual.  This ColourList is passed to
 * XClam by wrapping both IH and IC in a wave-hole of the right colours.
 */

:- dynamic ripple_portraying/1.
ripple_portraying(no).
ripple_portray_start :- 
    \+ ripple_portraying(yes),
    retractall(ripple_portraying(X)),
    asserta(ripple_portraying(yes)).
ripple_portray_stop :-
    \+ ripple_portraying(no),
    retractall(ripple_portraying(X)),asserta(ripple_portraying(no)).

display_ripple(Method,Effects):-
    member(Method-Effects,[induction(_,_)-[_,H==>G],
			   induction(_,_)-[_,_,H==>G],
			   induction(_,_)-[_,_,_,H==>G],
			   induction(_,_)-[_,_,_,_,H==>G],
			   wave(_,_,_)-[H==>G],
			   unblock(_,_,_)-[H==>G],
			   generalise(_,_)-[H==>G],
			   fertilize(_,_)-[H==>G],
			   fertilize_left_or_right(_,_)-[H==>G]]),
    select(V:[ihmarker(Tag,_)|HYPS], H, _ ),
    /* avoid finding a indhyp thats been used */
    (var(Tag); (Tag = notraw(Tagger), var(Tagger))),
    /* map all of the hypotheses */
    findall(Id:Hyp,(member(Id:Hyp,HYPS)),HTagsSorted),!,
    matrix(_,IC,G),
    ripple_portray_start,
    ww(ripple),
    write('clear'),nl,
    process_hyp(1,HTagsSorted),
    writef(ripple,'IC: %t\n','@wave_var@'(IC)),
    ripple_portray_stop,
    delay_ripple,!.
display_ripple(_,_) :- !.
 
delay_ripple:- run_free.
delay_ripple:- ask(_).
process_hyp(1,[C:H|Rest]) :-
    !,
    writef(ripple,'H1: %t\n','@wave_var@'(H)),
    process_hyp(2,Rest).
process_hyp(2,[C:H|Rest]) :-
    !,
    writef(ripple,'H2: %t\n','@wave_var@'(H)),
    process_hyp(3,Rest).
process_hyp(3,[C:H|Rest]) :-
    !,
    writef(ripple,'H3: %t\n','@wave_var@'(H)),
    process_hyp(4,Rest).
process_hyp(4,[C:H|Rest]) :-
    !,
    writef(ripple,'H4: %t\n','@wave_var@'(H)),
    process_hyp(4,Rest).
process_hyp(_,[]) :- !.

/*
 * portray a wave-rule using the colour window in xclam;
 * uses wave_rule_match/4 to get a regular annotated wave-rule then 
 * grounds the colours, then send the resulting string off to the ripple
 * window.  How to represent meta-colours...?  
 */
colour_wr(Name,Type,C=>L:=>R) :-
    wave_rule_match(Name,Type,C=>L:=>R),
    ripple_portray_start,
    clear_ripple_window,
    grounding_subst(f(L,R)),
    writef(ripple,'%t: %t -> %t ==> %t\n',
           [Name,C,'@wave_var@'(L),'@wave_var@'(R)]),
    ripple_portray_stop.
grounding_subst(Term) :-
    free_meta_variables(FVs,Term),
    inj_subst(FVs,['S','T','U','V','W','X','Y','Z'],_,Term),!.

/*
 * inj_subst(Vars,Rng,RRng,Term)
 * there is an injective substitution from Vars to the range RRng (a 
 * subset of Rng) which grounds Term.
 */
inj_subst(Vars,Rng,RRng,Var) :- atom(Var),!.
inj_subst(Vars,Rng,RRng,Var) :-
    var(Var),
    member(VarNew,Vars),
    VarNew == Var,!,
    member(Element,Rng),
    copy(RRng,RRngCopy),
    make_ground(RRngCopy),
    \+ member(Element,RRngCopy),
    /* do the substitution */
    member(Element,RRng),
    Var = Element.

inj_subst(Vars,Rng,RRng,Var) :-
    var(Var),!.

inj_subst(Vars,Rng,RRng,App) :-
    App =.. [F|Args],
    inj_subst_list(Vars,Rng,RRng,Args).
inj_subst_list(Vars,Rng,RRng,[]).
inj_subst_list(Vars,Rng, RRng, [T|Ts]) :-
    inj_subst(Vars,Rng,RRng,T),
    inj_subst_list(Vars,Rng,RRng,Ts).

/*
 * free_meta_variables(V,T) V is the list (not set) of free variables
 * in term T
 */
free_meta_variables([V],V) :- metavar(V),!.
free_meta_variables([],C) :- atom(C),!.
free_meta_variables(Vs,T) :-
    T =.. [F|Args],
    free_meta_variables_list(Vs,Args).
free_meta_variables_list(VVs,[T|Ts]) :-
    free_meta_variables(V,T),
    free_meta_variables_list(Vs,Ts),
    append(V,Vs,VVs).
free_meta_variables_list([],[]).



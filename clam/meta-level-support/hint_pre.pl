/*
 * @(#)$Id: hint_pre.pl,v 1.5 1997/01/14 10:44:10 img Exp $
 *
 * $Log: hint_pre.pl,v $
 * Revision 1.5  1997/01/14 10:44:10  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.4  1996/08/01 10:51:33  img
 * Extend user interface: allow OR choices to be made (between different
 * branches previously computed via "a" command).
 *
 * Revision 1.3  1995/05/17  02:17:31  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:11  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: hint_pre.pl,v 1.5 1997/01/14 10:44:10 img Exp $').

/* 
 * This file load files and predicates needed to use the hint
 * planners.  Some of the predicates common to the planners
 * are defined in this file to avoid redefinition
 */

% Operator to chain plan.
:- op(500, xfy, [/\]).

%-------------------------------------------------------------------sny
% Name: next_methd/7.
%
% Arguments: 
%   1) Hint list (+).
%   2) Rest. List of remaining Hints after a method is selected (-).
%   3) Input sequent (+).
%   4) Method (?), usually (-).
%   5) Partial plan built so far (with marker) (+).
%   6) Path from root to current sequent in plan (+).
%   7) Desired Effects (?).
%
% Semantics: Method is the next applicable method/hint-method to Input and
%     Effects given the context defined by the other arguments. Rest contains
%     the remainig hints to be used in the following steps.
%
% Comments: The second clause is what the normal dplanner does, so if not hint 
%  is used (first clause), the normal dplan procedure will be folloed on 
%  backtrack.
%

next_mthd( Hints, Rest, Input, Method, Plan_so_far, Path, Effects ):-
    applicable_hints( Hints, Rest, Input, Method,  Plan_so_far, Path, Effects ).

next_mthd( Hints, Hints, Input, Method, _, _, Effects ):-
         applicable( Input, Method, _, Effects ).


%-------------------------------------------------------------------sny
% Name: applicable_hints.  
% 
% Arguments: 
% 1) Hint list (+).  
% 2) Rest.  List of remaining Hints after a method is selected (-).  
% 3) Input sequent (+).  
% 4) Method (?), usually (-).  
% 5) Partial plan built so far (with marker) (+).  
% 6) Path from root to current sequent in plan (+).  
% 7) Desired Effects (?).  
% 
% Semantics: Method is the next applicable Method/Hint-method to Input 
% and  Effects.  Rest is a list of the remaining hints.  
% Comments: The first clause deals with "imm_after" hints, and the 
% second clause  with "after" hints.  Rest1 is the Hints list without 
% the chosen hint.  Is is sent to get_hint because it might still be 
% edited interactively before  returning it to Rest.  The third and 
% four clauses deal with "always" hints.  They are just like imm_after 
% but the hint is retained in the list of hints after it has been applied.
% "imm_after" and "alw_imm_after" hints call the interactive option if 
% the stated position in the partial plan has been reached and the action 
% does not succeed. 
%



applicable_hints( Hints, Rest, Input, Method,  Plan_so_far, Path, Effects ):-
                select( imm_after( Meth, Action ), Hints, Rest1 ),
                last_mthd( Meth, Path ),
   (get_mthd( Action, Rest, Rest1, Input, Method, Plan_so_far, Path, Effects ) ;
   \+ member(Action,[askme,no(_)]),
    nl,write('------> Position: '),
          write(Meth),
          write(' reached.'),nl,nl,
    get_mthd( askme, Rest, Hints, Input, Method, Plan_so_far, Path, Effects )).

                
applicable_hints( Hints, Rest, Input, Method,  Plan_so_far, Path, Effects ):-
                select( after( Meth, Action ), Hints, Rest1 ),
                occurs( Meth, Path ),
     get_mthd( Action, Rest, Rest1, Input, Method, Plan_so_far, Path, Effects ).

applicable_hints( Hints, Rest, Input, Method,  Plan_so_far, Path, Effects ):-
                member( alw_imm_after( Meth, Action ), Hints ),
                \+ \+ last_mthd( Meth, Path ),
   (get_mthd( Action, Rest, Hints, Input, Method, Plan_so_far, Path, Effects ) ;
   \+ member(Action,[askme,no(_)]),
    nl,write('------> Position: '),
          write(Meth),
          write(' reached.'),nl,nl,
    get_mthd( askme, Rest, Hints, Input, Method, Plan_so_far, Path, Effects )).

applicable_hints( Hints, Rest, Input, Method,  Plan_so_far, Path, Effects ):-
                member( alw_after( Meth, Action ), Hints),
                \+ \+ occurs( Meth, Path ),
     get_mthd( Action, Rest, Hints, Input, Method, Plan_so_far, Path, Effects ).


%-------------------------------------------------------------------sny
% Name: get_mthd/8.
%
% Arguments:
%   1) An action (either no(Method), askme, method or hint-method ) (+).
%   2) List of remaining hints to be used aferwards (-).
%   3) Current list of hints (without the one in the first arg) (+).
%   4) Input sequent (+).
%   5) Method to be applied (-)
%   6) Plan built so far (+)
%   7) Path from root to current sequent (+).
%   8) Desired effects (?).
%
% Semantics: Method will be the next applicable method/hint-method to 
%   Input and Effects according to the given action and context.
%   arg 2 will contain the remaining hints after the current action is 
%   applied.
%
% Comments: no(Method) fails bacause it will cause the planning to continue.
%   It just adds to memory that Method should not be applied.
%


get_mthd( no(Method), R, R, _, Method, _, _, _ ):- assert( no(Method) ),
                                                                !, fail.

get_mthd( askme, Rest, RestI, Input, Method, Plan_so_far, Path, Effects ):- 
        % 
        %              MENU.
        %
	   display_options(Effects),
           select_option(Op),
           perform_action( Op, [ RestI, RestO, Input, 
                                  Method, Plan_so_far, Path, Effects ]  ),
           ( ((\+var(Method)), Rest=RestO)  |
             (!, get_mthd( askme, Rest, RestO, Input, 
                            Method, Plan_so_far, Path, Effects ))  ).
           

get_mthd( Hint, R, R, Input, Hint, _, _, Effects ):- 
             hint(Hint,_,_,_,_,_),
             app_notice(hint,Input, Hint, _, Effects ).

get_mthd( Method, R, R, Input, Method, _, _, Effects ):-
             method(Method,_,_,_,_,_),
             app_notice(method, Input, Method, _, Effects ).


%-------------------------------------------------------------------sny
% Name: Occurs/2.
% Arguments: 1) Path section. 2) Path.
% Semantics: Succeeds if 1) occurs in 2). i.e. if 1) is part of 2).
% Comments:
%



occurs( _, V ):- var(V), !, fail.

occurs( X, X ):-!.

occurs( M, M-_ ):- !.

occurs( M-B, M-B then _ ):- !.

occurs( M, M-_ then _ ):- !.

occurs( M-B then Section, M-B then Plan ):- occurs( Section, Plan ), !.

occurs( M then Section, M-_ then Plan ):- occurs( Section, Plan ), !.

occurs( X, _ then Plan ):- occurs( X, Plan ).



%-------------------------------------------------------------------sny
% Name: last_mthd.
% Arguments: 1) Path section. 2) Path.
% Semantics: Succeeds if 1) is the last part of Path.
% Comments:
%



last_mthd( _, V ):- var(V), !, fail.

last_mthd( X, X ).

last_mthd( M, M-_ ).

last_mthd( M-B then Section, M-B then Plan ):- last_mthd( Section, Plan ),!.

last_mthd( X, _ then Plan ):- last_mthd( X, Plan ).



%-------------------------------------------------------------------sny
% Name: add_branch/3
% Arguments: 1) Branch (number). 2) Path. 3) Path.
% Semantics: 3) is 2) with 1) labeling its last method.
% Comments:
%




add_branch(Branch, M then Path, M then NewPath):- !, 
                                   add_branch(Branch, Path, NewPath).

add_branch(Branch, Method, Method-Branch).



%-------------------------------------------------------------------sny
% Name: concat_method/3.
% Arguments: 1) Path, 2) Method, 3) Path.
% Semantics: 3) is 1) with 2) added as its last method.
% Comments:
%

concat_method(M then Path, Method, M then NewPath):-!,
                                             concat_method(Path,Method,NewPath).

concat_method(Method, NewMethod, Method then NewMethod).



%-------------------------------------------------------------------sny
% options. (t)est method/hint
%          (pro)log,
%          (seq)uent.
% 	   (pla)n.
%          (c)ontexts.
%          (a)pplicable methods,
%          (e)dit hint list.
%          (sel)ect method.
%          (r)esume
%          (h)elp.

options([ t, pro, seq, pla, c, a, e, sel, r, h ]).


%-------------------------------------------------------------------sny
% menu. Headings for the help menu.

menu([ 'Test Method/Hint',
       'Prolog access',
       'Display current sequent',
       'Display partial plan',
       'Display hint contexts',
       'Applicable methods',
       'Edit hint list',
       'Select method',
       'Resume',
       'Help'                      ] ) .



%-------------------------------------------------------------------sny
% actions. Predicates corresponding to each item in menu.

actions([ test_method,
          prolog_meta,
          display_seq,
          display_plan,
          display_contexts,
          app_methods,
          edit_hints,
          select_option,
          resume,
          help_option       ] ) .




%-------------------------------------------------------------------sny
% Name: display_options/1.
%
% Arguments: 1) Effects.
% 
% Semantics: Display brief menu on the screen as side effecs and also shows
%   the desired output is if it is a groud term.
%
%  Comments:
%




display_options(Effects):- nl,
                   (\+ground(Effects) | 
			write('Looking for effects: '),
		    write(Effects),nl),
                  options(O), 
                  write(O), 
                  write(' <?> '),!.



%-------------------------------------------------------------------sny
% Name: select_option/1
%
% Arguments: 1) Option (constant).
% 
% Semantics: Prompts the user for h/is/er (its (?)) option.
% Comments: Returns Op = error if the user chose an invalid option.
%



select_option(OP):- options(Ops), read(OP), member(OP,Ops),!.
select_option(error):- nl,write('Illegal option'),nl.
       

%-------------------------------------------------------------------sny
% Name: perform_action/2
%
% Arguments: 1) option, 2) List of Parameters.
%
% Semantics: Calls the appropriate predicate according to the given
%   option. If option is invalid (error), it doen't do anything.
%
% Comments: error doen't do anything because it will go back to 
%   get_mthd(askme... and will cycle again.
%   Params are not used here so they are kept wrapped and are sent along.
%

perform_action(error,[R,R,_,_,_,_,_]):-!.
perform_action(Op, Params):- 
                             options(O),
                             actions(A),
	                     get_action(Op,O,A,Ac),
                             Goal =.. [Ac|Params],
                             nl,nl,nl,
                             Goal.



%-------------------------------------------------------------------sny
% Name: get_action/4.
%
% Arguments: 
%    1) option (constant), 
%    2) list of options, 
%    3) list of actions,
%    4) action.
%
% Semantics: 4) is the corresponding action in 3) to 1) in 2).
% Comments:
%

get_action(Op,[Op|_],[Ac|_],Ac):-!.
get_action(Op,[_|Ops],[_|Acs],Ac):- get_action(Op,Ops,Acs,Ac).


% ################ OPTION PREDICATES #################################
%
% These predicates are the corresponding action of the option in the
% askme menu.
%
% They all have the same arguments:
%
%   1) List of remaining hints to be used aferwards (-).
%   2) Current list of hints (without the one in the first arg) (+).
%   3) Input sequent (+).
%   4) Method to be applied (-)
%   5) Plan built so far (+)
%   6) Path from root to current sequent (+).
%   7) Desired effects (?).
%


%-------------------------------------------------------------------sny
% Name: test_method/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Asks the user for a method and tests its applicablitiy.
%   see test/3 below.
%
% Comments: Returns the list of remaining hints unchanged.
%

test_method(R,R,Input,_,_,_,_):-  write('Method/Hint ?:'),
                                      read(Method),nl,
                                      present(Method),
                                      test(Method,Input,_).






%-------------------------------------------------------------------sny
% Name: prolog_meta.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: (too) simple interface to prolog.
%
% Comments: Returns list of remaining hints unchanged.
%

prolog_meta(R,R,_,_,_,_,_):- (repeat), 
                             write('<prolog ?> '),
                             read(C),nl,
                             call_once(C),
                             C = true.


%-------------------------------------------------------------------sny
% Name: display_seq/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Prints current sequent.
%
% Comments: Returen list of remaining hints unchanged.
%

display_seq(R,R,Input,_,_,_,_):- print_seq(Input),nl,nl.



%-------------------------------------------------------------------sny
% Name: display_plan/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Displays the plan built so far showing where the current
%   planning is being done.
%
% Comments: Returns the list of remaining hints unchanged.
%



display_plan(_,_,_,_,Plan/\'<current>',_,_):- print_plan(Plan),nl,nl,fail.
display_plan(R,R,_,_,_,_,_).



%-------------------------------------------------------------------sny
% Name: display_contexts/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Displays the hint contexts.
%
% Comments: If the system is compiled, then listing might not work.
%   Returns the list of remaining hints unchanged.
%



display_contexts(R,R,_,_,_,_,_):- listing(hint_context),nl,nl.



%-------------------------------------------------------------------sny
% Name: app_methods/7
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Displays all applicable methods and hint-methods to Input
%   with desired Effects.
%
% Comments: Effects (7th arg) is not instantiated. Returns the list of
%   remaining hints unchanged.
%

app_methods(_,_,Input,_,_,_,Effects):- 
    write('Methods: '),nl,
    app_methods_(Input,Effects,EMs,EMPEs),
    retractall(htplan/1),
    asserta(htplan(EMPEs)),
    prlist(EMs),
    fail.
app_methods(_,_,Input,_,_,_,Effects):- 
    nl,nl,write('Hints: '),nl,
    applcble(hint,Input,H,_,Effects),
    print(H),nl,fail.

app_methods(R,R,_,_,_,_,_).


app_methods_(Input,E,EMs,EMPEs) :-
    findall(M-P-E, applicable(Input,M,P,E),Ms),
    app_methods__(1,Ms,EMs,EMPEs). 
app_methods__(_,[],[],[]).
app_methods__(N,[(M-P-E)|Ms],[N-M|EMs],[(N-(M-P-E))|EMPEs]) :-
    NN is N + 1,
    app_methods__(NN,Ms, EMs,EMPEs).

%-------------------------------------------------------------------sny
% Name: edit_hints/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: RestO is RestI edited by the user through edit_list.
%
% Comments:
%



edit_hints(RestI,RestO,_,_,_,_,_):- edit_list(RestI,RestO).



%-------------------------------------------------------------------sny
% Name: select_option/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Asks user for method/hint-method and  verifies it is applicable 
%    to Input and Effects. Returns the given method if succeeds or writes
%    notice if method/hint-method is not applicable.
%
% Comments: Returns the list of remaining hint unchanged.
%



select_option(R,R,Input,Method,_,_,Effects):- write('Method/Hint (or number)? '),
                                      read(Method1),nl,
    integer(Method1) -> 
    select_option_(Method1,R,R,Input,Method,_,_,Effects);
                                          \+ \+ present(Method1),
                                    (applicable(Input,Method1,_,Effects),
                                       Method = Method1  ;
                                       \+ var(Method1),
                                       applcble(hint,Input,Method1,_,Effects),
                                       Method = Method1 ;
                                       write('Method '),
                                       write(Method1),
                                       write(' not applicable'),nl).
select_option_(N,R,R,_,Method,_,_,Effects) :-
    htplan(Poss),
    member(N-(Method-_-Effects),Poss).
%-------------------------------------------------------------------sny
% Name: Resume/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: fails. Forces backtrack to continue normal planning.
%
% Comments:
%

resume(_,_,_,_,_,_,_):- fail.

%-------------------------------------------------------------------sny
% Name: help_option/7.
%
% Arguments: (see above: Option Predicates).
%
% Semantics: Displays explanation of options.
%
% Comments: Returns the list of remaining hints unchanged.
%

help_option(R,R,_,_,_,_,_):- options(O),
                             menu(M),
                             display_menu(O,M).



% ################ END OF OPTION PREDICATES #########################


%-------------------------------------------------------------------sny
% Name: display_menu/2.
%
% Arguments: 1) list of options 2) (corresponding) list of explanations.
%
% Semantics: Displays explanations.
%
% Comments:
%

display_menu( [], _ ):-nl,nl,nl.

display_menu( [O|Ops],[M|Ms]):- write('<'),write(O),write('> '),
                                write(M),nl,
                                display_menu(Ops,Ms).


%-------------------------------------------------------------------sny
% Name: display_list/1.
%
% Arguments: A list.
%
% Semantics: Prints the list
%
% Comments:
%

display_list([]):-nl.
display_list([H|T]):- write(H),nl,display_list(T).



%-------------------------------------------------------------------sny
% Name: no/1.
%
% Comments: dynamic declaration of no/1.
%
% no nothing. i.e. everything.

:- dynamic no/1.

no(nothing).



%-------------------------------------------------------------------sny
% Name: test/3.
%
% Arguments: 1) Method/Hint-method 2) Sequent 3) Output (-)
%
% Semantics: Test the applicability of 1) to 2) and 3). Displays all
%   successfully applied preconditions, postconditions, and output.
%
% Comments: If the method is not applicable, it backtrack until the last
%   possible instantiations of preconditions has been exhausted, and
%   then print the last instantiation of the successful preconditions.
%   No postconditions or output are displayed if not all preconditions
%   succeed.
%

test(Method, Input, Out):- 
                     member(Type,[method,hint]),
                     Term =.. [Type, Method, Input, Pre, Pos, Out, _],
                     Term,
                     apply_all(Pre,X/\X,L,Res),
                     write('Preconditions tried: '),nl,nl,
                     pp_term(L),nl,nl,
                     Res = all,
                     apply_all(Pos,Y/\Y,L1,Res1),
                     write('Postconditions tried: '),nl,nl,
                     pp_term(L1),
                     Res1 = all,
                     write('Output: '),nl,nl,
                     pp_term(Out),nl,nl.

test(_,_,_).



%-------------------------------------------------------------------sny
% Name: tried/1.
%
% Semantics: initial value of dynamic predicate tried.
%

:-dynamic tried/1.

tried([]/\_).



%-------------------------------------------------------------------sny
% Name: Apply_all/4.
%
% Arguments:
%   1) List of goals (+).
%   2) Goals applied so far (+).
%   3) Sublist of goals (-).
%   4) Message ( either all of not_all ).
%
% Semantics: 3) is the sublist of 1) of the successfully applied goals.
%   4) is all if all goals in 1) succeed and not_all otherwise.
%
% Comments: This predicated saves in memory as tried(L) the list of
%   successfully applied goals, recovers them if needed (clause 3) and 
%   deletes them at the end (clauses 1 and 3).
%



apply_all( [], Sofar/\[], Sofar, all ):- abolish(tried/1),
                                         assert(tried([]/\_)),!.

apply_all( [ H | T ], Sofar/\[ H | Next ], Tried, Message ):-
          H,
          asserta(tried(Sofar/\Next)),
          apply_all( T, Sofar/\Next, Tried, Message ), !.

apply_all( _, _, Tried, not_all ):- tried( Tried/\['<end_of_evaluation>'] ),
                                    abolish(tried/1),
                                    assert(tried([]/\_)),!.


%-------------------------------------------------------------------sny
% Name: pp_term/1.
%
% Arguments: A term.
%
% Semantics: (not very) pritty prints the argument.
%
% Comments: It doesn't split declared operators, so too complex 
%    expressions using them will be printed in a single (unreadable) line.
%



pp_term(Term):- pp_term(Term,0).

pp_term(Term,Tab):- var(Term),!,
                    tab(Tab),
                    write(Term),nl.


pp_term([H|T],Tab):- !, tab(Tab),
                        write('['),nl,
                        Tab1 is Tab+2,
                        pp_list([H|T],Tab1),
                        tab(Tab),
                        write(']'),nl.



pp_term(Term,Tab):- Term \= [],
                    Term =.. [ O | [Non|Empty] ],
                    \+current_op(_,_,O),!,
                    tab(Tab),
	            write(O),
                    write('('),nl,
                    Tab1 is Tab+3,
                    pp_list( [Non|Empty] ,Tab1).

pp_term(Term,Tab):- tab(Tab), print(Term),nl.



%-------------------------------------------------------------------sny
% Name: pp_list/1
%
% Arguments: A list.
%
% Semantics: Prints each element of arg in a different line.
%


pp_list([],_).

pp_list([H|T],Tab):- pp_term(H,Tab),pp_list(T,Tab).                     



%-------------------------------------------------------------------sny
% Name: edit_list/2.
%
% Arguments: 1) A list (+), 2) A list (?), usually (-).
%
% Semantics: General list editor. 2) is the edited version of 1).
%



edit_list( IList, OList ):-
         write(IList),nl,
         write('[ i(n), (u)ndo, (a)dd, (d)elete, (q)uit ] <?> '),
         read(Op),
         (Op=u -> (!,fail);true),
         edit_list( IList, OList, Op ),!.

edit_list( IList, OList ):- edit_list( IList, OList ).



%-------------------------------------------------------------------sny
% Name: edit_list/3.
%
% Arguments: 1) A list (+), 2) A list (-), 3) Option (constant).
%
% Semantics: Auxiliar predicate for edit_list/2. Decides what to do
%    in each case (option) and calls recursively edit_list/2.
%

edit_list( [ H | T ], [ H | T1 ], i ):- edit_list(T,T1).

% edit_list( _, _, o ):- fail.

edit_list( IList, OList, a ):- nl,
                    write('New element for the list <?> '),
                    read(New),nl,
                    all_present([New]),
                    edit_list( [ New | IList ], OList ).

edit_list( [ _ | T ], OList, d ):- edit_list( T, OList ).

edit_list( L, L, q ).



%-------------------------------------------------------------------sny
% Name: call_once/1.
%
% Arguments: 1) A goal.
%
% Semantics: Applies once the goal and prints result.
%    
%

call_once(Goal):- vars_in(Goal,[],Varlist),
                  count_vars(1,Varlist,Varlist1),
                  Goal, !, 
                  pp_list(Varlist1,0),
% nl,nl,pp_term(Goal),nl,nl,
                  nl, write('-yes'),nl.
call_once(_):- nl, write('-no'), nl.


%-------------------------------------------------------------------sny
% Name: vars_in/4 and vars_in_list/4
%
% Arguments: 1) A Term (+)
%            2) A number (+)
%            3) A list (+)
%            4) A list (-)
%
% Semantics: These two predictes return in 4) the list of all variables in
%             1) indexed by a number.
%


vars_in(Term,Sofar,[Term]):-var(Term),
                  \+ (member(T,Sofar),T==Term),!.

vars_in(Term,_,[]):-var(Term),!.

vars_in([Nonempty|List],Sofar,Varlist):- !,
                  vars_in_list([Nonempty|List],Sofar,Varlist).

vars_in(Term,Sofar,Varlist):- \+atom(Term),!,
                  Term =.. [_|List],
                  vars_in_list(List,Sofar,Varlist).

vars_in(_,_,[]).


vars_in_list([],_,[]).

vars_in_list([H|T],Sofar, Varlist):-
         vars_in(H,Sofar,L1),
         append(L1,Sofar,Newsofar),
         vars_in_list(T,Newsofar, L2),
         append(L1,L2,Varlist).

var_in_list([_|T],Sofar,Varlist):-
         vars_in_list(T,Sofar,Varlist).


%-------------------------------------------------------------------sny
% Name: count_vars/3
%
% Arguments: 1) A number (+)
%            2) A list (+)
%            3) A list (-)
%
% Semantics: 3) is the list of variables 2) but all elements numbered 
%            starting from 1).
%
         
count_vars(_,[],[]).

count_vars(N,[H|T],[var(N)=H|T1]):- N1 is N+1, count_vars(N1,T,T1).

  
%-------------------------------------------------------------------sny
% Name: all_present/1 
% 
% Arguments: 1) A list 
%
% Semantics: all_present succeed if all action parts (2nd. arg) of the 
%            elements of the list are either methods or hint-methods in 
%            the current databases.

all_present([]):-!.

all_present([ H | R ]):- H =.. [F,_,M],!,
                         member(F, [after,imm_after,alw_imm_after,
                                    alw_after]),
                         ( member(M, [no(_),askme]),! ; present(M) ),
                         all_present(R).

all_present([X|_]):- nl,nl,
                 write(X),
                 write(' is an illegal hint.'),
                 nl,nl,fail.

%-------------------------------------------------------------------sny
% Name: present/1
%
% Arguments: 1) (hint-)method.
%
% Semantics: Succeds if 1) is present, either in the methods db or in 
%            the hints db. Reports if it doesn't succeed.

present(M):- method(M,_,_,_,_,_),!.
present(H):- hint(H,_,_,_,_,_),!.
present(X):- nl,nl,write(X),
                   write(' is not present in current data bases. '),
             nl,nl.


%-------------------------------------------------------------------sny
% Name: app_notice/5.
%
% Arguments: Same as applcble.
%
% Semantics: The predicate is just like applcble/5 but it also
%            reports on the screen when applcble fails.

app_notice(Type,Input,Method,Effects,Output):-
           ( applcble(Type,Input,Method,Effects,Output),! ;
             nl,nl,write(' (Hint-)Method: '),
                   write(Method),
                   write(' is not applicable for '),
                   write(Output),
                   write(' effects.'),nl,fail).




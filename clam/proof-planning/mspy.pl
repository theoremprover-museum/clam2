/*
 * @(#)$Id: mspy.pl,v 1.5 1997/10/09 14:58:52 img Exp $
 *
 * $Log: mspy.pl,v $
 * Revision 1.5  1997/10/09 14:58:52  img
 * call_conjunction/1 replaced with call_precondition/1
 *
 * Revision 1.4  1997/01/14 10:45:24  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:02  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:29  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: mspy.pl,v 1.5 1997/10/09 14:58:52 img Exp $').

/* Note: mspy is current not used.
 *
 * This file contains procedures that reason about/with the methods
 * specified in the file method.pl, and contains such things as: is a
 * particular method applicable, which methods are applicable, what
 * would be the results of a method if we applied it, etc.  The
 * difference between this file and ``applicable'' is that this
 * one contains code to support the placing of pseudo-spy points
 * on methods.   This code is not include as standard because it
 * significantly slows down the proof-planning process.
 */

?- dynamic mspy_point/2 .

/*
 * The main predicate is applicable/[1;2;3;4] and the corresponding
 * applicable_submethod/[1;2;3;4] for submethods. 
 * The predicates applicable/{1,2} check if a method is applicable
 * (either to current sequent or to a specified sequent), and
 * the predicates applicable/{3,4} check if a method is applicable
 * (either to current sequent or to a specified sequent), but also
 * compute what the effects- and output-slots would be if the method
 * were applied.
 *
 * In order to avoid a lot of repetition between the clauses for methods
 * and submethods, we map both applicable/n and applicable_submethod/n
 * into applcbl/n+1 (n=1,2,3,4) which does the work for both, but
 * distinguishes between methods and submethods on the basis of an extra
 * first argument.
 *
 * Also, the clauses for the methodicals try/1, then/2 and or/2 live in the
 * file methodical.pl, and we map the relevant cases of applcble/n to
 * applicable_{try,then,or}/n. 
 */

applicable(Method) :- applcble(method,Method).
applicable(Input,Method) :- applcble(method,Input,Method).
applicable(Method,Post,Effects) :- applcble(method,Method,Post,Effects).
% Switch dynamic declaration on for taking stats (nodesvisited)
% :- dynamic applicable/4.
applicable(Input,Method,Post,Effects) :-
    applcble(method,Input,Method,Post,Effects).

applicable_submethod(Method) :- applcble(submethod,Method).
applicable_submethod(Input,Method) :- applcble(submethod,Input,Method).
applicable_submethod(Method,Post,Effects) :-
    applcble(submethod,Method,Post,Effects).
applicable_submethod(Input,Method,Post,Effects) :-
    applcble(submethod,Input,Method,Post,Effects).


/*
 * applcbl/[1;2;3;4] does the real work for both applicable/[1;2;3;4]
 * and applicable_submethod/[1;2;3;4].
 * From now on, for "Method", read "Method or Submethod depending on the
 * first argument".
 */

        % applcble(+Type,?Method) checks if Method is applicable in the
        % current context. Notice that Method can be partially or wholly
        % uninstantiated, so that applcbl/1 can be used to search for
        % all applicable methods. 
        %
        % First clause for human consumption only: provides Input
        % automatically using the current goal and hypothesis list.
applcble(Type,Method) :-
    goal(Input), hyp_list(H),
    applcble(Type,H==>Input,Method).
        % For the try/1 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of try/1 methodical.
applcble(Type,Input,Try_Method) :-
    functorp(Try_Method,try,1), !,
    applicable_try(Type,Input,Try_Method).
        % For the then/2 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of then/2 methodical.
applcble(Type,Input,Then_Method) :-
    functorp(Then_Method,then,2),!,
    applicable_then(Type,Input,Then_Method).
        % For the or/2 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of or/2 methodical.
applcble(Type,Input,Or_Method) :-
    functorp(Or_Method,or,2), !,
    applicable_or(Type,Input,Or_Method).
        %
applcble(Type,Input,Method) :-
    apply(Type,[Method,Input,Pre,_,_,_]),
    plantraced(30,writef('trying %t %t...\n',[Type,Method])),
    call_precondition(Pre).

        % applcble(+Type,?Input,?Method, ?Post,?Effects): succeeds if Method is
        % applicable on Input and Post and Effects are the resulting
        % postconditions and effects. Possible usage includes
        % applcble(+,+,+,-,-) to compute postconds/effects of a given method,
        % applcble(+,+,-,-,-) to search for applicable methods , and
        % applcble(+,+,-,-,+) or applcble(+,+,-,+,-) to search for methods
        % that will give certain desired postconditions/effects. 
        %
        % applcbl/5 subsumes applcbl/3, but is more expensive.
        % Therefore we keep applcbl/3 around anyway.
        % 
        % We cant get away with just calling applcbl/3, but rather
        % have to explicitly call the body of applcbl/3 as the 
        % first two conjuncts in order to bind the local variables in
        % the definition of Method. This is rather unfortunate.
        %
        % Again, first clause for human consumption only: provides Input
        % automatically using the current goal and hypothesis list.
applcble(Type,Method,Post,Effects) :-
    goal(Input), hyp_list(H),
    applcble(Type,H==>Input,Method,Post,Effects).
        % For the try/1 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of try/1 methodical.
applcble(Type,Input,Try_Method,Post,Effects) :-
    functorp(Try_Method,try,1), !,
    applicable_try(Type,Input,Try_Method,Post,Effects).
        % For the then/2 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of then/2 methodical.
applcble(Type,Input,Then_Method,Post,Effects) :-
    functorp(Then_Method,then,2), !,
    applicable_then(Type,Input,Then_Method,Post,Effects).
        % For the or/2 methodical we call special-case code defined in
        % methodical.pl. See there for semantics of or/2 methodical.
applcble(Type,Input,Or_Method,Post,Effects) :-
    functorp(Or_Method,or,2), !,
    applicable_or(Type,Input,Or_Method,Post,Effects).
        %
applcble(Type,Input,Method,Post,Effects) :-
    mspy_redo( node_redo, _Dummy ),
    on_backtracking (recorded(mspy_msg,savenode,Ref),
                     erase(Ref),
                     savednode := Input,
                     ttywrite( 'savednode := <Current node>' ),
                     ttynl ),
    on_backtracking (recorded(mspy_msg,plannode,Ref),erase(Ref),fail),
    applcble1(Type,Input,Method,Post,Effects).

applcble1(Type,Input,Method,Post,Effects) :-
    apply(Type,[Method,Input,Pre,Post,Effects,_]),
    mspy_ports( Method, Type, PrePorts, PostPorts ),
    functor( Method, M, A ),
            plantraced(30,( functor(Method, M, A),
                            writef('  Trying %t %t\n',[Type,M/A]))),
            plantraced(40,writef('    Trying preconds...%f')),
    on_backtracking plantraced(40,writef('Preconds of %t %t failed\n',
                                         [Type,M/A])),
    ( true ; 
      recorded( mspy_msg, plannode, _ ),!,fail
    ),
    mspy_redo( cond_redo, _Dummy1 ),
    call_conj(Pre, PrePorts, M/A, precondition ),
            plantraced(40,writef('Preconds succeeded...%f')),
    on_backtracking plantraced(40,writef('    Retrying preconds of %t %t...%f',
                                        [Type,M/A])),
    ( true ; 
      recorded( mspy_msg, plannode,_),!,fail
    ),
    mspy_redo( cond_redo, _Dummy2 ),
    call_conj(Post, PostPorts, M/A, postcondition),
            plantraced(40,writef('Postconds succeeded\n')).

call_conj( Conj, [], _, _ ) :-
    !,
    call_precondition( Conj ).
call_conj( Conj , Ports, Method, Place ) :-
    call_conj1( Conj, Ports, Method, Place ).
call_conj( _, Ports, Method, Place ) :-
    \+ recorded( mspy_msg, plannode, _ ),
    \+ recorded( mspy_msg, cond_redo, _ ),
    !,
    do_mspy_port( fail, Ports, Method, Place ),
    fail.


call_conj1( Conj, Ports, Method, Place ) :-
    (do_mspy_port( call, Ports, Method, Place ), !, fail ; true ),
    call_conj2( Conj ),
    ( true ; 
      ( do_mspy_port( redo, Ports, Method, Place ),!,fail ; fail )
    ),
    ( do_mspy_port( exit, Ports, Method, Place ),!,fail ; true ).

call_conj2( Conj ) :-
    recorded(mspy_msg,creap,Ref),
    erase(Ref),
    !,
    call_precondition( (trace,Conj) ).
call_conj2( Conj ) :-
    call_precondition( Conj ).





        % applicable_anymethod/[1,2,3,4] represent the union of
        % applicable[1,2,3,4] and applicable_submethod/[1,2,3,4].
        %
        % Included more for completeness than for usefulness...
applicable_anymethod(Input,Method,Postconds,Effects) :-
    applicable(Input,Method,Postconds,Effects).
applicable_anymethod(Input,Method,Postconds,Effects) :-
    applicable_submethod(Input,Method,Postconds,Effects).

applicable_anymethod(Method,Postconds,Effects) :-
    applicable(Method,Postconds,Effects).
applicable_anymethod(Method,Postconds,Effects) :-
    applicable_submethod(Method,Postconds,Effects).

applicable_anymethod(Input,Method) :- applicable(Input,Method).
applicable_anymethod(Input,Method) :- applicable_submethod(Input,Method).

applicable_anymethod(Method) :- applicable(Method).
applicable_anymethod(Method) :- applicable_submethod(Method).

mspy_redo( _,_ ).
mspy_redo( X,_ ) :-
    recorded( mspy_msg,X,Ref ),
    erase(Ref),
    mspy_redo(X, _ ).


mspy_ports( Pat, Type, PrePorts, PostPorts ) :-
    mspy_point( Pat, d([Type, PrePorts, PostPorts]) ),
    !.
mspy_ports( _, _, [], [] ).

mspy( Pat ) :-
    mspy( Pat, _ ).

mspy( M / A, [Kind, PrePorts, PostPorts] ) :-
    ( Kind = mthd, Type = method ;  Kind = smthd, Type = submethod),
    LibId =.. [ Kind, M / A ],
    lib_present( LibId ),
    ( pre_ports =: PrePorts ; true ),
    ( post_ports =: PostPorts ; true ),
    functor( Pat, M, A),
    retractall( mspy_point( Pat, _ ) ),   
    asserta( mspy_point( Pat, d([Type, PrePorts, PostPorts]) ) ),
    ttywrite( 'Method spy-point placed on: ' ),
    ttywrite( M / A ),
    ttynl,
    !.

mspy( Pat, [Kind, PrePorts, PostPorts] ) :-
    ( Kind = mthd, Type = method ;  Kind = smthd, Type = submethod),
    LibId =.. [ Kind, M / A ],
    lib_present( LibId ),
    ( pre_ports =: PrePorts ; true ),
    ( post_ports =: PostPorts ; true ),
    functor( Pat, M, A),
    retractall( mspy_point( Pat, _ ) ),   
    asserta( mspy_point( Pat, d([Type, PrePorts, PostPorts]) ) ),
    ttywrite( 'Method spy-point placed on: ' ),
    ttywrite( M / A ),
    ttynl,
    !.    

mspy( M / A, _ ) :-
    ttywrite( 'No such (sub)method ' ),
    ttywrite( M / A ),
    ttywrite( ' is loaded!' ),
    ttynl,
    fail.

nomspy( M / A ) :-
    !,
    functor(Pat,M,A),
    retractall( mspy_point( Pat, d(_) ) ).

mspy_point( dummy, dummy ).

?- pre_ports := [call,redo,exit,fail].
?- post_ports := [call,redo,exit,fail].


     

do_mspy_port( Port, Ports, Method, Comp ) :-
    member( Port, Ports ),
    ttywrite( '**Reached ' ),
    ttywrite( Comp ),
    ttywrite( ' ' ),
    ttywrite( Port ),
    ttywrite( ' port on method ' ),
    ttywrite( Method ),
    get_mspy_comm( Input, Method ),
    !,
    do_mspy_comm(Input).

get_mspy_comm( Input, Method ) :-
    (repeat),
    ttynl,
    ttywrite( ' [rRfFSla@-]' ),
    ask(X),
    name( NX, [X] ),
    ( call( ( NX = '@' -> do_subcall, fail ; true ) ),
      call( ( NX = '-' -> nomspy(Method), fail ; true ) ),
      Input = NX, !
    ).


tidy_mspy :- recorded(mspy_msg,_,Ref),erase(Ref),fail.
tidy_mspy.
do_mspy_comm(a) :- tidy_mspy,
                    abort.           
do_mspy_comm('R') :-
    recorda(mspy_msg,plannode,_),
    recorda(mspy_msg,node_redo,_),!.
do_mspy_comm(r) :-
    recorda(mspy_msg,cond_redo,_),!.
do_mspy_comm('S') :-
    recorda(mspy_msg,plannode,_),
    recorda(mspy_msg,node_redo,_),
    recorda(mspy_msg,savenode,_),!.
do_mspy_comm('F') :-
    recorda(mspy_msg,plannode,_),!.
do_mspy_comm(f) :- !.
do_mspy_comm(l) :- !,recorded(mspy_msg,_,Ref),erase(Ref),fail.
do_mspy_comm(_) :- recorded(mspy_msg,_,Ref),erase(Ref),fail.
do_mspy_comm(_) :-
    recorda(mspy_msg,creap,_),
    !,
    fail.

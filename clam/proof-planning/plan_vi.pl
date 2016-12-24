/*
 * @(#)$Id: plan_vi.pl,v 1.4 1997/01/14 10:45:38 img Exp $
 *
 * $Log: plan_vi.pl,v $
 * Revision 1.4  1997/01/14 10:45:38  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:17  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:15:59  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:19:36  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: plan_vi.pl,v 1.4 1997/01/14 10:45:38 img Exp $').

/*
 * Visual planner:
 * 
 * Same algorithm as iterative deepening planner (see plan-id.pl), but
 * produces visually actractive tracing output.
 * 
 * Contributed by Geraint Wiggins.
 *
 * I didn't do any further checks or improvements, but just took it as
 * it was, with the exception of some trivial improvements listed below.
 * I don't like some of the code on first sight (communication
 * by glabal variables, for instance), and 0 comments, so see Geraint
 * for any complaints (or praise, of course!).
 * 
 * WARNING: Uses hardwired VT100 terminal codes. Thus, will only work on
 * terminal vaguely like VT100's (e.g. which is quite a lot: xterm,
 * sun-console, suntools-window, plessy, wyse).
 * 
 * POTENTIAL IMPROVEMENTS:
 * - remove use of global variable bottom_line/1.
 * - make terminal independent.
 * - make speed adjustable (so that if planning is very efficient, user
 *   can still follow display by artificially slowing down the
 *   computation with idle/wait an loop.
 *
 * Trivial changes by FvH:
 * - changed ttyflush calls to %f in writef.
 * - changed (slow) call to unix(shell(clear)) into writef('\e[H\e[2J%f').
 *   This is of course more terminal-dependent, but since the whole
 *   thing is terminal dependent anyway...
 * - added extra %f flush after writing depth-message.
 * - use print instead of write to print method, to enable pretty printing.
 * - redid some of the code-layout to fit CLaM conventions.
 * - change assert/retract on bottom_line/1 to record/erase. This is more
 *   ideologically correct (bottom_line/1 is data, not code), and allows
 *   garbage collection in NIP, and avoids problems with retractall
 *   across Prolog dialects (e.g. SWI).
 *
 */

viplan :- viplan(Plan), viplan := Plan.
viplan(Plan) :- genint(X), viplan(Plan, X).

viplan(Plan,Level) :-
    writef('\e[H\e[2J%f'), % Clear screen. 
    writef('Planning to depth of %d%f', [Level]),
    ((recorded(bottom_line,_,Ref),erase(Ref),fail) ; true),
    recorda(bottom_line,0,_), % YUCK (FvH)
    hyp_list(H),
    goal(G),
    viplan(H==>G,Plan,[],Level),
    recorded(bottom_line,D,_),
    D1 is D+1,
    locate(0, D1).

viplan(Input,Plan,Effects,MaxDepth) :-
    bound(Bound),
    MaxDepth=Bound,
    !,
    viplan(3,3,_,1,Bound,Input,Plan,Effects,MaxDepth).

viplan(X,Pos,NewPos,D,B,Input,Method,Effects,D) :-
    D=<B,
    applicable(Input,Method,_1,Effects),
    locate(X, Pos),
    print(Method),
    NewPos is Pos+1,
    writef('\e[J%f'). % Clear to end of display.

viplan(X,Pos,NewPos,Depth,Bound,Input,P1 then P2,Effects,MaxDepth) :-
    Depth<Bound,
    applicable(Input,P1,_1,[E|Es]),
    locate(X, Pos),
    print(P1),writef(' then\e[J%f'), % Clear to end of display.
    Pos1 is Pos+1,
    Depth1 is Depth+1,
    NewX is X+2,
    i_vp(NewX,Pos1,NewPos,Depth1,Bound,[E|Es],P2,Effects,MaxDepths),
    max(MaxDepths,MaxDepth).

viplan(X,Pos,_,_,_,_,_,_,_) :-
    locate(X, Pos),
    writef('\e[J%f'), % Clear to end of display.
    fail.

i_vp(NewX,Pos1,NewPos,Depth1,Bound,[E],P2,Effects,MaxDs) :-
    !,
    iterate_viplan(NewX,Pos1,NewPos,Depth1,Bound,[E],P2,Effects,MaxDs).
i_vp(X,PosIn,NewPosOut,Depth,Bound,Input,Method,Effects,MaxD) :-
    locate(X, PosIn),
    write('['),
    NewX is X+1,
    iterate_viplan(NewX,PosIn,PosOut,Depth,Bound,Input,Method,Effects,MaxD),
    locate(0, PosOut), writef('\e[K%f'),
    locate(X, PosOut),
    writef(']\e[J%f'), % Clear to end of display.
    NewPosOut is PosOut+1.

iterate_viplan(_,Pos,Pos,_,_,[],[],[],[]).
iterate_viplan(X,Pos,NewPos,D,B,[Input|Inputs],[Plan|Plans],Effects,[D1|Ds]) :-
    (Effects==[] -> Effect=[] ; true),
    viplan(X,Pos,NewPos1,D,B,Input,Plan,Effect,D1),
    (Effect==[] -> ! ; true),
    append(Effect,OtherEffects,Effects),
    iterate_viplan(X,NewPos1,NewPos,D,B,Inputs,Plans,OtherEffects,Ds).

locate(X, Y) :-
    X1 is X,
    Y1 is Y,
    writef('\e[%d;0H\e[%d;%dH%f', [Y1,Y1,X1]), % position cursor at line
					       % Y, column X.
    note_lowest(Y1).

note_lowest(Line) :-
    recorded(bottom_line,OldLine,_),
    Line =< OldLine, !.
note_lowest(Line) :-
    ((recorded(bottom_line,_,Ref),erase(Ref),fail) ; true),
    recorda(bottom_line,Line,_).

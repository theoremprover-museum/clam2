/*
 * @(#)$Id: hint_context.pl,v 1.4 1997/01/14 10:44:08 img Exp $
 *
 * $Log: hint_context.pl,v $
 * Revision 1.4  1997/01/14 10:44:08  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:17:27  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/03/01  04:14:08  img
 * 	* Added file_version/1 and associated multifile declaration
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: hint_context.pl,v 1.4 1997/01/14 10:44:08 img Exp $').

:- dynamic hint_context/4.

% hint_context for Hints.
%   
%     hint_context( Hint_method, Name, Pattern, [ <Parameters> ] ).




% This hint contexts is for the hint method gen_hint.

% This clause is for the theorem x+(x+x)=(x+x)+x in pnat.
% The parameters are the positions of the variables to be generalised. 


hint_context(gen_hint,
             plus_assoc,
	     _==>G,
             [
              [[1,1,1],
               [1,1,2,1]]
             ]
            ):- matrix(_,plus(X,plus(X,X))=plus(plus(X,X),X) in pnat,G).

% This clause is for the theorem halfpnat.
% The parameters are the positions of the variables to be generalised.

hint_context(gen_hint,
             halfpnat,
             _==>plus(X,s(X))=S in pnat,
             [
              [[1,1,1],
               [1,1,2,1]]
             ]
            ):-
             wave_fronts(s(plus(X,X)),_,S).

% This hint context is for the square root theorem: 
%
%    x:pnat=>:y:pnat#y*y=<x#x<s(y)*s(y)
%
% The parameter is the expression for the case split. The two cases will
%  be the expression and its negation.
% The hyp condition is used to detect an induction attempt and to
% recover the second expression of the # in the induction hypothesis.

hint_context(casesplit_hint,
             sqrcase,
             H==>_:pnat#C1#C2,
             [
               less(s(X),IndCaseExp)
             ]
             ):-
             wave_fronts(leq(_,s(X)),_,C1),
             wave_fronts(less(_,_),_,C2),
             hyp(_:leq(_,X)#less(X,IndCaseExp), H).

% This hint is for the base case of the sqare root theorem.
%

hint_context(existential_hint,
             sqrex1,
             _==> _:pnat#leq(_,0)#less(0,_),
             [0]).

% This two hints are for the step case of the square root theorem. 
% They are applied after the split case, thats why they look for the
% corresponding case in the hypothsis.

hint_context( existential_hint,
              sqrex2,
              H==>_:pnat#C1#C2,
              [Var]):-
               
               wave_fronts(leq(_,s(_)),_,C1),
               wave_fronts(less(_,_),_,C2),
               hyp(_:less(_,times(s(Var),s(Var))), H).
             
hint_context( existential_hint,
              sqrex3,
              H==>_:pnat#C1#C2,
              [s(Var)]):-

               wave_fronts(leq(_,s(_)),_,C1),
               wave_fronts(less(_,_),_,C2),
               hyp(_:less(_,times(s(Var),s(Var)))=>void, H).

%
% Consider_finished context for interactive use. It is used to stop
% planning at the present branch of the planning space and continue
% with other branches.


hint_context( consider_finished,
              interactive,
              _,
              []).

% -----------------------------------------------------------------sny.
% Context to generalise theorem rotlen into rotapp.
%

hint_context( gen_thm, 
              rot,  
              []==> l:(int list)=>rotate(length(l),l)=l in int list,
              [ rotlen ]).



% -----------------------------------------------------------------sny.
% Predicate to replace a list of positions for a term in an expression.
%

replace_list([],_,E,E).
replace_list([H|T],Term,Exp,NewExp):- 
                   replace(H,Term,Exp,IntExp),
                   replace_list(T,Term,IntExp,NewExp).



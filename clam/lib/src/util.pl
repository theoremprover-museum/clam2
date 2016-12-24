% $Id: util.pl,v 1.3 1995/04/02 20:14:02 armando Exp $
%
% $Log: util.pl,v $
% Revision 1.3  1995/04/02 20:14:02  armando
% indent0 defined
%
% Revision 1.2  1995/03/29  14:28:26  armando
% CVS Header added
%

make_obj(Term) :- Term=..[_,Name],
	          create_thm(Name,user),
	          select(Name),
		  apply(because),
		  lib_save(Term).

indent0 :- assert(appIndent(0)).

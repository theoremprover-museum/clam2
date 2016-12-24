/*
 * @(#)$Id: nested_ops.pl,v 1.4 1997/01/14 10:50:05 img Exp $
 *
 * $Log: nested_ops.pl,v $
 * Revision 1.4  1997/01/14 10:50:05  img
 * Generalized conditional for multifile declaration.
 *
 * Revision 1.3  1995/05/17 02:19:41  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.2  1995/04/25  10:07:30  img
 * 	* file_version/1 added
 *
 * Revision 1.1  1994/09/16  09:42:49  dream
 * Initial revision
 *
 */
?-if(multifile_needed). ?-multifile file_version/1. ?-endif.
file_version('$Id: nested_ops.pl,v 1.4 1997/01/14 10:50:05 img Exp $').

%***************
%*
%*   nested_ops  -   Operator declarations to allow recursive functions
%*               to be readily expressed in the usual nested conditional
%*               format
%*
%***************

:- op(950,fy,[if, wffwits ] ).

:- op(950,xfy,[else,boundin] ).
:- op(880,xfy,[and] ).



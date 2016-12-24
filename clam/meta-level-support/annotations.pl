/*
 * @(#)$Id: annotations.pl,v 1.2 1997/10/17 14:43:01 img Exp $
 *
 * $Log: annotations.pl,v $
 * Revision 1.2  1997/10/17 14:43:01  img
 * added header
 *
 *
 * revision 1.1 date: 1996/12/06 16:22:19;  author: img;  state: Exp;
 * "abstract data type" for annotated terms
 */

/* ABSTRACT TYPES FOR ANNOTATIONS */
/* This group is the only place in Clam that the specical functors for
   annotations are mentioned.  */
wave_front_functor('@wave_front@').
wave_hole_functor('@wave_var@').
wave_hole_coloured_functor('@wave_var_coloured@').
sink_functor('@sink@').

/* and some derived clauses for speed */
iswf('@wave_front@'(T,D,S),  T,D,S).
issink('@sink@'(X),X).
iswh('@wave_var@'(A),A).
iswh_colour('@wave_var_coloured@'(Colours,A),Colours,A).
/* END OF ABSTRACTION */

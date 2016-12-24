hyp2goal([],[]).
hyp2goal([G|Gs],[N|Ns]):- hyp2goal(G,N),
	                  hyp2goal(Gs,Ns).

hyp2goal(H==>G,Vs==>NG):- split_vars_and_prop(H,Vs,Ps),
	                  impi_props(Ps,G,NG).

split_vars_and_prop([],[],[]).
split_vars_and_prop([X:E|H],[X:E|Vs],Ps) :- type(E), !,
	split_vars_and_prop(H,Vs,Ps).
split_vars_and_prop([_:[ihmarker(_,_)|H1]|H],Vs,Ps) :- !,
	split_vars_and_prop(H,Vs,Ps1),
	append(H1,Ps1,Ps).
split_vars_and_prop([E|H],Vs,[E|Ps]) :- split_vars_and_prop(H,Vs,Ps).

impi_props([],G,G).
impi_props([_:P|Ps],G,P=>G1) :- impi_props(Ps,G,G1).

type(C):-member(C,[int, pnat, atom, _ list, _ tree]).

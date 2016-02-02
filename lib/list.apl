namespace List (

	pred append([A],[A],[A]).
	append([],L,L).
	append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).

	pred remove(A,[A],[A]).
	remove(X,[],[]).
	remove(X,[X|L],L')     :- remove(X,L,L').
	remove(X,[Y|L],[Y|L']) :- remove(X,L,L'),not(X=Y).

	pred mem(A,[A]).
	mem(X,[X|L]).
	mem(X,[Y|L]) :- mem(X,L).

	pred reverse([A],[A]).
	pred rev([A],[A],[A]).
	rev(L,[],L).
	rev(L,X::L',L''):- rev(X::L,L',L'').
	reverse(L,M)    :- rev([],L,M).

	pred concat([[A]],[A]).
	concat([],[]).
	concat([A|L],L') :- concat(L,L''), append(A,L'',L').


).

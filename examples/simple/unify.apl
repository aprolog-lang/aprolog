% #use "list.apl".
% #open List.

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



var  : name_type.
sym  : name_type.
term : type.

var : var -> term.
fun : (sym,[term]) -> term.

type prob = [(term,term)].
type subst = (var,term).

pred zip ([A], [B], [(A,B)]).
zip ([], [], []).
zip ([A|L],[B|M],[(A,B)|N]) :- zip (L,M,N).

pred unify (prob,[subst]).
unify([],[]).
unify([(fun(F,Ts),fun(F,Us))|P],S) :- zip(Ts,Us,TUs),
                                      append(TUs,P,P'),
                                      unify(P',S).
unify([(var V, var V)|P],S)        :- unify(P,S).
unify([(var V, T)| P], [(V,T)|S])  :- V # T, P' is P{T/var V}, unify(P',S).
unify([(T, var V)| P], [(V,T)|S])  :- V # T, P' is P{T/var V}, unify(P',S).

? unify([(fun(f,[var v]),var v)],S). 

? unify([(fun(f,[var v]),var w)],S).

? unify([(fun(f,[var v,fun (c,[])]), fun(f,[fun(d,[]),var v]))],S).

? unify([(fun(f,[var v,fun (c,[])]), fun(f,[fun(d,[]),var w]))],S).

? unify([(var w,fun (d,[]))],S).

? unify([(fun (c,[]),var v)],S).


%% From P. Taylor, practical for foundations  mathematics
type solution = [([var],term)].
type eqn = (term,term).




pred fetch(solution,var,([var],term),solution).
fetch((Vs,T)::R,X,(Vs,T),R) :- mem(X,Vs).
fetch((Vs,U)::R,X,B,(Vs,U)::R') :- X # Vs, fetch(R,X,B,R').

pred not_bound_in (var,solution).
not_bound_in(V,[]).
not_bound_in(V,[(Vs,_)|R]) :- V # Vs, not_bound_in (V,R).

pred unify' eqn solution solution.
pred unifys' ([term], [term]) solution solution.
pred merge_vars (var,var) solution solution.
pred merge_var_term (var,term) solution solution.

unify'(fun(F,Ts),fun(F,Us)) --> unifys' (Ts,Us).
unify'(var(X), var(Y)) --> merge_vars(X,Y).
unify'(var(X), T) -->  {X#T},merge_var_term(X,T).
unify'(T,var(X)) --> {X#T},merge_var_term(X,T).

unifys'([] ,[]) --> {true}.
unifys'([T|Ts] ,[U|Us]) --> unify' (T,U), unifys' (Ts,Us).

/* Transparent version */
/*merge_vars(X,X) --> {true}.
merge_vars(X,Y) R R :- fetch(R,X,(Vs,_),_), mem(Y,Vs).
merge_vars(X,Y) R R' :- fetch(R,X,(Vs,T),R1),
                        fetch(R1,Y,(Vs',T'),R2),
                        append(Vs,Vs',Vs''), 
                        R3 = (Vs'',T)::R2,
                        unify'(T,T') R3 R'.
merge_vars(X,Y) R ((Y::Vs,T)::R') 
 :- fetch(R,X,(Vs,T),R'),
    not_bound_in(Y,R). 
merge_vars(X,Y) R ((X::Vs,T)::R') 
 :- fetch(R,Y,(Vs,T),R'),
    not_bound_in(X,R).
merge_vars(X,Y) R (([X],var Y)::R) 
 :- not_bound_in(X,R),
    not_bound_in(Y,R). 

merge_var_term(X,T) R R' :- fetch(R,X,(Vs,T'),_),
                            unify' (T,T') R R'.
merge_var_term(X,T) R (([X],T)::R) :- not_bound_in(X,R).
*/


/*Transparent version+ cut */
/*merge_vars(X,X) --> {true}.
merge_vars(X,Y) R R :- fetch(R,X,(Vs,_),_), mem(Y,Vs),!.
merge_vars(X,Y) R R' :- fetch(R,X,(Vs,T),R1),
                        fetch(R1,Y,(Vs',T'),R2),!,
                        append(Vs,Vs',Vs''), 
                        R3 = (Vs'',T)::R2,
                        unify'(T,T') R3 R'.
merge_vars(X,Y) R ((Y::Vs,T)::R') 
 :- fetch(R,X,(Vs,T),R'),
    not_bound_in(Y,R),!. 
merge_vars(X,Y) R ((Y::Vs,T)::R') 
 :- fetch(R,Y,(Vs,T),R'),
    not_bound_in(X,R),!.
merge_vars(X,Y) R (([X],var Y)::R') 
 :- not_bound_in(X,R),
    not_bound_in(Y,R),!. 

merge_var_term(X,T) R R' :- fetch(R,X,(Vs,T'),_),!,
                            unify' (T,T') R R'.
merge_var_term(X,T) R (([X],T)::R) :- not_bound_in(X,R),!.
*/



/* Using if-then-else */
merge_vars(X,Y) R R' :- 
  ( X = Y -> R = R' | 
    ( fetch(R,X,(Vs,T),R1) -> 
      ( mem(Y,Vs) -> R = R' 
      | ( fetch(R1,Y,(Vs',T'),R2) -> 
            append(Vs,Vs',Vs''), 
            R3 = (Vs'',T)::R2,
            unify'(T,T') R3 R' 
        | R' = (Y::Vs,T)::R1
        )
      )
    | fetch(R,Y,(Vs,T),R1) -> 
      ( R' = (X::Vs,T)::R1 )
    | R' = (([X],var Y)::R)
    )
  ).


merge_var_term(X,T) R R' :- 
  ( fetch(R,X,(Vs,T'),_) -> 
      unify' (T,T') R R'
    | R' = ([X],T)::R).  



/*
? unify'(fun(f,[fun(f,[var v])]),var v) [] R.

? unify'(fun(f,[var w]),var v) [] R, unify'(fun(f,[var v]),var w) R R'.


? unify'(fun(f,[var v]),var w) [] R.

? unify'(fun(f,[var v,fun (c,[])]), fun(f,[fun(d,[]),var v])) [] R.

? unify'(fun(f,[var v,fun (c,[])]), fun(f,[fun(d,[]),var w])) [] R.

? unify'(var w,fun (d,[])) [] R.

? unify'(fun (c,[]),var v) [] R.

? unify'(var x1, fun(f,[var x2,var x2])) [] R1, 
unify'(var x2, fun(f,[var x3,var x3])) R1 R2, 
unify'(var x3, fun(f,[var x4,var x4])) R2 R3, 
unify'(var x4, fun(f,[var x5,var x5])) R3 R4. 

? unify'(var x4, fun(f,[var x5,var x5])) [] R1,
unify'(var x3, fun(f,[var x4,var x4])) R1 R2, 
unify'(var x2, fun(f,[var x3,var x3])) R2 R3, 
unify'(var x1, fun(f,[var x2,var x2])) R3 R4
. 

func big(int,var,sym) = ([term],[term]).
big(N,V,F) = ([],[]) :- N <= 0.
big(N,V,F) = ((var V)::L1,(fun (F,[var w,var w]))::L2)
  :- M is N - 1, 
     (L1,L2) = big(M,w,F).

?(L1,L2) = big(60,x,f), append(L1,L1,L1'), append(L2,L2,L2'),!, 
unifys'(L1',L2') [] R.
*/

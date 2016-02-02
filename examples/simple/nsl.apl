#use "list.apl".
#open List.

a	: name_type.
k	: type.
n	: name_type.
m	: type.

pub	: a -> k.
pri	: a -> k.
shared	: n -> k.

nm	: a -> m.
enc	: (k,m) -> m.
nonce	: n -> m.
pair	: (m,m) -> m.

pred send m [m] [m].
send M L [M|L].

pred recv m [m] [m].
recv M L L :- mem(M, L).

pred fresh n [m] [m].
fresh n L L :- n # L. (* needs atom search/equivariance *)

pred	dec	(m, k, m).
dec (enc(pub A,M),pri A,M).

(* freshness? need m fresh for "world" *)
pred	nsStep1	 a a [m] [m].
nsStep1 A B --> fresh M, 
	        send (enc (pub B,pair (nonce M,nm A))).

pred	nsStep2	 a a [m] [m].
nsStep2 B A --> recv Msg, 
	        {dec (Msg,pri B,pair (nonce M,nm A))},
		fresh N,
	        send (enc (pub A,pair (nonce M,nonce  N))).


pred	nsStep3	 a a [m] [m].
nsStep3 A B --> recv Msg, 
	        {dec (Msg,pri A,pair (nonce M,nonce N))},
		send (enc (pub B,nonce N)).

pred	nsTypical [m] [m].
nsTypical --> nsStep1  alice bob,
	      nsStep2  bob alice,
	      nsStep3  alice bob.

pred	nsAttack [m] [m].
nsAttack -->   nsStep1  alice eve,
	       recv M1,
               {dec (M1,pri eve, M1')},
               send (enc (pub bob,M1')),
	       nsStep2  bob alice,
               nsStep3  alice eve,
	       recv M3,
	       {dec (M3,pri eve,M3')},
	       send (enc (pub bob, M3')).

pred	nslStep1	 a a [m] [m].
nslStep1 A B --> fresh M,
		 send (enc (pub B,pair (nonce M,nm A))).

pred	nslStep2	 a a [m] [m].
nslStep2 B A --> recv Msg,
		 {dec (Msg,pri B,pair (nonce M,nm A))},
		 fresh N,
	         send (enc (pub A,pair(pair (nonce M,nonce N),nm B))).

pred	nslStep3	 a a [m] [m].
nslStep3 A B --> recv Msg,
	         {dec (Msg,pri A,pair(pair (nonce M,nonce N),nm B))},
		 send (enc (pub B,nonce N)).


pred	nslTypical [m] [m].
nslTypical --> nslStep1 alice bob,
	       nslStep2 bob alice,
	       nslStep3 alice bob.
 
pred	nslAttack [m] [m].
nslAttack -->  nslStep1 alice eve,
	       recv M1,
               {dec (M1,pri eve, M1')},
               send (enc (pub bob,M1')),
	       nslStep2 bob alice,
               nslStep3 alice eve,
	       recv M3,
	       {dec (M3,pri eve,M3')},
	       send (enc (pub bob, M3')).

?nsTypical [] L.
?nsAttack [] L.
?nslTypical [] L.
?nslAttack [] L.
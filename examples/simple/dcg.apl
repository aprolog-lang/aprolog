exp	: type.
id	: name_type.

var : id -> exp.
app : exp -> exp -> exp.
lam : id\exp -> exp.




pred token	A [A] [A].
token C (C::X) X.




pred exp 	exp [char] [char].
pred id 	id  [char] [char].
pred ws_opt 	    [char] [char].
pred ws 	    [char] [char].

id A --> token C, {A is Name.from_string([C])}.

ws --> ' ', ws_opt
    ;  '\t',ws_opt
    ;  '\n',ws_opt.
ws_opt --> {true}
        ;   ws.

exp (app E1 E2) --> '(',ws_opt,exp E1,ws, exp E2, ws_opt,')'.
exp (var V) --> id (V).
exp (lam F) --> 
	"fn",ws,
	id (V),	ws_opt,
	'.', ws_opt,
	exp E,
	{F is mk_abs V E}.

pred parse_exp 	string exp.

parse_exp X E :- exp E X [].


pred string(string) string string.
string([]) L L.
string(C::S) (C::L) M :- string(S) L M.

pred print_exp exp string string.
print_exp (var V) -->  {S is Name.to_string(V)},string(S).
print_exp (app E1 E2) --> "(", print_exp E1, " ", print_exp E2, ")".
print_exp (lam (F)) -->  {(A,X) is split_abs(F)}, "fn ", print_exp (var A), ".", print_exp (X).

?parse_exp "fn x.fn y.(x y)" E,print_exp(E) S [].

?parse_exp "fn y.(x y)" E, F is E{y/x}, print_exp(E) S [].

?parse_exp "fn x. fn x.(x x)" E,print_exp(E) S [].

pred beta(exp,exp).
beta(app (lam(x\F)) N, G) :- G is F{N/var x}.

?
parse_exp "fn x.fn y.(x y)" E1,
parse_exp "fn y.(x y)" E2,
parse_exp "fn x.(x x)" E3,
X = app E3 E3,
beta(X,Y),
print_exp(Y) S [].

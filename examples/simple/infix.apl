i : type.
o : type.
zero : i.
++ : i -> i -> i.
** : i -> i -> i.
== : i -> i -> o.

pred t o.
infixl == 4.
infixl ++ 5.
infixl ** 6.

func (***) (int,int) = int.
(***) (X, 0) = 1.
(***) (X,1) = X.

infixr *** 7.


forall X. t(zero == X ** zero).

t(X ** (Y ++ Z) == X ** Y ++ X ** Z).

t( (**) X Y == (++) Y Z).

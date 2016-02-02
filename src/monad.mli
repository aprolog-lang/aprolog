type ('a,'b,'c) scmonad ;;
type ('a,'b) scmonoid = ('a,'b,unit) scmonad;;
type ('b) smonoid = (unit,'b,unit) scmonad;;
type ('b,'c) smonad = (unit,'b,'c) scmonad;;

val (>>=)  : ('a,'b,'c) scmonad ->
             ('c -> ('a,'b,'d) scmonad) -> 
             ('a,'b,'d) scmonad;;
val (>>)   : ('a,'b,'d) scmonad -> ('a,'b,'c) scmonad -> ('a,'b,'c) scmonad;;
val return : 'c -> ('a,'b,'c) scmonad;;
val skip   : ('a,'b) scmonoid;;
val run    : 'a -> 'b -> ('a,'b,'c) scmonad -> 'b * 'c;;

val using : ('a -> ('a,'b,'c) scmonad) -> ('a,'b,'c) scmonad;;
val lift  : ('b -> 'b) -> ('a,'b) scmonoid;;
val get_state : ('a,'b,'b) scmonad;;

type ('b,'c) field = ('b -> 'c) *  ('b -> 'c -> 'b);;

val get    : ('b,'c) field -> ('a,'b,'c) scmonad;;
val set    : ('b,'c) field -> 'c -> ('a,'b,unit) scmonad;;
val update : ('b,'c) field -> ('c -> 'c) -> ('a,'b,unit) scmonad;;

val iter      : ('a -> ('b,'c) scmonoid) -> 'a list -> ('b,'c,unit) scmonad;;
val map       : ('a -> ('b,'c,'d) scmonad) -> 'a list -> 
                ('b,'c,'d list) scmonad;;
val fold_left : ('a -> 'b -> ('c,'d,'a) scmonad) -> 
                  'a -> 'b list -> ('c,'d,'a) scmonad;;
val fold_left2 : ('a -> 'b -> 'c -> ('d,'e,'a) scmonad) -> 
                  'a -> 'b list -> 'c list -> ('d,'e,'a) scmonad;;

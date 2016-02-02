
type ('a,'b,'c) scmonad = 'a -> 'b -> ('b*'c);;


type ('a,'b) scmonoid = ('a,'b,unit) scmonad;;


type ('b) smonoid = (unit,'b,unit) scmonad;;


type ('b,'c) smonad = (unit,'b,'c) scmonad;;


type ('a,'b) field = ('a -> 'b) *  ('a -> 'b -> 'a);;


let return c = (fun a b -> (b,c));;


let run a b m = m a b;;


let (>>=) m f = 
  (fun a b -> 
    let (b,c) = m a b in
    let (b,d) = f c a b in
    (b,d))
;;


let (>>) m n = m >>= (fun _ -> n);;


let skip = (fun a b -> (b,()));;


let using f = (fun a -> f a a);;


let lift f = (fun c s -> (f s,()));;


let get_state = (fun a b -> (b,b));;


let get (g,s) = (fun a b -> (b,g b));;


let set (g,s) c = (fun a b -> (s b c,()));;


let update f g = 
  get f >>= fun x -> 
  set f (g x)
;;


let rec iter m l = 
  match l with
    [] -> skip
  | x::xs -> m x >> iter m xs
;;


let rec map m l = 
  match l with
    [] -> return []
  | x::xs -> 
      m x >>= fun y -> 
      map m xs >>= fun ys -> 
      return (y::ys)
;;


let rec fold_left f a l = 
  match l with
    [] -> return a
  | (x::xs) -> 
      f a x >>= (fun x -> 
      fold_left f x xs)
;;


let rec fold_left2 f a l1 l2 = 
  match l1,l2 with
    [],[] -> return a
  | (x::xs,y::ys) -> 
      f a x y >>= (fun x -> 
      fold_left2 f x xs ys)
  | _,_ -> Util.impos "fold_left2: lists of different length"

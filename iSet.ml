(* Zadanie : Modyfikacja drzew  *)
(* Autor : Marcin Michorzewski  *)
(* Code review: Magda Grabowska *)

(* t - (l, k, r, h, n), gdzie h - wys,*)
(* n - liczba elementów w drzewie,    *)
(* k - przedział w korzeniu drzewa    *)
type t = 
  | Empty
  | Node of t * (int * int) * t * int * int

let empty = Empty

(* Suma i różnica liczb *)

(* Przyjmujemy, że x, y należy do [min_int, max_int] *)
(* sum x y = x + y, chyba, że zbyt duże, lub zbyt    *)
(* małe, wtedy min_int lub max_int odpowiednio,      *)
(* diff x y = x - y analogicznie                     *)
let sum x y =
  if x <= 0 then
    if min_int - x > y then min_int
    else x + y
  else
    if max_int - x < y then max_int
    else x + y

let diff x y =
  if y <= 0 then
    if max_int + y < x then max_int
    else x - y
  else
    if min_int + y > x then min_int    
    else x - y

(* część wspólna przedziałów *)
let common_part (a, b) (c, d) =
  if ((c >= a && c <= sum b 1) ||
      (d >= diff a 1 && d <= b) ||
      (d > b && c < a)        )
      then true
  else false

let is_empty = function
  | Empty -> true
  | _ -> false

let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0

let size = function
  | Node (_, _, _, _, s) -> s
  | Empty -> 0

let i_size (a, b) =
  sum (diff b a) 1

let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec max_elt = function
  | Node (_, k, Empty, _, _) -> k
  | Node (_, k, r, _, _) -> max_elt r
  | Empty -> raise Not_found

(* suma elementów drzew l, r oraz liczby x *)
let size_sum l r = function x ->
  let temp_sum = sum (size l) (size r) in
     sum temp_sum x

let make l k r =
  Node (l, k, r, max (height l) (height r) + 1, size_sum l r (i_size k))

(* l i r są zbalansowane a ich wysokości   *)
(* różnią się co najwyżej o 3              *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r

let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "ISet.remove_min_elt"

let rec remove_max_elt = function
  | Node (l, _, Empty, _, _) -> l
  | Node (l, k, r, _, _) -> bal l k (remove_max_elt r)
  | Empty -> invalid_arg "ISet.remove_max_elt"

(* t1, t2 - zbalansowane, podobnej wysokości        *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* t - drzewo nie zawiera żadnego przedziału, który *)
(* możnaby dokleić do (a, b), dodaje (a, b) do t    *)
let rec add_reduced (a, b) t =
  match t with
  | Empty -> Node (Empty, (a, b), Empty, 1, i_size (a, b))
  | Node (l, (p1, p2), r, h, _) ->
      if p1 > sum b 1 then
	bal (add_reduced (a, b) l) (p1, p2) r
      else if p2 < diff a 1 then
	bal l (p1, p2) (add_reduced (a, b) r)
      else invalid_arg "ISet.add_reduced"

(* join l v r - l, r - zbalansowane drzewa dowolnej *)
(* wysokości niełączliwe z v (tzn. nie istnieje     *)
(* wierzchołek który można powiększyć o v)          *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_reduced v r
  | (_, Empty) -> add_reduced v l
  | (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
      if lh > rh + 2 then bal ll lv (join lr v r) else
      if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

let split a t =
  let rec loop = function
    | Empty -> (Empty, false, Empty)
    | Node (l, (p1, p2), r, _, _) ->
	if p1 <= a && p2 >= a then
	  let l1 =
	    if a > p1 then add_reduced (p1, diff a 1) l
	    else l
	  and r1 =
	    if a < p2 then add_reduced (sum a 1, p2) r
	    else r
	  in
	    (l1, true, r1)
        else if a < p1 then
	  let (ll, pres, rl) = loop l in 
	    (ll, pres, join rl (p1, p2) r)
	else
	  let (lr, pres, rr) = loop r in 
	    (join l (p1, p2) lr, pres, rr)
  in
    loop t

(* add dzieli t na l i r, których elementy są       *)
(* mniejsze od a (drzewo l) oraz większe od b (r)   *)
(* następnie wyciąga wierzchołki, które możnadokleić*)
(* do (a, b)i tak nowe drzewa l', r' łączy z (a',b')*)
let add (a, b) t =
  let (tl, _, _) = split a t 
  and (_, _, tr) = split b t in
    match (tl, tr) with
    | (Empty, Empty) -> add_reduced (a, b) empty
    | _ -> 
	let (tl_red, tl_max) =
	  if is_empty tl then (tl, a)
	  else
	    let (p1, p2) = max_elt tl in
	      if p2 + 1 >= a then (remove_max_elt tl, p1)
	      else (tl, a)
	and (tr_red, tr_min) =
	  if is_empty tr then (tr, b)
	  else
	    let (p1, p2) = min_elt tr in
	      if p1 - 1 <= b then (remove_min_elt tr, p2)
	      else (tr, b)
	in
	  join tl_red (tl_max, tr_min) tr_red


(* usuwa z drzewa przedział (a, b), przy założeniu, *)
(* że istnieje 1 wierzchołek, który ten przedział   *)
(* zawiera                                          *)
let rec remove_reduced (a, b) = function
  | Node (l, (p1, p2), r, _, _) ->
      if (p1 <= a && p2 >= b) then
	let l1 =
	  if p1 < a then add (p1, diff a 1) l
	  else l
	and r1 =
	  if p2 > b then add (sum b 1, p2) r
	  else r
	in 
	  merge l1 r1
      else if (p2 < a) then bal l (p1, p2) (remove_reduced (a, b) r)
      else bal (remove_reduced (a, b) l) (p1, p2) r
  | Empty -> invalid_arg "ISet.remove_reduced"


(* dodaje przedział, a następnie go odejmuje        *)
let remove x t =
  let t1 = add x t in
    remove_reduced x t1

let mem x t =
  let rec loop = function
    | Empty -> false
    | Node (l, (a, b), r, _, _) ->
	if (a <= x && x <= b) then true else
        if x < a then loop l
	else loop r in
  loop t

let iter f t =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r in
  loop t

let fold f t acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
          loop (f k (loop acc l)) r in
  loop acc t

let elements t = 
  let rec loop acc = function
    | Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
  loop [] t

let below x t =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, (p1, p2), r, _, _) ->
	if (p1 <= x && x <= p2) then 
	  sum acc (sum (size l) (i_size (p1, x)))
	else if x < p1 then 
	  loop acc l
        else 
	  loop (sum acc (sum (size l) (i_size (p1, p2)))) r
  in
    loop 0 t

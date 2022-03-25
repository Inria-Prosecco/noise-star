module Spec.Noise.Map

include FStar.List.Tot

/// A high level map which uses a predicate function for lookups and filtering.

#push-options "--z3rlimit 25 --fuel 0 --ifuel 1"

(** Some utilities *)
// TODO: move to F*
[@(strict_on_arguments [3])]
val gmap : #a:Type -> #b:Type -> f:(a -> GTot b) -> list a -> GTot (list b)
let rec gmap #a #b f ls =
  match ls with
  | [] -> []
  | x :: ls' -> f x :: gmap f ls'

[@(strict_on_arguments [1])]
val pairwise_distinct : #a:eqtype -> ls:list a -> Tot bool
let rec pairwise_distinct (#a : eqtype) (ls : list a) : Tot bool =
  match ls with
  | [] -> true
  | x :: ls' -> List.Tot.for_all (fun y -> x <> y) ls' && pairwise_distinct ls'

[@(strict_on_arguments [2])]
val pairwise_rel : #a:Type -> pred:(a -> a -> Tot bool) -> ls:list a -> Tot bool
let rec pairwise_rel #a pred ls =
  match ls with
  | [] -> true
  | x :: ls' ->
    List.Tot.for_all (pred x) ls' && pairwise_rel pred ls' 

[@(strict_on_arguments [2])]
val gfor_all: #a:Type -> f:(a -> GTot bool) -> list a -> GTot bool
let rec gfor_all (f : 'a -> GTot bool) (l : list 'a) : GTot bool =
  match l with
  | [] -> true
  | hd::tl -> if f hd then gfor_all f tl else false

[@(strict_on_arguments [2])]
val gfilter : #a: Type -> f:(a -> GTot bool) -> l: list a -> GTot (m:list a{forall x. memP x m ==> f x})
#push-options "--fuel 1 --ifuel 1"
let rec gfilter #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::gfilter f tl else gfilter f tl
#pop-options

/// Filter at most one element
[@(strict_on_arguments [2])]
val filter_one : #a: Type -> f:(a -> Tot bool) -> l: list a -> Tot (list a)
#push-options "--fuel 1 --ifuel 1"
let rec filter_one #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter_one f tl else tl
#pop-options

/// Filter at most one element
[@(strict_on_arguments [2])]
val gfilter_one : #a: Type -> f:(a -> GTot bool) -> l: list a -> GTot (list a)
#push-options "--fuel 1 --ifuel 1"
let rec gfilter_one #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::gfilter_one f tl else tl
#pop-options

/// "p" stands for "prop"

[@(strict_on_arguments [2])]
val for_allP: #a:Type -> f:(a -> Tot Type0) -> list a -> Tot Type0
let rec for_allP (f : 'a -> Tot Type0) (l : list 'a) : Tot Type0 =
  match l with
  | [] -> True
  | hd::tl -> f hd /\ for_allP f tl

[@(strict_on_arguments [2])]
val gfor_allP: #a:Type -> f:(a -> GTot Type0) -> list a -> GTot Type0
let rec gfor_allP (f : 'a -> GTot Type0) (l : list 'a) : GTot Type0 =
  match l with
  | [] -> True
  | hd::tl -> f hd /\ gfor_allP f tl

val gfor_allP_and:
     #a:Type
  -> f:(a -> GTot Type0)
  -> g:(a -> GTot Type0)
  // Because of the SMT encoding, it is better to provide h such that h == f /\ g,
  // otherwise some assertions expected by the user might not get proven
  -> h:(x:a -> GTot (y:Type0{(f x /\ g x) ==> y}))
  -> ls:list a ->
  Lemma (requires (gfor_allP f ls /\ gfor_allP g ls))
  (ensures (gfor_allP h ls))

#push-options "--fuel 1 --ifuel 1"
let rec gfor_allP_and #a f g h ls =
  match ls with
  | [] -> ()
  | hd::tl -> gfor_allP_and f g h tl
#pop-options

[@(strict_on_arguments [2])]
val gexistsP: #a:Type -> f:(a -> GTot Type0) -> list a -> GTot Type0
#push-options "--ifuel 1"
let rec gexistsP #a f l = match l with
 | [] -> False
 | hd::tl -> f hd \/ gexistsP f tl
#pop-options

[@(strict_on_arguments [2])]
val pairwise_grel : #a:Type -> pred:(a -> a -> GTot bool) -> ls:list a -> GTot bool
let rec pairwise_grel (#a : Type) (pred : a -> a -> GTot bool) (ls : list a) : GTot bool =
  match ls with
  | [] -> true
  | x :: ls' ->
    gfor_all (pred x) ls' && pairwise_grel pred ls' 

[@(strict_on_arguments [2])]
val pairwise_grelP : #a:Type -> pred:(a -> a -> GTot Type0) -> ls:list a -> GTot Type0
let rec pairwise_grelP (#a : Type) (pred : a -> a -> GTot Type0) (ls : list a) : GTot Type0 =
  match ls with
  | [] -> true
  | x :: ls' ->
    gfor_allP (pred x) ls' /\ pairwise_grelP pred ls' 

val gfold_left: ('a -> 'b -> GTot 'a) -> 'a -> l:list 'b -> GTot 'a (decreases l)
let rec gfold_left f x l = match l with
  | [] -> x
  | hd::tl -> gfold_left f (f x hd) tl

val gfold_right: ('a -> 'b -> GTot 'b) -> list 'a -> 'b -> GTot 'b
let rec gfold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (gfold_right f tl x)

[@(strict_on_arguments [2])]
val memP_gfilter :
     #a: Type
  -> f: (a -> GTot bool)
  -> x: a
  -> l: list a ->
  Lemma (requires (memP x l /\ f x))
  (ensures (memP x (gfilter f l)))
#push-options "--fuel 1 --ifuel 1"
let rec memP_gfilter #a f x l =
  match l with
  | [] -> ()
  | hd::tl ->
    if FStar.IndefiniteDescription.strong_excluded_middle (x == hd) then ()
    else memP_gfilter f x tl
#pop-options

val list_in_listP (#a:Type) (ls0 ls1 : list a) : Type0
let list_in_listP #dt ls0 ls1 =
  for_allP (fun x -> memP x ls1) ls0

val list_in_listP_append (#a:Type) (ls0 ls1 : list a) (x : a) :
  Lemma
  (requires (list_in_listP ls0 ls1))
  (ensures (list_in_listP ls0 (x::ls1)))
  (decreases ls0)

#push-options "--fuel 1 --ifuel 1"
let rec list_in_listP_append #dt ls0 ls1 x =
  match ls0 with
  | [] -> ()
  | x0 :: ls0' ->
    list_in_listP_append ls0' ls1 x
#pop-options

val list_in_listP_refl (#a: Type) (ls: list a) :
  Lemma (list_in_listP ls ls)
#push-options "--fuel 1 --ifuel 1"
let rec list_in_listP_refl #dt ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    list_in_listP_refl ls';
    list_in_listP_append ls' ls' x
#pop-options

val memP_list_in_listP_implies_memP (#a : Type) (x : a) (ls0 ls1 : list a) :
  Lemma
  (requires (
    memP x ls0 /\
    list_in_listP ls0 ls1))
  (ensures (memP x ls1))

#push-options "--fuel 1 --ifuel 1"
let rec memP_list_in_listP_implies_memP #a x ls0 ls1 =
  match ls0 with
  | [] -> ()
  | x' :: ls0' ->
    if FStar.IndefiniteDescription.strong_excluded_middle (x == x') then ()
    else memP_list_in_listP_implies_memP x ls0' ls1
#pop-options

val list_in_listP_trans (#a:Type) (ls0 ls1 ls2 : list a) :
  Lemma
  (requires (
    list_in_listP ls0 ls1 /\
    list_in_listP ls1 ls2))
  (ensures (list_in_listP ls0 ls2))

#push-options "--fuel 1 --ifuel 1"
let rec list_in_listP_trans #dt ls0 ls1 ls2 =
  match ls0 with
  | [] -> ()
  | x0 :: ls0' ->
    list_in_listP_trans ls0' ls1 ls2;
    memP_list_in_listP_implies_memP x0 ls1 ls2
#pop-options

val memP_gfor_allP:
     #a:Type
  -> f:(a -> GTot Type0)
  // Because of the SMT encoding, it is better to provide h such that h == f /\ g,
  // otherwise some assertions expected by the user might not get proven
  -> x:a
  -> ls:list a ->
  Lemma (requires (gfor_allP f ls /\ memP x ls))
  (ensures (f x))

#push-options "--fuel 1 --ifuel 1"
let rec memP_gfor_allP #a f x ls =
  match ls with
  | [] -> ()
  | hd::tl ->
    if FStar.IndefiniteDescription.strong_excluded_middle (x == hd) then ()
    else memP_gfor_allP f x tl
#pop-options

val gfor_allP_list_in_listP_and:
     #a:Type
  -> f:(a -> GTot Type0)
  -> g:(a -> GTot Type0)
  // Because of the SMT encoding, it is better to provide h such that h == f /\ g,
  // otherwise some assertions expected by the user might not get proven.
  // Also note that we put the condition between f, g and h as an additional
  // parameter and not as a refinement: otherwise it creates problems, again, with the
  // encoding.
  -> h:(x:a -> GTot Type0)
  -> h_lem:(x:a -> Lemma ((f x /\ g x) ==> h x))
  -> ls0:list a
  -> ls1:list a ->
  Lemma (requires (
    gfor_allP f ls0 /\
    gfor_allP g ls1 /\
    list_in_listP ls0 ls1))
  (ensures (gfor_allP h ls0))

#push-options "--fuel 1 --ifuel 1"
let rec gfor_allP_list_in_listP_and #a f g h h_lem ls0 ls1 =
  match ls0 with
  | [] -> ()
  | hd::tl ->
    h_lem hd;
    memP_gfor_allP g hd ls1;
    gfor_allP_list_in_listP_and f g h h_lem tl ls1
#pop-options

val gfor_allP_list_in_listP:
     #a:Type
  -> f:(a -> GTot Type0)
  -> ls0:list a
  -> ls1:list a ->
  Lemma (requires (
    gfor_allP f ls1 /\
    list_in_listP ls0 ls1))
  (ensures (gfor_allP f ls0))

#push-options "--fuel 1 --ifuel 1"
let rec gfor_allP_list_in_listP #a f ls0 ls1 =
  match ls0 with
  | [] -> ()
  | hd::tl ->
    memP_gfor_allP f hd ls1;
    gfor_allP_list_in_listP f tl ls1
#pop-options


(** The map *)
val t : a:Type u#a -> Type u#a
let t a = list a

val add : #a:Type -> x:a -> m:t a -> t a
let add #a x m = x :: m

val lookup : #a:Type -> (f:a -> Tot bool) -> m:t a -> option a
let lookup #a f m = tryFind f m

val remove_first : #a:Type -> (f:a -> Tot bool) -> m:t a -> t a
let rec remove_first #a f m =
  match m with
  | [] -> []
  | x :: m' -> if f x then m' else x :: remove_first f m'

val lookup_pred_eq_lem (#a:Type) (f1 f2 : a -> Tot bool) (m:t a) :
  Lemma
  (requires (forall x. f1 x == f2 x))
  (ensures (lookup f1 m == lookup f2 m))
  (decreases m)

#push-options "--fuel 1"
let rec lookup_pred_eq_lem #a f1 f2 m =
  match m with
  | [] -> ()
  | x :: m' -> lookup_pred_eq_lem f1 f2 m'
#pop-options

// TODO: move those lemmas to F* library
val tryFind_lem (#a : Type) (f : a -> Tot bool) (ls : list a) :
  Lemma
  (requires True)
  (ensures (
    match List.Tot.tryFind f ls with
    | None -> True
    | Some x -> f x))
  (decreases ls)

#push-options "--fuel 1"
let rec tryFind_lem #a f ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    tryFind_lem f ls'
#pop-options

/// In the below lemma, we use two predicate functions pred1 and pred2 because
/// the SMT encoding is unprecise: if we only have one and use its negation in the
/// postcondition, the user may not be able to use the lemma.
val tryFind_not_is_for_all_lem :
     #a:Type0
  -> pred1:(a -> Tot bool)
  -> pred2:(a -> a -> Tot bool)
  -> x:a
  -> ls:list a ->
  Lemma
  (requires (
    forall y. pred1 y <> pred2 x y))
  (ensures (
    match List.Tot.tryFind pred1 ls with
    | None -> List.Tot.for_all (pred2 x) ls
    | Some _ -> not (List.Tot.for_all (pred2 x) ls)))
  (decreases ls)

#push-options "--fuel 1"
let rec tryFind_not_is_for_all_lem #a pred1 pred2 x ls =
  match ls with
  | [] -> ()
  | y :: ls' ->
    tryFind_not_is_for_all_lem pred1 pred2 x ls'
#pop-options

val forall_implies_list_for_all (#a : Type) (pred : a -> Tot bool)
                                (ls : list a) :
  Lemma
  (requires (forall x. pred x))
  (ensures (
    List.Tot.for_all pred ls))
  (decreases ls)

#push-options "--fuel 1"
let rec forall_implies_list_for_all pred ls =
  match ls with
  | [] -> ()
  | x :: ls' -> forall_implies_list_for_all pred ls'
#pop-options

val filter_preserves_for_all :
     #a:Type
  -> forall_pred:(a -> Tot bool)
  -> filter_pred:(a -> Tot bool)
  -> ls:list a ->
  Lemma
  (requires (List.Tot.for_all forall_pred ls))
  (ensures (
    List.Tot.for_all forall_pred (List.Tot.filter filter_pred ls)))
  (decreases ls)

#push-options "--fuel 1 --ifuel 1"
let rec filter_preserves_for_all #a forall_pred filter_pred ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    filter_preserves_for_all #a forall_pred filter_pred ls'
#pop-options

val filter_preserves_pairwise_rel :
     #a:Type
  -> pairwise_pred:(a -> a -> Tot bool)
  -> filter_pred:(a -> Tot bool)
  -> ls:list a ->
  Lemma
  (requires (pairwise_rel pairwise_pred ls))
  (ensures (
    pairwise_rel pairwise_pred (List.Tot.filter filter_pred ls)))
  (decreases ls)

#push-options "--fuel 1"
let rec filter_preserves_pairwise_rel #a pairwise_pred filter_pred ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    filter_preserves_for_all #a (pairwise_pred x) filter_pred ls';
    filter_preserves_pairwise_rel #a pairwise_pred filter_pred ls'
#pop-options

/// Filter one
val filter_one_unchanged_lem :
  #a: Type -> f:(a -> Tot bool) -> l: list a ->
  Lemma
  (requires (for_all f l))
  (ensures (filter_one f l == l))
#push-options "--fuel 1 --ifuel 1"
let rec filter_one_unchanged_lem #a f = function
  | [] -> ()
  | hd::tl -> filter_one_unchanged_lem f tl
#pop-options

val filter_one_preserves_for_all :
     #a:Type
  -> forall_pred:(a -> Tot bool)
  -> filter_pred:(a -> Tot bool)
  -> ls:list a ->
  Lemma
  (requires (List.Tot.for_all forall_pred ls))
  (ensures (
    List.Tot.for_all forall_pred (filter_one filter_pred ls)))
  (decreases ls)

#push-options "--fuel 1 --ifuel 1"
let rec filter_one_preserves_for_all #a forall_pred filter_pred ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    filter_one_preserves_for_all #a forall_pred filter_pred ls'
#pop-options

val filter_one_preserves_pairwise_rel :
     #a:Type
  -> pairwise_pred:(a -> a -> Tot bool)
  -> filter_pred:(a -> Tot bool)
  -> ls:list a ->
  Lemma
  (requires (pairwise_rel pairwise_pred ls))
  (ensures (
    pairwise_rel pairwise_pred (filter_one filter_pred ls)))
  (decreases ls)

#push-options "--fuel 1"
let rec filter_one_preserves_pairwise_rel #a pairwise_pred filter_pred ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    filter_one_preserves_for_all #a (pairwise_pred x) filter_pred ls';
    filter_one_preserves_pairwise_rel #a pairwise_pred filter_pred ls'
#pop-options

val splitAt_eq_lem (#a:Type) (n:nat) (l:list a) :
  Lemma
  (requires (n <= List.Tot.length l))
  (ensures (
    let l1, l2 = List.Tot.splitAt n l in
    List.Tot.length l1 = n /\
    List.Tot.length l2 = List.Tot.length l - n /\
    l == List.Tot.append l1 l2))
  (decreases l)

#push-options "--fuel 1 --ifuel 1"
let rec splitAt_eq_lem n l =
  match l with
  | [] -> ()
  | x :: l' ->
    if n = 0 then ()
    else splitAt_eq_lem (n-1) l'
#pop-options

[@(strict_on_arguments [2])]
val memP_gfilter_one :
     #a: Type
  -> f: (a -> GTot bool)
  -> x: a
  -> l: list a ->
  Lemma (requires (memP x l /\ f x))
  (ensures (memP x (gfilter_one f l)))
#push-options "--fuel 1 --ifuel 1"
let rec memP_gfilter_one #a f x l =
  match l with
  | [] -> ()
  | hd::tl ->
    if FStar.IndefiniteDescription.strong_excluded_middle (x == hd) then ()
    else memP_gfilter_one f x tl
#pop-options

val splitAt_incr_lem (#a:Type) (n:nat) (l:list a) :
  Lemma
  (requires (n < List.Tot.length l))
  (ensures (
    let _, l1 = List.Tot.splitAt n l in
    let _, l2 = List.Tot.splitAt (n+1) l in
    Cons? l1 /\ Cons?.tl l1 == l2))

#push-options "--fuel 1 --ifuel 1"
let splitAt_incr_lem #a n l =
  splitAt_eq_lem n l;
  splitAt_eq_lem (n+1) l;
  let l1, l2 = List.Tot.splitAt n l in
  let l3, l4 = List.Tot.splitAt (n+1) l in
  assert(Cons? l2);
  let x :: l2' = l2 in
  List.Tot.append_l_cons x l2' l1;
  assert(List.Tot.append l1 (x :: l2') == List.Tot.append (List.Tot.append l1 [x]) l2');
  List.Tot.append_assoc l1 [x] l2';
  List.Tot.append_length l1 [x];
  assert_norm(List.Tot.length [x] = 1);
  assert(List.Tot.length (List.Tot.append l1 [x]) = List.Tot.length l3);
  assert(List.Tot.append l1 l2 == l);
  assert(List.Tot.append (List.Tot.append l1 [x]) l2' == l);
  assert(List.Tot.append l3 l4 == l);
  assert(List.Tot.length (List.Tot.append l1 [x]) = n+1);
  List.Tot.append_length_inv_head (List.Tot.append l1 [x]) l2' l3 l4
#pop-options  

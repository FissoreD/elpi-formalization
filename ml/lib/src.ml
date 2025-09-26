
type nat =
| O
| S of nat

let rec to_int = function
  | O -> 0
  | S n -> 1 + to_int n

let pp_nat fmt n = Format.fprintf fmt "%d" (to_int n)


(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val subn : nat -> nat -> nat **)

let subn =
  sub

(** val size : 'a1 list -> nat **)

let rec size = function
| [] -> O
| _::s' -> S (size s')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x::s1' -> x::(cat s1' s2)

(** val drop : nat -> 'a1 list -> 'a1 list **)

let rec drop n s = match s with
| [] -> s
| _::s' -> (match n with
            | O -> s
            | S n' -> drop n' s')

(** val take : nat -> 'a1 list -> 'a1 list **)

let rec take n = function
| [] -> []
| x::s' -> (match n with
            | O -> []
            | S n' -> x::(take n' s'))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| x::s' -> (f x)::(map f s')

module Language =
 struct
  type coq_D =
  | Func
  | Pred
  [@@deriving show]

  type coq_B =
  | Exp
  | Coq_d of coq_D
  [@@deriving show]

  type mode =
  | Coq_i
  | Coq_o
  [@@deriving show]

  type coq_S =
  | Coq_b of coq_B
  | Coq_arr of mode * coq_S * coq_S
  [@@deriving show]

  type coq_P = nat
  [@@deriving show]

  type coq_K = nat
  [@@deriving show]

  type coq_V = nat
  [@@deriving show]

  type coq_C =
  | Coq_p of coq_P
  | Coq_v of coq_V
  [@@deriving show]

  type coq_Tm =
  | Code of coq_C
  | Data of coq_K
  | Comb of coq_Tm * coq_Tm
  [@@deriving show]

  let pp_coq_Tm fmt t =
    match t with
    | Data d -> Format.fprintf fmt "d %a" pp_coq_K d
    | _ -> pp_coq_Tm fmt t

  type 'a coq_R_ = { head : coq_Tm; premises : 'a list }
  [@@deriving show]

  type coq_A =
  | Cut
  | Call of coq_Tm
  [@@deriving show]

  type coq_Sigma = coq_V -> coq_Tm option
    (* singleton inductive, whose constructor was Build_Sigma *)
  [@@deriving show]

  type index = coq_A coq_R_ list
  [@@deriving show]

  type mode_ctx = coq_Tm -> mode list
  [@@deriving show]

  type sigT = coq_P -> coq_S
  [@@deriving show]

  type program = { rules : index; modes : mode_ctx; coq_sig : sigT }
  let pp_program fmt _p = Format.fprintf fmt "(p)"
 end

module Unif =
 struct
  type state =
  | Bot
  | OK
  | Top
  | Dead
  | Goal of Language.program * Language.coq_A
  | Or of state * Language.coq_Sigma * state
  | And of state * state * state
  [@@deriving show]

  type coq_G =
  | Coq_call of Language.program * Language.coq_Tm
  | Coq_cut of coq_G list list

  let rec pp_coq_G fmt g =
    let pp_sep = (fun fmt _ -> Format.fprintf fmt ", ") in
    let p = Format.pp_print_list  in
    match g with
    | Coq_call (_p, t) -> Language.pp_coq_Tm fmt t
    | Coq_cut l -> Format.fprintf fmt "!_{%a}" (p ~pp_sep (fun fmt e -> p ~pp_sep (fun fmt e -> pp_coq_G fmt e) fmt e)) l
  (* [@@deriving show] *)

  (** val apply_cut : (coq_G list list -> coq_G list list) -> coq_G -> coq_G **)

  let apply_cut f g = match g with
  | Coq_call (_, _) -> g
  | Coq_cut a -> Coq_cut (f a)

  type alt = coq_G list
  [@@deriving show]
  type alts = alt list
  [@@deriving show]

  (** val add_ca : coq_G list list -> coq_G -> coq_G **)

  let add_ca alts = function
  | Coq_call (pr, t) -> Coq_call (pr, t)
  | Coq_cut a1 -> Coq_cut (cat a1 alts)

  (** val add_ca_deep : nat -> coq_G list list -> coq_G list list -> coq_G list list **)

  let rec add_ca_deep n tl alts =
    match n with
    | O -> alts
    | S n0 -> map (map (fun x -> add_ca tl (apply_cut (add_ca_deep n0 tl) x))) alts

  (** val add_suff : alt list -> coq_G list -> alt list -> coq_G list list **)

  let add_suff bt hd l =
    let s = subn (size l) (size bt) in cat (map (fun x -> cat x hd) (take s l)) (drop s l)

  (** val add_deep_help :
      (alt list -> nat -> coq_G list -> coq_G list list -> alt list) -> alt list -> nat -> coq_G list -> coq_G ->
      coq_G **)

  let add_deep_help add_deep0 bt n hd =
    apply_cut (fun x -> add_suff bt hd (add_deep0 bt n hd x))

  (** val add_deep : alt list -> nat -> alt -> alt list -> alt list **)

  let rec add_deep bt n l a =
    match n with
    | O -> a
    | S n0 -> map (map (add_deep_help add_deep bt n0 l)) a

  (** val add_deep_ : alt list -> nat -> alt -> alt -> alt **)

  let add_deep_ bt n l a =
    match n with
    | O -> a
    | S n0 -> map (add_deep_help add_deep bt n0 l) a

  (** val kill : alt -> coq_G list **)

  let kill a =
    map (apply_cut (fun _ -> [])) a

  (** val make_lB0 : alt list -> alt -> coq_G list list **)

  let make_lB0 xs lB0 =
    map (fun x -> cat x lB0) xs

  (** val state_to_list : state -> alt list -> alt list **)

  let rec state_to_list a bt =
    match a with
    | Bot -> []
    | Dead -> []
    | Goal (pr, a0) ->
      (match a0 with
       | Language.Cut -> ((Coq_cut [])::[])::[]
       | Language.Call t -> ((Coq_call (pr, t))::[])::[])
    | Or (a0, _, b) ->
      let lB = state_to_list b [] in let lA = state_to_list a0 lB in add_ca_deep (size (cat lA lB)) bt (cat lA lB)
    | And (a0, b0, b) ->
      let lB0 = state_to_list b0 bt in
      let lA = state_to_list a0 bt in
      (match lA with
       | [] -> []
       | x::xs ->
         (match lB0 with
          | [] -> let lB = state_to_list b bt in map (fun y -> cat (kill x) y) lB
          | hd::l ->
            (match l with
             | [] ->
               let x0 = add_deep_ bt (S (size xs)) hd x in
               let xs0 = add_deep bt (size xs) hd xs in
               let xs1 = make_lB0 xs0 hd in
               let lB = state_to_list b (cat xs1 bt) in cat (map (fun y -> cat x0 y) lB) xs1
             | _::_ -> [])))
    | _ -> []::[]
 end

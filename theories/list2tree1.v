From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Fixpoint list_to_state (l: alts) : state :=
  match l with
  | no_alt => Bot
  | more_alt x no_alt => 
    let l := goals_to_state x.2 Bot in
    Or Bot x.1 l
  | more_alt x (more_alt y ys as t) => 
    let t := goals_to_state x.2 (list_to_state t) in
    Or Bot x.1 t
  end
with goals_to_state (l:goals) t: (state):=
  match l with
  | no_goals => (Or Top empty t)
  | more_goals x xs => 
    let '(l, tca) := goal_to_state x in
    let r := goals_to_state xs t  in
      (And l l r)
  end
with goal_to_state (l:G) :=
  match l with
  | call pr tm ca => (CallS pr tm, list_to_state ca)
  | cut ca => (CutS, list_to_state ca)
  end
. *)

Inductive G' := 
  | call' : program -> Callable -> G'
  | cut' : alts' -> G'
with alts' :=
  | no_alt'
  | more_alt' : (nat * Sigma * goals') -> alts' -> alts'
with goals' :=
  | no_goals'
  | more_goals' : (nat * G') -> goals' -> goals' 
  .

Fixpoint erase_G' (g : G') : G :=
  match g with
  | call' p c => call p c
  | cut' a => cut (erase_alts' a)
  end
with erase_alts' (a : alts') : alts :=
  match a with
  | no_alt' => nilC
  | more_alt' (_, s,gl') a' => (s,erase_goals' gl') ::: (erase_alts' a')
  end
with erase_goals' (a : goals') : goals :=
  match a with
  | no_goals' => nilC
  | more_goals' (_, g') a' => (erase_G' g') ::: (erase_goals' a')
  end.

  Fixpoint append_alts' l1 l2 := 
    match l1 with
    | no_alt' => l2
    | more_alt' (n, hd) tl => more_alt' (n, hd) (append_alts' tl l2)
    end.

    Axiom eqb_alts' : alts' -> alts' -> bool.
    Lemma xx a b : reflect (a = b) (eqb_alts' a b).
    Admitted.

    Lemma xx_refl a: eqb_alts' a a. Admitted. 

  Lemma alts_eqb_OK' : Equality.axiom eqb_alts'.
  Proof. apply: iffP2 xx xx_refl. Qed.
  HB.instance Definition _ : hasDecEq _ := hasDecEq.Build _ alts_eqb_OK'.

  #[program] Global Instance IsList_alts' : @IsList (nat * Sigma * goals') alts' :=
    {| 
    nilC := no_alt'; consC := more_alt';
    appendC := append_alts'; 
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
  Admit Obligations.

  Fixpoint append_goals' l1 l2 := 
    match l1 with
    | no_goals' => l2
    | more_goals' (n, hd) tl => more_goals' (n, hd) (append_goals' tl l2)
    end.

  #[program] Global Instance IsList_goals' : @IsList _ _ :=
    {| 
    nilC := no_goals'; consC := more_goals';
    appendC := append_goals'; 
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
  Admit Obligations.

Definition add_ca' alts a : (nat * _) :=
  match a with
  | (n, cut' a1) => (n, cut' (a1 ++ alts))
  | (n, call' pr t) => (n, call' pr t)
  end.

Definition save_goals' (a: alts') (gs b:goals') := map (add_ca' a) b ++ gs.

Definition save_alts' (a : alts') (gs: goals') (bs : alts') := 
  map (fun '((n,s,x): nat * Sigma * goals') => (n, s, save_goals' a gs x)) bs.

  Definition a2g' p A :=
  match A with
  | ACut => cut' nilC
  | ACall t => call' p t
  end.

Fixpoint a2gs' n p (b: seq A) := 
  match b with
  | nil => nilC
  | x::xs => (n, a2g' p x) ::: (a2gs' n p xs)
  end.

Fixpoint aa2gs' n p (b: (seq (Sigma * R))) := 
  match b with
  | nil => nilC
  | x::xs => (n, x.1, a2gs' n p x.2.(premises)) ::: (aa2gs' n p xs)
  end.

Definition a2gs1' n p (b : Sigma * R) :=
  a2gs' n p b.2.(premises).

Definition isnil x := erase_goals' x == nilC.
Definition isnila x := erase_alts' x == nilC.

Definition same' x y := erase_alts' x = erase_alts' y.

Definition hd' x y ys := erase_goals' x = (erase_G' y) ::: (erase_goals' ys).

Inductive nur' u : Sigma -> goals' ->  alts' -> Sigma -> alts' -> Prop :=
| StopE' s a : nur' s nilC a s a
| CutE' s s1 a ca r gl n1 : nur' s gl ca s1 r -> nur' s ((n1, cut' ca) ::: gl) a s1 r
| CallE' p s s1 a b bs gl r t n1: 
  F u p t s = [:: b & bs ] -> 
    nur' b.1 (save_goals' a gl (a2gs1' n1.+1 p b)) (save_alts' a gl ((aa2gs' n1.+1 p) bs) ++ a) s1 r -> 
      nur' s ((n1, call' p t) ::: gl) a s1 r
| FailE' p s s1 s2 t gl a al r n n1 : 
  F u p t s = [::] -> nur' s1 a al s2 r -> nur' s ((n, call' p t) ::: gl) ((n1, s1, a) ::: al) s2 r.

(* Lemma listP' {l x xs} : erase_goals' l = x ::: xs ->
  exists y ys, erase_goals' l = (erase_G' y) ::: (erase_goals' ys).
Admitted. *)

Fixpoint decorate_G (g : G) : G' :=
  match g with
  | call p c => call' p c
  | cut a => cut' (decorate_alts a)
  end
with decorate_alts (a : alts) : alts' :=
  match a with
  | no_alt => nilC
  | more_alt (s,gl) a => (0, s,decorate_goals gl) ::: (decorate_alts a)
  end
with decorate_goals (a : goals) : goals' :=
  match a with
  | no_goals => nilC
  | more_goals g a => (0, decorate_G g) ::: (decorate_goals a)
  end.

Lemma erase_decorate_G x : erase_G' (decorate_G x) = x
with erase_decorate_goals x : erase_goals' (decorate_goals x) = x
with erase_decorate_alts x : erase_alts' (decorate_alts x) = x.
- by case: x => //= a; rewrite erase_decorate_alts.
- by case: x => //= g gs; rewrite erase_decorate_goals erase_decorate_G.
- by case: x => //= -[s g] gs /=; rewrite erase_decorate_alts erase_decorate_goals.
Qed.

Definition ed := (erase_decorate_alts, erase_decorate_goals, erase_decorate_G).

(* Inductive nurk u : Sigma -> goals ->  alts -> Sigma -> alts -> Type :=
| StopE s a : nurk s nilC a s a
| CutE s s1 a ca r gl : nurk s gl ca s1 r -> nurk s ((cut ca) ::: gl) a s1 r
| CallE p s s1 a b bs gl r t : 
  F u p t s = [:: b & bs ] -> 
    nurk b.1 (save_goals a gl (a2gs1 p b)) (save_alts a gl ((aa2gs p) bs) ++ a) s1 r -> 
      nurk s ((call p t) ::: gl) a s1 r
| FailE p s s1 s2 t gl a al r : 
  F u p t s = [::] -> nurk s1 a al s2 r -> nurk s ((call p t) ::: gl) ((s1, a) ::: al) s2 r. *)

(* Lemma two u s s1 a a1 xs  : nurk u s xs a s1 a1 -> { a' & { a1' & { xs' |
  erase_alts' a' = a /\ erase_alts' a1' = a1 /\ erase_goals' xs' = xs /\
    nur' u s xs' a' s1 a1'}}}.
elim; clear.
- move=> s2 a2 *.
  exists (decorate_alts a2).
  exists (decorate_alts a2).
  exists (decorate_goals nilC).
  rewrite !ed /=; repeat split.
  apply: StopE' => //=.

- move=> s s1 a ca r gl H [a' [a1' [xs' [Ha' [Ha1' [Hxs' H']]]]]].
  eexists (decorate_alts a), a1', (decorate_goals ((cut ca) ::: gl)) => /=.
  rewrite !ed /=; repeat split => //.
  by apply: CutE' H' _; subst; rewrite /hd' /= !ed.

Admitted. *)

Lemma one u s xs a s1 a1: nur' u s xs a s1 a1 -> 
  nur u s (erase_goals' xs) (erase_alts' a) s1 (erase_alts' a1).
Proof.
  elim => /=; clear.
  - move=> *; constructor.
  - move=> *; constructor => //.
  - move=> p s s1 a [s2 r] rs gl a1 t n/= H H1 H2.
    apply: CallE H _.
    move: H2.
    rewrite/save_goals/=/map/=/save_goals'/=.
    admit.
  - move=> p s s1 s2 t gl a al r _ _ H H1 H2.
    apply: FailE H H2.
Admitted.

Definition empty_ca_G' '((_, g) : nat * _) :=
  match g with call' _ _ | cut' no_alt' => true | _ => false end.
Definition empty_caG' goals := all empty_ca_G' goals.
Definition empty_ca' alts := all (fun x => empty_caG (snd x)) alts.

Fixpoint valid_caG' (gs:goals') (a:alts') (bt:alts') {struct gs} :=
    match gs with
    | no_goals' => true
    | more_goals' (_, call' _ _) xs => valid_caG' xs a bt
    | more_goals' (_, cut' ca) xs =>
      if suffix bt ca then
        suffix ca (a ++ bt) &&
        let n := size ca - size bt in
        let ca' := take n ca in
        valid_caG' xs ca' bt
        && valid_caA_aux' ca ca' bt
      else (match ca with no_alt' => true | _ => false end) && empty_caG' xs
      end
    with valid_caA_aux' ca ca1 bt : bool :=
      if ca == bt then true
      else
      match ca with
      | no_alt' => false
      | more_alt' hd tl => valid_caG' hd.2 (behead ca1) bt && valid_caA_aux' tl (behead ca1) bt
    end
    .

  (* to be valid: size L1 <= size L2, in a sense L1 should be a suffix of L2 *)
  Fixpoint valid_caA' L1 L2 (bt:alts') {struct L1} :=
    match L1 with
    | no_alt' => true
    | more_alt' hd tl => valid_caG' hd.2 (behead L2) bt && valid_caA' tl (behead L2) bt
    end.

  Definition valid_ca' L := valid_caA' L L nilC.



Lemma two' u s s1 a a1 xs  : nur u s xs a s1 a1 -> exists a' a1' xs',
  [/\ (erase_alts' a' = a), (erase_alts' a1' = a1), (erase_goals' xs' = xs) &
    (nur' u s xs' a' s1 a1')].
elim; clear.
- move=> s2 a2 *.
  exists (decorate_alts a2).
  exists (decorate_alts a2).
  exists (decorate_goals nilC).
  rewrite !ed /=; repeat split.
  apply: StopE'.

- move=> s s1 a ca r gl H [a'[a1'[xs']]] [??? IH]; subst.
  exists (decorate_alts a).
  do 2 eexists; repeat split; last first => //=.
  apply: CutE' 3 IH => /=.
  move=> //=.
  rewrite ed//.

- move=> p s s1 a [s2 r] bs gl rs t H1/= H2 [a'[a1'[xs']]][H3 ? H4] IH; subst.
  do 3 eexists; repeat split; last first => //.
  apply: CallE' H1 _.
  admit.

- 

Admitted.

Definition l2l' {s s1 a a1 xs} (H : nur s xs a s1 a1) : alts' :=
   projT1 (projT2 (two s s1 a a1 xs H)).

Lemma l2l'P s s1 a a1 xs (H : nur s xs a s1 a1) :
  erase_alts' (l2l' H) = a1.
by rewrite /l2l'; case: two => /= ? [? []] //= ? [] ? [] ? [] ?.
Qed.


Axiom F : alts' -> state.

Lemma titi u s xs' a' s1 a1': nur' u s xs' a' s1 a1' -> valid_state (F ((s, xs') ::: a')) /\
  run u s (F ((s, xs'):::a')) s1 (F a1').
Admitted.



Definition G'2s (g : G') : state :=
  match g with
  | cut' _ => CutS
  | call' p t => CallS p t 
  end.

Fixpoint upto_append (a : goals') : state :=
  match a with
  | no_goals' => Top
  | append_goals' _ _ => Top
  | more_goals' x xs => And (G'2s x) (upto_append xs) (upto_append xs)
  end.




runtree t -> nur (t2l t)
nulr' g g' a a' -> nur g a
nulr' |g'| g' |a'| a' -> nur |g'| |a'|


nur |g'| |a'| = s |b'| -> nulr' |g'| g' |a'| a'  = s |b| b'

nur g a = s b -> exists g' a' b', |g'| = g /\ nur' g g' a a'  = s b b'

nur g [] -> nur' g g' [] []




(* todo, flip everything *)
(* Fixpoint alts'2s (a : alts') : state :=
  match a with
  | no_alt' => Bot
  | more_alt' (s,a) a1 => Bot
  | append_alt' a1 a2 => 
       Or (aux Top a1) empty (alts'2s a2)
  end
with goals'2s (g : goals') : state :=
  Top 
with aux reset (a : alts') : state := 
  match a with
  | no_alt' => Bot
  | more_alt' (s,a) a1 =>
     (* a may not be unexplored, the reset point is reset *)
     (* one alternative for this level *)
     And (upto_append a) reset a
  | append_alt' a1 a2 => 
     (* the level had only one applicable rule *)
  | more_alt' (s,a) a1 => And reset aux (upto_append a) a1

  end

. *)


From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Fixpoint list_to_state (l: alts) : state :=
  match l with
  | no_alt => Bot
  | more_alt x no_alt => 
    let l := goals_to_state x.2 KO in
    Or KO x.1 l
  | more_alt x (more_alt y ys as t) => 
    let t := goals_to_state x.2 (list_to_state t) in
    Or KO x.1 t
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
  | more_alt' : (Sigma * goals') -> alts' -> alts'
  | append_alt' :  alts' -> alts' -> alts'
with goals' :=
  | no_goals'
  | more_goals' : G' -> goals' -> goals' 
  | append_goals' : goals' -> goals' -> goals' 
  .

  Fixpoint erase_G' (g : G') : G :=
  match g with
  | call' p c => call p c
  | cut' a => cut (erase_alts' a)
  end
with erase_alts' (a : alts') : alts :=
  match a with
  | no_alt' => nilC
  | more_alt' (s,gl') a' => (s,erase_goals' gl') ::: (erase_alts' a')
  | append_alt' a1' a2' => (erase_alts' a1') ++ (erase_alts' a2')
  end
with erase_goals' (a : goals') : goals :=
  match a with
  | no_goals' => nilC
  | more_goals' g' a' => (erase_G' g') ::: (erase_goals' a')
  | append_goals' a1' a2' => (erase_goals' a1') ++ (erase_goals' a2')
  end.

  #[program] Global Instance IsList_alts' : @IsList (Sigma * goals') alts' :=
    {| 
    nilC := no_alt'; consC := more_alt';
    appendC := append_alt'; 
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
  Admit Obligations.


    #[program] Global Instance IsList_goals' : @IsList G' goals' :=
    {| 
    nilC := no_goals'; consC := more_goals';
    appendC := append_goals'; 
    (*size := _; take := _; drop := _;
    behead := _; eqB := _; suffix:= _; all:= _;
    map := _; mem := _ *)
    |}.
    Admit Obligations.


Definition add_ca' alts a :=
  match a with
  | cut' a1 => cut' (a1 ++ alts)
  | call' pr t => call' pr t
  end.

Definition save_goals' (a: alts') (gs b:goals') := map (add_ca' a) b ++ gs.

Definition save_alts' (a : alts') (gs: goals') (bs : alts') := 
  map (fun '((s,x): Sigma * goals') => (s, save_goals' a gs x)) bs.

  Definition a2g' p A :=
  match A with
  | ACut => cut' nilC
  | ACall t => call' p t
  end.

Fixpoint a2gs' p (b: seq A) := 
  match b with
  | nil => nilC
  | x::xs => (a2g' p x) ::: (a2gs' p xs)
  end.

Fixpoint aa2gs' p (b: (seq (Sigma * R))) := 
  match b with
  | nil => nilC
  | x::xs => (x.1, a2gs' p x.2.(premises)) ::: (aa2gs' p xs)
  end.

Definition a2gs1' p (b : Sigma * R) :=
  a2gs' p b.2.(premises).

  Definition isnil x := erase_goals' x == nilC.
Definition isnila x := erase_alts' x == nilC.


Definition same' x y := erase_alts' x = erase_alts' y.

Definition hd' x y ys := erase_goals' x = (erase_G' y) ::: (erase_goals' ys).

Inductive runE' u : Sigma -> goals' ->  alts' -> Sigma -> alts' -> Prop :=
| StopE' s a a' x : isnil x -> same' a a' -> runE' s x a s a'
| CutE' s s1 a ca r gl gl' : runE' s gl ca s1 r -> hd' gl' (cut' ca) gl -> runE' s gl' a s1 r
| CallE' p s s1 a b bs gl r t : 
  F u p t s = [:: b & bs ] -> 
    runE' b.1 (save_goals' a gl (a2gs1' p b)) (save_alts' a gl ((aa2gs' p) bs) ++ a) s1 r -> 
      runE' s ((call' p t) ::: gl) a s1 r
| FailE' p s s1 s2 t gl a al r : 
  F u p t s = [::] -> runE' s1 a al s2 r -> runE' s ((call' p t) ::: gl) ((s1, a) ::: al) s2 r.

Fixpoint decorate_G (g : G) : G' :=
  match g with
  | call p c => call' p c
  | cut a => cut' (decorate_alts a)
  end
with decorate_alts (a : alts) : alts' :=
  match a with
  | no_alt => nilC
  | more_alt (s,gl) a => (s,decorate_goals gl) ::: (decorate_alts a)
  end
with decorate_goals (a : goals) : goals' :=
  match a with
  | no_goals => nilC
  | more_goals g a => (decorate_G g) ::: (decorate_goals a)
  end.

Lemma erase_decorate_G x : erase_G' (decorate_G x) = x
with erase_decorate_goals x : erase_goals' (decorate_goals x) = x
with erase_decorate_alts x : erase_alts' (decorate_alts x) = x.
- by case: x => //= a; rewrite erase_decorate_alts.
- by case: x => //= g gs; rewrite erase_decorate_goals erase_decorate_G.
- by case: x => //= -[s g] gs /=; rewrite erase_decorate_alts erase_decorate_goals.
Qed.

Definition ed := (erase_decorate_alts, erase_decorate_goals, erase_decorate_G).

Inductive nurk u : Sigma -> goals ->  alts -> Sigma -> alts -> Type :=
| StopE s a : nurk s nilC a s a
| CutE s s1 a ca r gl : nurk s gl ca s1 r -> nurk s ((cut ca) ::: gl) a s1 r
| CallE p s s1 a b bs gl r t : 
  F u p t s = [:: b & bs ] -> 
    nurk b.1 (save_goals a gl (a2gs1 p b)) (save_alts a gl ((aa2gs p) bs) ++ a) s1 r -> 
      nurk s ((call p t) ::: gl) a s1 r
| FailE p s s1 s2 t gl a al r : 
  F u p t s = [::] -> nurk s1 a al s2 r -> nurk s ((call p t) ::: gl) ((s1, a) ::: al) s2 r.

Lemma two u s s1 a a1 xs  : nurk u s xs a s1 a1 -> { a' & { a1' & { xs' |
  erase_alts' a' = a /\ erase_alts' a1' = a1 /\ erase_goals' xs' = xs /\
    runE' u s xs' a' s1 a1'}}}.
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

Admitted.

Lemma two' u s s1 a a1 xs  : runE u s xs a s1 a1 -> exists a' a1' xs',
  erase_alts' a' = a /\ erase_alts' a1' = a1 /\ erase_goals' xs' = xs /\
    runE' u s xs' a' s1 a1'.
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

Admitted.

Definition l2l' {s s1 a a1 xs} (H : runE s xs a s1 a1) : alts' :=
   projT1 (projT2 (two s s1 a a1 xs H)).

Lemma l2l'P s s1 a a1 xs (H : runE s xs a s1 a1) :
  erase_alts' (l2l' H) = a1.
by rewrite /l2l'; case: two => /= ? [? []] //= ? [] ? [] ? [] ?.
Qed.


Axiom F : alts' -> state.

Lemma titi u s xs' a' s1 a1': runE' u s xs' a' s1 a1' -> valid_state (F ((s, xs') ::: a')) /\
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




runtree t -> runE (t2l t)
nulr' g g' a a' -> runE g a
nulr' |g'| g' |a'| a' -> runE |g'| |a'|


runE |g'| |a'| = s |b'| -> nulr' |g'| g' |a'| a'  = s |b| b'

runE g a = s b -> exists g' a' b', |g'| = g /\ runE' g g' a a'  = s b b'

runE g [] -> runE' g g' [] []




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


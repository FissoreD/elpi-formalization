From mathcomp Require Import all_ssreflect.

Definition predname := nat.
Inductive pred := cut | call of predname.
Inductive goal := Goal (g : pred) (ca : list (list goal)).
Definition alt := seq goal.

Definition bodiesT := predname -> list (list pred).
Definition t_empty : bodiesT := (fun _ => [::]).

Definition t_update (m : bodiesT) (x : nat) v :=
  fun x' => if x == x' then v else m x'.

Definition not_alt_goal gl := [seq Goal g [::] | g <- gl].

Definition add_last_cut (b: bodiesT) : bodiesT :=
  fun x => 
    let res := (b x) in
    match rev res with
    | [::] => [::]
    | b :: bs => rcons (rev bs) [:: cut & b]
    end.

Lemma fold_add_last_cut prog:
  (fun x : predname =>
  match rev (prog x) with
  | [::] => [::]
  | b :: bs => rcons (rev bs) (cut :: b)
  end) = add_last_cut prog.
auto.
Qed.

Lemma fold_not_alt_goal:
  forall l,
    [seq Goal g [::]  | g <- l] = not_alt_goal (l).
    auto. 
Qed.

Definition neck_cut_pred (m : bodiesT) f : bodiesT :=
  fun x' => if f == x' then [seq (cons cut x) | x <- m x'] else m x'.

Definition tail_cut_pred (m : bodiesT) f : bodiesT :=
  fun x' => if f == x' then [seq (cons cut x) | x <- m x'] else m x'.

(* add neck cut to all clauses *)
Definition tail_cut_all (m : bodiesT) : bodiesT :=
  fun x' => [seq (rcons x cut) | x <- m x'].

(* add neck cut to all clauses of f *)
Definition neck_cut_all (m : bodiesT) : bodiesT :=
  fun x' => [seq (cons cut x) | x <- m x'].

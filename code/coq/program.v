From mathcomp Require Import all_ssreflect.

Check 3 \in [:: 3 ; 4].


From elpi.apps Require Import derive.std.
From HB Require Import structures.

Definition predname := nat.
Inductive pred := cut | call of nat.
#[only(eqbOK)] derive pred.
Inductive goal := Goal (g : pred) (ca : list (list goal)).
#[only(eqbOK)] derive goal.


HB.instance Definition _ := hasDecEq.Build pred pred_eqb_OK.
HB.instance Definition _ := hasDecEq.Build goal goal_eqb_OK.

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


Ltac fold_neck_cut prog f := replace ((fun x' : predname => if f == x' then _ else prog x')) with (neck_cut_pred prog f) by auto.
Ltac fold_neck_cutH prog f Hyp := replace ((fun x' : predname => if f == x' then _ else prog x')) with (neck_cut_pred prog f) in Hyp by auto.

Ltac fold_neck_cut_all prog := replace (fun x' : predname => [seq cut :: x  | x <- prog x']) with (neck_cut_all prog) by auto.
Ltac fold_neck_cut_allH prog Hyp := replace (fun x' : predname => [seq cut :: x  | x <- prog x']) with (neck_cut_all prog) in Hyp by auto.

Ltac fold_tail_cut_all prog := replace (fun x' : predname => [seq rcons x cut  | x <- prog x']) with (tail_cut_all prog) by auto.
Ltac fold_tail_cut_allH prog Hyp := replace (fun x' : predname => [seq rcons x cut  | x <- prog x']) with (tail_cut_all prog) in Hyp by auto.

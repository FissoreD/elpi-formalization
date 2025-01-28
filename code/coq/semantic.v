From mathcomp Require Import all_ssreflect.
From det Require Import program.
From det Require Import interpreter.

Inductive same_solutions p1 p2 : seq alt -> seq alt -> Prop :=
  | CNone a1 a2: 
  (* cattura divergenza + fallimento *)
    (forall n, next_alt a1 (run p1 n) = None /\ next_alt a2 (run p2 n) = None) 
      -> same_solutions a1 a2
  | CSome a1 a2:
      forall n m x y,
        next_alt a1 (run p1 n) = Some (x) /\ next_alt a2 (run p2 m) = Some (y) 
          -> same_solutions x y (*/\ s1 = s2 *)
            -> same_solutions a1 a2.

Definition same_semantics p1 p2:=
  forall gs, same_solutions p1 p2 [:: (not_alt_goal gs)] [:: (not_alt_goal gs)].

Lemma add_cut_last_pred_empty_alts:
  forall prog,
     same_solutions prog (add_last_cut prog) [:: not_alt_goal [::]] [:: not_alt_goal [::]].
Proof.
  intros?.
Admitted.


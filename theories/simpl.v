From mathcomp Require Import all_ssreflect.
From det Require Import zify_ssreflect.

Inductive tree A :=
  | E
  | N : A -> tree A -> tree A -> tree A .

Arguments N {_}.
Arguments E {_}.

Fixpoint f acc (l: tree nat) :=
  match l with
  | E => acc
  | N v L R => 
    f (acc + f v L) R
  end.

Fixpoint f1 (l: tree nat) :=
  match l with
  | E => 0
  | N v L R => 
    v + f1 L + f1 R
  end.

Definition T := N 3 (N 2 E E) E.
Compute (f 0 T).
Compute (f1 T).


Lemma sum:
  forall t n, f n t = n + f1 t.
Proof.
  elim => //=.
  - lia.
  - move=> hd l hl r hr n.
    rewrite hr hl; lia.
Qed.
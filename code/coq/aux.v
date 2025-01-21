From mathcomp Require Import all_ssreflect.

Lemma add_comm: forall a b, (a + b)%coq_nat = b + a. Admitted.

Lemma add_trans: forall n k k0, n + k + k0 = (n + (k + k0))%coq_nat. Admitted.

Lemma add_1_r: forall n, addn n (S O) = S n. Admitted.
Lemma add0r: forall a, a + 0 = a. induction a; auto.
  rewrite addSn; auto. Qed.


Lemma rcons_non_empty {T:Type} (x:T) xs: rcons xs x <> [::].
Proof. elim: xs => //. Qed.

Lemma rev_non_empty {T:Type} (x:T) xs: rev (x :: xs) <> [::].
Proof. rewrite rev_cons. apply rcons_non_empty. Qed.


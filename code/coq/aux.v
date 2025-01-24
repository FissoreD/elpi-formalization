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

Lemma leq_add:
  forall a b, a <= b -> exists c, a + c = b.
Admitted.

Lemma map_app {T:Type} {Q:Type}:
  forall (l1: list T) l2 (f:T->Q),
    [seq f x | x <- l1] ++ [seq f x | x <- l2] =
    [seq f x | x <- l1 ++ l2].
Proof.
  induction l1; auto; intros; simpl; f_equal; auto.
Qed.

Fixpoint In {T: Type} (e:T) l :=
  match l with
  | [::] => False
  | x:: xs => x = e \/ In e xs
  end.

Fixpoint In' {T: Type} R (l: list T) :=
  match l with
  | [::] => False
  | x:: xs => R x \/ In' R xs
  end.

Fixpoint for_all {T:Type} (P : T -> Prop) l :=
  match l with
  | [::] => True
  | [::x&xs] => P x /\ for_all P xs
  end.

Fixpoint exists_ {T:Type} (P : T -> Prop) l :=
  match l with
  | [::] => False
  | [::x&xs] => P x \/ exists_ P xs
  end.

Lemma exists_split {T : Type}:
  forall a b P, @exists_ T P a \/ exists_ P b -> exists_ P (a ++ b).
Proof.
  induction a.
  intros.
  destruct H; try by [].
  intros.
  unfold exists_.
  simpl.
  inversion H.
  inversion H0; auto.
  all:right; apply IHa; auto.
Qed.
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

Lemma split_in {T: Type}: forall (e:T) l1 l2,
  In e l1 \/ In e l2 <-> In e (l1 ++ l2).
Proof.
  split.
  destruct 1.
  induction l1; simpl; try easy.
  destruct H; auto.
  induction l1; simpl; auto.
  induction l1; auto.
  inversion 1; simpl; auto.
  apply or_assoc.
  right.
  auto.
Qed.

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
  forall a b P, @exists_ T P a \/ exists_ P b <-> exists_ P (a ++ b).
Proof.
  constructor.
  - revert a b.
    induction a.
    inversion 1; try by [].
    inversion 1; try by [].
    inversion H0.
    constructor 1.
    auto.
    constructor; apply IHa; auto.
    constructor; apply IHa; auto.
  - revert b.
    induction a; auto.
    inversion 1.
    now repeat constructor.
    
    enough (exists_ P a0 \/ exists_ P b).
    destruct H1.
    left; constructor 2; auto.
    auto.
    apply IHa; auto.
Qed.

Lemma forall_split {T:Type}: 
  forall a b P, @for_all T P a /\ for_all P b <-> for_all P (a ++ b).
Proof.
  constructor; revert b; induction a.
  destruct 1; auto.
  destruct 1; constructor; inversion H; auto.
  split; auto.
  constructor.
  inversion 1; apply IHa in H1 as []; repeat constructor; auto.
Qed.

Lemma same_int: forall (a:nat), a == a = true.
Proof. induction a; auto. Qed.
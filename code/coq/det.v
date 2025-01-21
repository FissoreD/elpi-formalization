From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.

Definition functional_goal p :=
  forall n r g, run p n (not_alt_goal g) [::] = r -> r = None \/ r = Some [::].

Definition functional_pred p f :=
  forall n r, run p n [:: Goal (call f) [::]] [::] = r -> r = None \/ r = Some [::].

Lemma same_int: forall (a:predname), a == a = true.
Proof. induction a; auto. Qed.

Ltac fold_neck_cut prog f := replace ((fun x' : predname => if f == x' then _ else prog x')) with (neck_cut_pred prog f) by auto.
Ltac fold_neck_cutH prog f Hyp := replace ((fun x' : predname => if f == x' then _ else prog x')) with (neck_cut_pred prog f) in Hyp by auto.

Ltac fold_neck_cut_all prog := replace (fun x' : predname => [seq cut :: x  | x <- prog x']) with (neck_cut_all prog) by auto.
Ltac fold_neck_cut_allH prog Hyp := replace (fun x' : predname => [seq cut :: x  | x <- prog x']) with (neck_cut_all prog) in Hyp by auto.

Ltac fold_tail_cut_all prog := replace (fun x' : predname => [seq rcons x cut  | x <- prog x']) with (tail_cut_all prog) by auto.
Ltac fold_tail_cut_allH prog Hyp := replace (fun x' : predname => [seq rcons x cut  | x <- prog x']) with (tail_cut_all prog) in Hyp by auto.

Lemma not_alt_goal_app:
  forall a b, not_alt_goal a ++ not_alt_goal b = not_alt_goal (a++b).
Proof.
  induction a; auto.
  intros; simpl; f_equal; auto.
Qed.

Lemma functional_neck_cut_all:
  forall p, functional_goal (neck_cut_all p).
Proof.
  intros prog n.
  elim: n => /=.
  - intro; subst; auto.
  - move=> n IH; destruct r; auto.
    destruct g as [|g gs]; auto.
    destruct g.
    + simpl. intros.
      eapply IH.
      apply H.
    + simpl.
      unfold neck_cut_all.
      destruct (prog p) eqn:?; auto.
      simpl.
      fold_neck_cut_all prog.
      destruct n; auto.
      simpl.
      intros.
      apply pumping1 in H.
      specialize (IH (Some l) (l0 ++ gs)).
      rewrite <-not_alt_goal_app in IH.
      apply IH in H.
      destruct H.
      by [].
      inversion H; auto.
Qed.

Fixpoint In {A:Type} (a:A) (l:list A) : Prop :=
    match l with
      | nil => False
      | b :: m => b = a \/ In a m
    end.

(* Lemma InOrNot:
  forall {T:Type} (e:T) l, In e l \/ not (In e l).
Proof.
  induction l; auto.
  destruct IHl.
  left.
  simpl.
  right.
  auto.
  simpl.
  case (a = e). *)


(* 
  Given some goals G, GS and gs.
  if (...G, !, gs) each with empty cut-alternatives gives a solution l
    or one of the alternatives among [(...G1, !, gs), ..., (...GN, !, gs)] with
      GS = [G1,...,GN] succeeds, then exists at least a succeeding goal G' in [G|GS]
*)

From Coq Require Import FunctionalExtensionality.

(* Lemma aaa:
  run (tail_cut_all prog) n (not_alt_goal G') [::] = Some l -> *)


Lemma blah prog n l:
  forall G GS gs,
    run (tail_cut_all prog) n (not_alt_goal (rcons G cut ++ gs))
[seq not_alt_goal (b ++ gs)  | b <- [seq rcons x cut  | x <- GS]] = Some l ->
    exists G', run (tail_cut_all prog) n (not_alt_goal G') [::] = Some l.
Proof.
  elim: n=> // n IH.
  intro.
  destruct (rcons G cut) as [|G' GS'] eqn:RC.
  destruct (rcons_non_empty _ _ RC).
  destruct G'.
  1:{ simpl.
    intros.
    destruct G; inversion RC; subst; clear RC.
    2:{
      specialize (IH G [::] gs).
      simpl in IH.
      specialize (IH H) as [].
      exists (cut :: rcons G cut ++ gs); simpl; auto.
    }
    simpl in H.
    exists (cut :: gs).
    now simpl.
  }
  intros GS gs.
  simpl.
  unfold tail_cut_all.
  destruct (prog p) eqn:?; simpl.
  destruct GS.
  by [].
  simpl.
  fold_tail_cut_all prog.
  
  intros.
  specialize (IH _ _ _ H) as [].
  exists (cut :: x); auto.

  fold_tail_cut_all prog.
  intros.
Admitted.


Lemma functional_tail_cut_all:
  forall p, functional_goal (tail_cut_all p).
Proof.
  intros prog n r.
  elim: n => /=.
  - move => _ ->; auto.
  - move=> n IH; destruct r; auto.
    assert (IH' : forall g : seq pred, run (tail_cut_all prog) n (not_alt_goal g) [::] = Some l ->
      Some l = Some [::]).
    intros; destruct (IH _ H); by[].
    clear IH.

    destruct g as [|g gs]; auto; simpl.
    destruct g as [|p].
    + intros.
      right; eapply IH'.
      apply H.
    + unfold tail_cut_all.
      destruct (prog p) as [|G GS] eqn:?; auto; simpl.
      fold_tail_cut_all prog.
      rewrite not_alt_goal_app.
      intros.
      right.
      rewrite cats0 in H.
      assert (H':[seq [seq Goal x [::]  | x <- b] ++ not_alt_goal gs  | b <- [seq rcons x cut  | x <- GS]] =
        [seq (not_alt_goal (b++gs)) | b <- [seq rcons x cut  | x <- GS]]).
      f_equal.
      apply functional_extensionality; intros.
      now rewrite not_alt_goal_app.
      rewrite H' in H.
      clear H'.


      
      pose proof (blah prog n l G GS gs H) as [].
      eapply IH'.
      apply H0.
Qed.




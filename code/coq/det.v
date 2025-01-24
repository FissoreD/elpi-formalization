From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.

(* Definition functional_prog' p :=
  forall n r g a, run p n g a = r -> r = None \/ r = Some a. *)

Definition functional_prog p :=
  forall n r g, run p n (not_alt_goal g) [::] = r -> r = None \/ r = Some [::].

Definition functional_pred p f :=
  forall n r, run p n [:: Goal (call f) [::]] [::] = r -> r = None \/ r = Some [::].

Definition functional_goal p g :=
  forall n r, run p n (not_alt_goal g) [::] = r -> r = None \/ r = Some [::].

Definition functional_goal' p g :=
  forall n r, run p n (not_alt_goal g) [::] = r -> r = Some [::].

Lemma functional_neck_cut_all:
  forall p, functional_prog (neck_cut_all p).
Proof.
  move=> prog n.
  elim: n => /=.
  - move=> r _ <-; auto.
  - move=> n IH [sol|]; auto.
    move=> [|[|p] gs] /=; auto.
    + apply IH.
    + simpl; unfold neck_cut_all.
      destruct (prog p) as [|s] eqn:?; auto.
      simpl; fold_neck_cut_all prog.
      destruct n; auto.
      move => /= H.
      apply pumping1 in H.
      specialize (IH (Some sol) (s ++ gs)).
      rewrite <-map_cat in H.
      now apply IH.
Qed.

Definition all_rules_have_cut (p: bodiesT) :=
  forall f, for_all (exists_ (fun x => x = cut)) (p f).

Definition goal_has_cut :=
  (exists_ (fun g => match g with Goal g _ => g = cut end)).

Definition all_goals_have_cut l := for_all (goal_has_cut) l.

Lemma all_have_cut_save_alt {b a gs} :
  exists_ (eq^~ cut) b ->
  goal_has_cut gs ->
  goal_has_cut (save_alt a b gs).
Proof.
  (* revert a. *)
  unfold save_alt.
  revert gs.
  elim: b.
  inversion 1.
  move=> b bs IH gs [|CUT_B CUT_BS].
  intros; subst.
  constructor; auto.
  simpl.
  constructor 2.
  now apply IH.
Qed.

Lemma all_have_cut_more_alts {a bs gs} :
  for_all (exists_ (fun x => x = cut)) (bs) -> 
    all_goals_have_cut (gs :: a) ->
      all_goals_have_cut (more_alt a bs gs).
Proof.
  unfold more_alt.
  move=> CUT_BS [CUT_GS CUT_A].
  induction bs as [|b bs]; auto.
  destruct CUT_BS as [CUT_B CUT_BS].
  simpl.
  constructor.
  apply all_have_cut_save_alt; auto.
  now apply IHbs.
Qed.


Lemma all_goals_with_cut_more_general' {prog g a r}:
  all_rules_have_cut prog ->
    all_goals_have_cut (g :: a) ->
      Elpi.nur prog g a r ->
      exists g', In g' (g::a) /\ Elpi.nur prog g' [::] r.
Proof.
  move=> ARC AGC RUN.
  induction RUN.
  - destruct AGC as [[] ?].
  - exists ((Goal cut ca :: gl)); repeat constructor; auto.
  - assert (all_goals_have_cut (gl :: a)).
    1:{ destruct AGC as [[] ?]; try by []. }
    clear AGC.
    specialize (ARC f).
    rewrite H in ARC.
    assert (all_goals_have_cut (save_alt a b gl :: more_alt a bs gl)).
      apply (@all_have_cut_more_alts) with (bs:=b :: bs); auto.
    specialize (IHRUN H1) as (?&?&?).
    exists x.
    constructor; auto.
    revert H2.
    unfold more_alt, save_alt.
    admit.
  - destruct AGC as [AGC1 AGC2].
    destruct (IHRUN AGC2) as [?[]].
    exists x.
    constructor; auto.
    simpl.
    auto.
Abort.









Definition inRun prog g gs a :=
  forall n, let r := run prog n g a in In' (fun g' => r = run prog n g' a) gs.

Lemma all_goals_with_cut_more_general' prog n r:
  all_rules_have_cut prog ->
    forall g gs, 
      all_goals_have_cut (g :: gs) ->
        run prog n g gs = r ->
          exists n' g', inRun prog g' (g::gs) [::] /\ n' <= n /\ run prog n' g' [::] = r.
Proof.
  intro.
  induction n.
  + simpl; intros; subst. exists 0, g; simpl; constructor; auto.
    unfold inRun; simpl; auto.
  + destruct g.
    solve [intros; inversion H0; inversion H2].

    destruct g.
    destruct g as [|p].
    + simpl; intros.

      exists (n+1), (Goal cut ca :: g0); simpl.
      unfold inRun.
      rewrite add_1_r.
      simpl.
      auto.
    +
      pose proof (H p) as Hp.
      destruct (prog p) eqn:PP.

      destruct gs; simpl; rewrite PP.
      exists 0, (Goal (call p) ca :: g0); unfold inRun; simpl; auto.
      intros.
      inversion H0.
      specialize (IHn _ _ H3 H1) as (?&?&?&?&?).

      exists x, x0; unfold inRun; simpl; constructor; auto.
      intro.

      specialize (H4 n0); simpl in H5; auto.      
    +
      simpl.
      rewrite PP.
      intros.

      assert (all_goals_have_cut (g0 :: gs)).
      destruct H0 as [[] B]; try discriminate.
      constructor; auto.

Abort.


Lemma functional_all_with_cut:
  forall prog, all_rules_have_cut prog -> functional_prog prog.
Proof.
  intros prog H n.
  induction n; auto.
  simpl.
  destruct g as [|g gs]; simpl; auto.
  destruct g as [|p].
  apply IHn.
  destruct (prog p) eqn:?.
  auto.
  rewrite cats0.
  rewrite <-map_cat.
  intro.
  destruct r; auto.
  pose proof (H p) as Hp.
  rewrite Heql in Hp.

  (* apply all_goals_with_cut in H0 as [?[?[]]]; auto.
  epose proof (pumping_leq _ _ _ _ _ _ H0 H1).
  eapply IHn.
  apply H2. *)
Admitted.

Lemma all_have_cut_tail_cut_all:
  forall p, all_rules_have_cut(tail_cut_all p).
Proof.
  intros ??.
  unfold tail_cut_all.
  destruct (p f); simpl; auto.
  split.
  induction l; simpl; auto.
  
  induction l0; simpl; auto.
  constructor; auto.
  induction a; simpl; auto.
Qed.

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  intro.
  now pose proof (functional_all_with_cut (tail_cut_all p) (all_have_cut_tail_cut_all p)).
Qed.
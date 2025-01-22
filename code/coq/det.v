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


Lemma same_int: forall (a:predname), a == a = true.
Proof. induction a; auto. Qed.

Lemma not_alt_goal_app:
  forall a b, not_alt_goal a ++ not_alt_goal b = not_alt_goal (a++b).
Proof.
  induction a; auto.
  intros; simpl; f_equal; auto.
Qed.

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
      rewrite <-not_alt_goal_app in IH.
      now apply IH.
Qed.

Fixpoint has_cut l :=
  match l with
  | [::] => False
  | (cut :: _) => True
  | _ :: xs => has_cut xs
  end.

Fixpoint all_has_cut (l: seq (seq pred)) :=
  match l with
  | [::] => True
  | [::x&xs] =>
    has_cut x /\ all_has_cut xs
  end.

Definition all_have_cut (p: bodiesT) :=
  forall f, all_has_cut (p f).

Lemma all_goals_with_cut prog n r:
  forall g gs tl, all_have_cut prog ->
    all_has_cut (g :: gs) ->
      (* in all goal (g::gs) we have a bang and each of them has no cut-alternatives,
            therefore, 
              -if a goal g' in (g::gs) succeeds, we have
                the same result as running the goal g' alone (the alternative being rejected)
              -otherwise, if all goals fails, the lemma is trivial
            
       *)
      run prog n (not_alt_goal (g ++ tl)) 
        [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl | b <- gs] = r ->
      exists g n', n' <= n /\ run prog n' (not_alt_goal g) [::] = r.
Proof.
  destruct r as [s|].
  2:{ intros. exists [::], 0; auto. }
  (* here r is Some s*)
  induction n; [by []|].
  destruct g as [|G GTL].
    - move=> ??? [] //.
    - (* here g is not empty: it is the list [G|GTL] *)
      move=> gs tl ACP ACG.
      destruct G as [|p].
      now intros; exists (GTL++tl), n.
      - (* here G is a call of a predicate p *)
        assert (all_has_cut (GTL :: gs)) by auto.
        clear ACG.
        destruct (prog p) as [|sol sols] eqn:PP.
        + (*here no solution for prog p*)
          simpl; rewrite PP.
          destruct gs; [by[]|].
          (*here gs is non empty*)
          simpl.
          intros.
          destruct H as [].
          rewrite not_alt_goal_app in H0.
          specialize (IHn l gs tl ACP H1 H0) as [?[?[]]].
          exists x, x0; split; auto.
        + (*here prog p has some solutions (sol::sols)*)
          simpl.
          rewrite PP.


Admitted.

Lemma functional_all_with_cut:
  forall prog, all_have_cut prog -> functional_prog prog.
Proof.
  unfold all_have_cut.
  intros prog H n.
  induction n; auto.
  simpl.
  destruct g as [|g gs]; simpl; auto.
  destruct g as [|p].
  apply IHn.
  destruct (prog p) eqn:?.
  auto.
  rewrite cats0.
  rewrite not_alt_goal_app.
  intro.
  destruct r; auto.
  pose proof (H p) as Hp.
  rewrite Heql in Hp.
  apply all_goals_with_cut in H0 as [?[?[]]]; auto.
  epose proof (pumping_leq _ _ _ _ _ _ H0 H1).
  eapply IHn.
  apply H2.
Qed.

Lemma all_have_cut_tail_cut_all:
  forall p, all_have_cut(tail_cut_all p).
Proof.
  unfold tail_cut_all.
  intros ??.
  destruct (p f); simpl; auto.
  split.
  induction l; simpl; auto.
  destruct a; auto.
  induction l0; simpl; auto.
  constructor; auto.
  induction a; simpl; auto.
  destruct a; auto.
Qed.

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  intro.
  now pose proof (functional_all_with_cut (tail_cut_all p) (all_have_cut_tail_cut_all p)).
Qed.
  (*Old incomplete proof without functional_all_with_cut *)
  (* simpl.
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
      clear H'. *)

(* Admitted. *)




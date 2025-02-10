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

Module Elpi.
  Definition success p g a :=
    exists x, Elpi.nur p g a x.

  Definition functional_goal p g :=
    (exists x, Elpi.nur p g [::] x) -> Elpi.nur p g [::] [::].

  Lemma functional_neck_cut_all:
    forall p g, functional_goal (neck_cut_all p) (not_alt_goal g).
  Proof.
    intros ??[x H].
    remember (neck_cut_all p).
    remember (not_alt_goal g).
    remember [::].
    revert g Heqb Heql0 Heql.
    induction H.
    - intros; subst; constructor.
    - intros; subst; constructor.
      destruct g; inversion Heql; subst.
      eapply IHnur; auto.
    - intros; subst.
      destruct g; inversion Heql.
      subst.
      econstructor.
      eapply H.
      simpl in Heql.
      (* econstructor 3. *)
      (* apply H. *)
  Abort.
End Elpi.

Definition all_pred_have_cut :=
  for_all (exists_ (fun x => x = cut)).

Definition all_rules_have_cut (p: bodiesT) :=
  forall f, all_pred_have_cut (p f).

Definition goal_has_cut :=
  (exists_ (fun g => match g with Goal g _ => g = cut end)).

Definition all_goals_have_cut l := for_all (goal_has_cut) l.

Lemma all_have_cut_save_alt {b a gs} :
  exists_ (eq^~ cut) b ->
  goal_has_cut gs ->
  goal_has_cut (save_alt a b gs).
Proof.
  unfold save_alt.
  revert gs.
  elim: b.
  inversion 1.
  move=> b bs IH gs [|CUT_B CUT_BS].
  intros; subst.
  constructor; auto.
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
  constructor.
  apply all_have_cut_save_alt; auto.
  now apply IHbs.
Qed.

(* Lemma more_goals {prog n g gs l a1} :
  run prog n (g++gs) a1 = Some l ->
    (exists n' a2, n' <= n /\ run prog n' gs a2 = Some l).
Proof.
  revert g gs a1.
  induction n.
    exists 0, [::]; auto.
  destruct g.
    exists n.+1, a1; auto.
  destruct g; destruct g.
    simpl.
    intros.
    apply IHn in H as [?[?[]]].
    exists x, x0; auto.
  simpl.
  destruct (prog n0) eqn:PP.
    unfold more_alt, save_alt; simpl.
    destruct a1; simpl.
      inversion 1.
    intros. 
    exists (n), 
    de
  intros. *)

(* Lemma invalid_eq:
  forall {T : Type} l1 (ff: seq (seq T)),
    ff = l1 ++ [::] :: ff -> False.
Proof.
  induction l1; simpl in *.
    induction ff; try by [].
    inversion 1; auto.
  intros.
  destruct ff; try by [].
  inversion H.
Admitted.

Lemma aaa ff prog n l1:
  next_alt ff (run prog n) = Some (l1 ++ ff) -> False.
Proof.
  revert l1 ff.
  induction n; destruct ff; auto; try by [].
  simpl.
  destruct l.
    inversion 1.
    eapply invalid_eq.
    apply H1.
  destruct g.
  destruct g.
  intros.
  admit. *)

Lemma map_cat_deep {T:Type} {R:Type} l gs:
  forall (P:T -> R),
  [seq [seq P x | x <- b] ++ [seq P x | x <- gs] | b <- l] = [seq [seq P x | x <- b ++ gs] | b <- l].
Proof.
  revert gs; induction l; intros; simpl; f_equal; auto.
  now rewrite map_cat.
Qed.

Section CUT_PROG.

  Context {prog : bodiesT}.
  Context (CProg : all_rules_have_cut prog).

  Lemma bah1 {n g alts gs l1 ff}:
      (* ff = [::] -> *)
    all_pred_have_cut (g :: alts) ->
      (* all_goals_have_cut ff -> *)
    (* 
      run prog n (save_alt ff g  R ) ([seq save_alt ff b R   | b <- l0] ++ ff) = Some l1 *)
      run prog n (save_alt ff g [seq Goal x ff | x <- gs])
      (*[seq save_alt ff b R              | b <- l0] ++ ff *)
        ([seq save_alt ff b [seq Goal x ff | x <- gs]  | b <- alts] ++ ff) = Some (l1++ff) ->
          exists g n', n' <= n /\ run prog n' [seq Goal x ff | x <- g] ff = Some (l1++ff).
  Proof.
    intro; subst; repeat rewrite cats0.
    
    (* intros.
    epose proof (bah12 _ _ H1) as [?[?[]]].
    unfold save_alt in H3.
    rewrite <-map_cat in H3.
    exists (x++gs), x0; auto.
    Unshelve.
    3:{ constructor. }
    inversion H; auto.
    constructor; auto.
    constructor. *)

    revert ff g alts gs l1 H .
    induction n.
      by [].
    simpl.
    unfold save_alt.
    destruct g.
      now inversion 1.
    simpl.
    destruct p.
      intros.
      exists (g++gs), n. rewrite <-map_cat in H0; auto.
    unfold more_alt; simpl.
    destruct (prog n0) eqn:PP; simpl.
      destruct alts as [|alt alts].
        admit.
      simpl.
      intros.
      inversion H.
      eapply IHn in H0 as (?&?&?&?); auto.
      exists x, x0; auto.
    intros.
    rewrite <-map_cat in H0.
    rewrite map_cat_deep in H0.
    pose ((([seq [seq Goal x ff  | x <- b ++ gs]  | b <- alts] ++ ff))) as TT.
    pose ([seq Goal x ff  | x <- g ++ gs]) as GG.
    fold TT GG in H0.
    epose proof (IHn TT l l0 (g++gs) l1).
    specialize (CProg n0). 
    rewrite <-PP in H1.
    specialize (H1 CProg).
     

    (* qui per cercare invariante *)
    (* destruct l as [|l ls].
      unfold save_alt in H1.
      simpl in *.
      admit.
    destruct l.
      unfold save_alt in H1.
      admit.
    unfold save_alt in H1.
      simpl in H1.
    destruct n.
      by [].
    simpl in H1.
    destruct (prog n1).
      admit.
    simpl in H1. *)
    
    (* Se solo riuscissi a risolvere questo... *)
    pose ([seq [seq Goal x ff  | x <- b ++ gs]  | b <- alts]).
    assert (T = l2).
      unfold T, l2.
      clear H H0 H1 IHn PP R.
      induction alts; simpl; f_equal; auto.
      rewrite map_cat; auto.
    rewrite H2 in H1.
    clear H2 T.
    (* R = [seq Goal x ff  | x <- g ++ gs] *)
    (* l2 = [seq [seq Goal x ff  | x <- b ++ gs]  | b <- alts] *)
    (* run prog n (save_alt l2 l R) ([seq save_alt l2 b R  | b <- l0] ++ l2) = Some l1 *)
    
    destruct l.
    unfold save_alt in H1; simpl in H1.
      admit.
    destruct n; simpl in H1; try by [].
    destruct p; [admit|].
    destruct (prog n1) eqn:PP1.
    admit.

    unfold more_alt in H1; simpl in H1.
    pose ([seq save_alt l2 b R  | b <- l0] ++ l2) as RR; fold RR in H1.
    pose (([seq Goal x l2  | x <- l] ++ R)) as TT; fold TT in H1.
    (* TT = [seq save_alt l2 b R  | b <- l0] ++ l2 *)
    (* RR = [seq Goal x l2  | x <- l] ++ R *)
    (* run prog n (save_alt RR l3 TT) ([seq save_alt RR b TT  | b <- l4] ++ RR) = Some l1 *)



  Admitted.

  Lemma bah {n l l0 gs l1}:
    all_pred_have_cut (l :: l0) ->
      run prog n (save_alt [::] l (not_alt_goal gs))
        [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] = Some l1 ->
          exists g, run prog n (not_alt_goal g) [::] = Some l1.
  Proof.
    intros.
    assert (all_goals_have_cut [::]).
    constructor.
    epose proof (bah1 H H1 H0) as (?&?&?&?).
    apply (pumping_leq _ _ _ _ _ _ H2) in H3.
    exists x; auto.
  Qed.

  Lemma functional_all_with_cut: functional_prog prog.
  Proof.
    intros n.
    induction n; auto.
    destruct g as [|g gs]; simpl; auto.
    destruct g as [|p].
      apply IHn.
    destruct (prog p) eqn:?; auto.
    simpl; rewrite cats0.
    destruct r; auto.
    pose proof (CProg p) as Hp.
    rewrite Heql in Hp.
    intro.
    epose proof (bah Hp H) as [g HP].
    apply IHn in HP; auto.
  Qed.
End CUT_PROG.

Lemma all_have_cut_tail_cut_all:
  forall p, all_rules_have_cut(tail_cut_all p).
Proof.
  intros ??.
  unfold tail_cut_all.
  destruct (p f); simpl; auto.
  split.
  constructor.
  induction l; simpl; auto.

  induction l0; simpl; auto.
  constructor; auto.
  induction a; simpl; auto.
Qed.

Lemma functional_tail_cut_all:
  forall p, functional_prog (tail_cut_all p).
Proof.
  intro.
  
  eapply (functional_all_with_cut).
  apply all_have_cut_tail_cut_all.
Qed.
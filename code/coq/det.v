From Coq Require Import FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

From det Require Import program.
From det Require Import interpreter.
From det Require Import aux.


Lemma map_cat_deep {T:Type} {R:Type} l gs:
  forall (P:T -> R),
  [seq [seq P x | x <- b] ++ [seq P x | x <- gs] | b <- l] = [seq [seq P x | x <- b ++ gs] | b <- l].
Proof.
  revert gs; induction l; intros; simpl; f_equal; auto.
  now rewrite map_cat.
Qed.

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

Lemma succeed_hd_list {prog n s}:
  forall hd gs a, 
    run prog n (hd ++ gs) a = Some s ->
      exists n', n' <= n /\
        ((exists a', run prog n' gs a' = Some s) \/ next_alt a (run prog n') = Some s).
Proof.
  induction n.
    exists 0; constructor; auto; left; exists [::]; auto.
  destruct hd.
    exists (n.+1); constructor; auto; left; exists a; auto.
  destruct g as [[|p] ca].
    (* cut case *)
    simpl.
    intros.
    apply IHn in H as [?[]].
    exists x; constructor; auto.
Abort.

Lemma succeed_hd {prog n s}:
  forall hd gs a, 
    run prog n (hd :: gs) a = s ->
      exists n', n' <= n /\
        ((exists a', run prog n' gs a' = s) \/ next_alt a (run prog n') = s).
Proof.
  induction n.
    exists 0; constructor; auto; left; exists a; auto.
  destruct hd; destruct g.
    simpl.
    exists n; constructor; auto; left; exists ca; auto.
  simpl.
  destruct (prog n0); unfold more_alt, save_alt; simpl.
    exists n; constructor; auto; auto.
  destruct l.
    simpl.
    exists n; constructor; auto; left; eexists.
    apply H.
  simpl.
  intros.
  apply IHn in H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
Abort.

Lemma goals_with_cut_big_step {prog n s}:
  forall g1 g2 ca a,  
    run prog n (g1 ++ Goal cut ca :: g2) a = s ->
      exists n', n' <= n /\ 
        (next_alt a (run prog n') = s \/ run prog n' g2 ca = s).
Proof.
  intro.
  revert n.
  induction g1.
    destruct n; simpl.
      exists 0; auto.
    intros.
    exists n; auto.
  destruct n.
    exists 0; auto.
  destruct a; destruct g; simpl.
    intros.
    specialize (IHg1 _ _ _ _ H) as (?&?&?).
    exists x.
    constructor; auto.
  auto.

  admit.
Abort.

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

Inductive IN_IND (prog: bodiesT) : list goal -> ( seq (seq goal)) -> Prop :=
  | IN_IND_OK g gs: IN_IND g (g::gs)
  | IN_IND_KO g ign gs: IN_IND g gs -> IN_IND g (ign::gs)
  | IN_IND_RC ca (a:seq (seq goal)) p g gs tl :
      IN_IND g ([seq [seq Goal x a | x <- x] ++ tl | x <- prog p] ++ gs) ->
        IN_IND g ((Goal (call p) ca :: tl) :: gs)
  .


Lemma all_goals_with_cut_more_general' {prog g a r}:
  all_rules_have_cut prog ->
    all_goals_have_cut (g :: a) ->
      Elpi.nur prog g a r ->
      exists g', IN_IND prog g' (g::a) /\ Elpi.nur prog g' [::] r.
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
    intro.
    econstructor 3.
    rewrite H.
    apply H2.
  - destruct AGC as [AGC1 AGC2].
    destruct (IHRUN AGC2) as [?[]].
    exists x.
    constructor; auto.
    constructor; auto.
Abort.

Lemma all_goals_with_cut_more_general'' {prog n g a r}:
  all_rules_have_cut prog ->
    all_goals_have_cut (g :: a) ->
      run prog n g a = r ->
      exists g' n', IN_IND prog g' (g::a) /\ run prog n' g' [::] = r. (*TODO: add: n' <= n*)
Proof.
  revert g a r.
  induction n.
  + intros; simpl in H1; subst; exists g, 0; repeat constructor.
  + simpl.
    destruct g.
    intros; destruct H0 as [[]?].
  + destruct g; destruct g.
    * intros.
      exists ((Goal cut ca :: g0)), (n.+1); repeat constructor; auto.
    * intros.
      destruct (prog n0) eqn:PP.
        unfold more_alt in H1; simpl in H1.
        destruct a; simpl in *.
          exists (Goal (call n0) ca::g0), 0; split; auto; repeat constructor.
        destruct H0.
        epose proof (IHn _ _ _ H H2 H1).
        destruct H3 as (?&?&?&?).
        exists x,x0; constructor; auto.
        econstructor 3; auto.
        rewrite PP; auto.
      --- (*non empty prog*)
      simpl in H1.
      epose proof (IHn _ _ _ H _ H1) as (?&?&?&?).
      exists x,x0; constructor; auto.
      econstructor 3.
      rewrite PP.
      apply H2.
      Unshelve.
      2:{
          epose proof (@all_have_cut_more_alts a (l::l0) g0) as HH.
          eapply HH.
          specialize (H n0); rewrite PP in H; auto.
          inversion H0.
          inversion H2.
          inversion H4.
          constructor; auto.
        }
        apply [::].
Qed.

(* in all goal (g::gs) we have a bang and each of them has no cut-alternatives,
      therefore, 
        -if a goal g' in (g::gs) succeeds, we have
          the same result as running the goal g' alone (the alternative being rejected)
        -otherwise, if all goals fails, the lemma is trivial
      
  *)
Lemma all_goals_with_cut prog n r:
  forall g gs tl, all_rules_have_cut prog ->
    all_pred_have_cut (g :: gs) ->
      run prog n (not_alt_goal (g ++ tl))
        (more_alt [::] gs (not_alt_goal tl)) = r ->
        (* [seq [seq Goal x [::]  | x <- b] ++ not_alt_goal tl | b <- gs] = r -> *)
        exists g n', n' <= n /\ run prog n' (not_alt_goal g) [::] = r.
Proof.
  induction n.
    now exists [::], 0; auto.
  destruct g; simpl.
    now destruct 2 as [[] ?].
  destruct p as [|p]; simpl.
    now intros; exists (cut :: g ++ tl), (n.+1); auto.
  destruct (prog p) eqn:PP.
    destruct 2 as [[] ?]; try by [].
    unfold more_alt; simpl.
    destruct gs; simpl.
      now exists [::], 0; auto.
    unfold save_alt.
    rewrite <-map_cat.
    intro.
    epose proof (IHn _ _ _ H H1 H2).
    destruct H3 as (gg&nn&?&?).
    now exists gg,nn; auto.
  simpl.
  destruct 2 as [[]?]; [by[]|].
  epose proof (IHn _ _ _ H (conj H0 H1)).
  intros.
  

Admitted.

Section CUT_PROG.

  Context {prog : bodiesT}.
  Context (CProg : all_rules_have_cut prog).

  Lemma goals_with_cut_big_step {n s}:
    forall g1 g2 ca,  
      run prog n ([seq Goal g ca | g <- g1] ++ Goal cut ca :: g2) ca = Some s ->
        exists n', n' <= n /\ 
          (next_alt ca (run prog n') = Some s \/ run prog n' g2 ca = Some s).
  Proof.
    induction n.
      exists 0; auto.
    destruct g1 as [|hd g1]; simpl.
      exists n; auto.
    (* g1 is not empty: hd::g1 *)
    destruct hd.
      (* hd is a cut *)
      intros.
      apply IHn in H as [?[?[]]].
      exists x; auto.
      exists x; auto.
    (*hd is call*)
    destruct (prog n0) eqn:PP.
      unfold more_alt; simpl.
      exists n; auto.
    simpl.
    unfold save_alt; simpl.
    (* Search ((_++_)++_). *)
    intros.
    rewrite catA in H.
  Abort.

  Lemma starts_with_cut {n s}:
    forall g2 ca a,  
      run prog n (Goal cut ca :: g2) a = Some s ->
        exists n', n' <= n /\ 
          (run prog n' g2 ca = Some s).
  Proof.
    induction n.
      by[].
    now exists n; auto.
  Qed.

  Lemma starts_with_call {n s}:
    forall p g2 ca a,
      run prog n (Goal (call p) ca :: g2) a = Some s ->
        exists n', n' <= n /\ 
          (next_alt (more_alt a (prog p) g2) (run prog n') = Some s).
  Proof.
    induction n.
      now by [].
    exists n; auto.
  Qed.

  (* Lemma add_cut_change_nothing:
    run prog n2 cut (alt1 ++ aft) = Some alt2 ->
      exists n3 : nat, run prog n3 [::] (alt1 ++ cut :: aft) = Some alt2. *)


  Inductive split_cut : list alt -> list alt -> alt -> list alt -> Prop :=
    | split_cut_lst hd tl : goal_has_cut hd -> split_cut (hd::tl) [::] hd tl
    | split_cut_not hd tl : forall bef cut aft,
      not (goal_has_cut hd) -> split_cut tl bef cut aft ->
        split_cut (hd::tl) (hd::bef) cut aft.

  Lemma split_cut_app:
    forall l bef cut aft,
      split_cut l bef cut aft -> (l = bef ++ cut :: aft).
  Proof.
    (* constructor. *)
    induction 1; intros; auto; simpl; f_equal; auto.
  Qed.

  Lemma fail_or_succeed {n1 n2}:
    forall l bef cut aft alt1 alt2,
      split_cut l bef cut aft ->
        next_alt bef (run prog n1) = Some alt1 ->
          next_alt (more_alt (alt1++cut::aft) [::] [::]) (run prog n2) = Some alt2 ->
            exists n3, next_alt (more_alt l [::] [::]) (run prog n3) = Some alt2.
  Proof.
    revert n2.
    induction n1 as [|n1]; destruct bef as [|bef befs]; try by [].
    destruct bef as [|b bs]; simpl.
      (*bef = [::]; befs = any; alt1 = befs *)
      intros cut aft alt1 alt2 HSplit.
      inversion HSplit.
      apply split_cut_app in HSplit as HSplitCat; subst.
      inversion HSplitCat; subst; clear HSplitCat.
      inversion 1.
      simpl.
      exists 4; simpl.
  Abort.

  Lemma fail_or_succeed {n1 n2 s} r:
    forall g1 g2 ca,
      (for_all (fun x => match x with Goal g _ => g <> cut end) g1) ->
      run prog n1 g1 ca = Some (s ++ ca) ->
          run prog n2 g2 (s ++ ca) = r ->
            exists n3, 
              run prog n3 (g1 ++ g2) ca = r.
  Proof.
    revert s n2.
    induction n1.
      inversion 2.
    destruct g1; simpl.
      destruct s; simpl; inversion 2.
      exists n2; auto.
      admit.
    destruct 1 as [DIFF_CUT_HD DIFF_CUT_TL].
    destruct g as [[]?].
      by [].
    destruct (prog n) eqn:PP.
      unfold more_alt, save_alt; simpl.
      destruct ca.
        inversion 1.
      simpl.
      rewrite <-cat_rcons.
      intros.
      epose proof (IHn1 _ _ _ _ _ _ H H0).
      intros.
      inversion H0.
      admit.
    simpl.
      intros.
  Abort.

  (* Lemma starts_with_call {n s}:
    forall p g2 ca a hd tl,
      run prog n (Goal (call p) ca :: g2) a = Some s ->
        prog p = (hd::tl) ->
          exists n', n' <= n /\ 
            (next_alt (more_alt a (prog p) gs) (run prog n)).
  Proof.
    induction n.
      inversion 1.
    simpl.
    exists n; auto.
    rewrite H0 in H.
    unfold more_alt in H.
    simpl in H.
    auto.
  Abort. *)

  Lemma with_cut l:
    exists_ (eq^~ cut) l -> exists bef aft, (for_all (fun x => x <> cut) bef) /\ bef ++ cut :: aft = l.
  Proof.
    induction l; inversion 1; subst.
      exists [::], l; simpl; auto.
    apply IHl in H0 as [?[?[]]]; subst.
    destruct a.
    exists [::], (x++cut::x0); constructor; simpl; auto.
    exists (call n::x), x0; simpl; repeat constructor; auto.
    easy.
  Qed.

  Lemma succeed_or_fail {n1 bef aft l0 gs l1}:
    all_pred_have_cut ((bef ++ cut :: aft) :: l0) ->
      for_all (fun x : pred => x <> cut) bef ->
        run prog n1 (save_alt [::] (bef ++ cut :: aft) (not_alt_goal gs))
          [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] = Some l1 ->
        exists n2, 
          (run prog n2 (save_alt [::] (bef ++ cut :: aft) (not_alt_goal gs)) [::] = Some l1)
            \/
          (next_alt [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] (run prog n2) = Some l1).
  Proof.
    revert bef aft l0 gs l1.
    induction n1.
      by [].
    simpl.
    destruct bef; simpl.
      exists n1.+1; auto.
    destruct p.
      inversion 2; by [].
    unfold more_alt, save_alt; simpl.
    destruct (prog n); simpl.
      admit.
    destruct l; simpl.
  Admitted.

  Lemma xx {l0 l1 x gs}:
    for_all (exists_ (eq^~ cut)) l0 ->
      next_alt [seq save_alt [::] b gs  | b <- l0] (run prog x) = Some l1 -> 
        exists n0 g, run prog n0 (not_alt_goal g) [::] = Some l1.
  Proof.
    revert l0 l1 gs.
    induction x; destruct l0 as [|hd tl]; try by [].
    destruct hd as [|hd1 hds].
      now inversion 1.
    destruct hd1 as [|p].
      (* simpl.
      intros.
      destruct H.
      epose proof (IHx (hds::tl) _ gs _ _) as [?[]].
      exists x0,x1; apply H2.
      Unshelve.
      3:{
        simpl.
        unfold save_alt.
        admit.
      }
      2:{
        
      } *)
        admit.
    simpl.
    destruct 1 as [[]?].
      by [].
    destruct (prog p) eqn:PP.
      unfold more_alt, save_alt; simpl.
      intros.
      eapply (IHx _ _ _ H0) in H1 as [?[]].
      exists x0, x1; auto.
    simpl.
    (* pose [seq save_alt [::] b (not_alt_goal gs)  | b <- tl] as T.
    fold T.
    pose ([seq Goal x0 [::]  | x0 <- hds] ++ not_alt_goal gs) as R.
    fold R.
    pose proof (CProg p).
    rewrite PP in H1.
    inversion H1.
    destruct l.
      by [].
    unfold save_alt; simpl.
    epose proof (IHx ((p0 :: l) :: l0) _ ) as TTT; simpl in TTT.
    unfold save_alt in TTT.
    simpl in TTT.

    fold T R in TTT. *)
Admitted.

  Lemma bah1 {n l l0 gs l1}:
    all_pred_have_cut (l :: l0) ->
      run prog n (save_alt [::] l (not_alt_goal gs))
        [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] = Some l1 ->
          exists g n, run prog n (not_alt_goal g) [::] = Some l1.
  Proof.
    intro.
    inversion H.
    apply with_cut in H0 as [bef[aft [N_CUT <-]]].
    intros.
    epose proof (succeed_or_fail H N_CUT H0) as [?[]].
      unfold save_alt in H2.
      rewrite <-map_cat in H2.
      exists ((bef ++ cut :: aft) ++ gs), x; auto.

    eapply xx in H2.
    destruct H2 as [?[]].
    exists x1, x0; auto.
    auto.
  Abort.

  Inductive valid_tl : seq (seq pred) -> seq alt -> Prop :=
    | valid_tl_base ff gs l0 : valid_tl [::] [seq save_alt ff b [seq Goal x ff  | x <- gs]  | b <- l0]
    | valid_tl_recu l0 l2 R bef: 
          valid_tl bef l2 -> 
            valid_tl l0 ([seq save_alt l2 b R | b <- l0] ++ l2).

  Lemma bah12 {n T R LOC_HD LOC_TL res A}:
    all_pred_have_cut (LOC_HD :: LOC_TL) ->
      valid_tl LOC_TL A ->
        run prog n (save_alt T LOC_HD R) A = Some res ->
        (* run prog n (save_alt ff l [seq Goal x ff | x <- gs])
          [seq save_alt ff b [seq Goal x ff | x <- gs]  | b <- l0] = Some res -> *)
            exists g n', n' <= n /\ run prog n' (save_alt T g R) T = Some res.
  Proof.
    revert LOC_HD LOC_TL T R res A.
    induction n.
      by [].
    simpl.
    unfold save_alt.
    destruct LOC_HD as [|LOC_HD l0s]; simpl.
      destruct R; now inversion 1.
    destruct LOC_HD as [|p].
      intros.
      exists l0s, n; auto.
    destruct (prog p) eqn:PP.
      unfold more_alt; simpl.
      destruct A as [|a A]; simpl.
        by [].
      inversion 2; subst.
  Abort.

  Inductive help : _ -> _ -> Prop :=
    (* | base A G GS : help ([::]) (more_alt A G GS) *)
    | hhhh A G GS G0 G0s PP:
      help (more_alt A G GS) (more_alt ([seq [seq Goal x A  | x <- b] ++ GS  | b <- G0s] ++ A) PP
([seq Goal x A  | x <- G0] ++ GS))
    (* | recu GS G AA BB l0 L' a b : 
      (* help a b -> *)
      help (([seq save_alt GS b [seq Goal x a | x <- G] | b <- ((AA::BB)::l0)] ++ GS))
        (([seq save_alt ([seq save_alt GS b G | b <- l0] ++ GS) b1 ([seq Goal x GS | x <- BB] ++ G) | b1 <- L']
      ++ [seq save_alt GS b G | b <- l0] ++ GS)). *)
      .

  Lemma invariant_next_alt {n l1 A G GS}:
    (* all_pred_have_cut (alts) ->
      all_goals_have_cut ff -> *)
        next_alt (more_alt A G GS) (run prog n) = Some l1 ->
          False.
  Proof.
    remember (more_alt A G GS).
    (* l = [seq save_alt A b GS  | b <- G] ++ A *)
    destruct G as [|G0 G0s] eqn:LL; simpl.
      admit.
    rewrite Heql.
    unfold more_alt.
    destruct n; simpl.
      by [].
    destruct G0; unfold save_alt; simpl.
      admit.
    destruct p; [admit|].
    unfold more_alt.
    destruct (prog n0); [admit|].

    assert (exists x, help (x) (([seq save_alt ([seq [seq Goal x A  | x <- b0] ++ GS  | b0 <- G0s] ++ A) b
([seq Goal x A  | x <- G0] ++ GS)
 | b <- l0 :: l2] ++ [seq [seq Goal x A  | x <- b] ++ GS  | b <- G0s] ++ A))).
    eexists; constructor.
    clear H.

    (* next_alt (save_alt GS l G :: ([seq save_alt GS b G | b <- l0] ++ GS)) (run prog n) = Some l1 -> False *)
    simpl map.
    simpl.
    destruct l0 as [|AA BB]; [admit|].
    unfold save_alt at 1; simpl.
    destruct n; simpl.
      by[].
    destruct AA; [admit|].

    assert (exists x, help x (more_alt
([seq save_alt ([seq [seq Goal x A  | x <- b0] ++ GS  | b0 <- G0s] ++ A) b
([seq Goal x A  | x <- G0] ++ GS)
 | b <- l2] ++ [seq [seq Goal x A  | x <- b] ++ GS  | b <- G0s] ++ A) (prog n1)
([seq Goal x ([seq [seq Goal x0 A  | x0 <- b] ++ GS  | b <- G0s] ++ A)  | x <- BB] ++
[seq Goal x A  | x <- G0] ++ GS))).

    eexists.
    constructor.
    Abort.

  (* Lemma bah12 {n T R LOC_HD LOC_TL res A}:
    all_pred_have_cut (LOC_HD :: LOC_TL) ->
      valid_tl LOC_TL A ->
        run prog n (save_alt T LOC_HD R) A = Some res ->
        (* run prog n (save_alt ff l [seq Goal x ff | x <- gs])
          [seq save_alt ff b [seq Goal x ff | x <- gs]  | b <- l0] = Some res -> *)
            exists g n', n' <= n /\ run prog n' (save_alt T g R) T = Some res.
  Proof.
    revert LOC_HD LOC_TL T R res A.
    induction n.
      by [].
    simpl.
    unfold save_alt.
    destruct LOC_HD as [|LOC_HD l0s]; simpl.
      destruct R; now inversion 1.
    destruct LOC_HD as [|p].
      intros.
      exists l0s, n; auto.
    destruct (prog p) eqn:PP.
      unfold more_alt; simpl.
      destruct A as [|a A]; simpl.
        by [].
      inversion 2; subst.
  Admitted. *)


  Lemma bah1 {n g alts gs l1 ff}:
    all_pred_have_cut (g :: alts) ->
      all_goals_have_cut ff ->
      run prog n (save_alt ff g [seq Goal x ff | x <- gs])
        [seq save_alt ff b [seq Goal x ff | x <- gs]  | b <- alts] = Some l1 ->
          exists g n', n' <= n /\ run prog n' [seq Goal x ff | x <- g] ff = Some l1.
  Proof.
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

    revert g alts gs l1 ff.
    induction n.
      by [].
    simpl.
    unfold save_alt.
    destruct g.
      now inversion 1.
    simpl.
    destruct p.
      intros.
      exists (g++gs), n. rewrite <-map_cat in H1; auto.
    destruct (prog n0) eqn:PP.
      unfold more_alt; simpl.
      destruct alts.
        by [].
      simpl.
      inversion 1.
      intros.
      eapply IHn in H3 as [?[?[]]].
      exists x, x0; auto.
      all:auto.
    simpl.
    intros.
    rewrite <-map_cat in H1.
    rewrite map_cat_deep in H1.
    pose ([seq [seq Goal x ff  | x <- b ++ gs] | b <- alts]) as T; fold T in H1.
    pose ([seq Goal x ff  | x <- g++gs]) as R; fold R in H1.
    
    (* Se solo riuscissi a risolvere questo... *)

  Admitted.

  Lemma bah {n l l0 gs l1}:
    all_pred_have_cut (l :: l0) ->
      run prog n (save_alt [::] l (not_alt_goal gs))
        [seq save_alt [::] b (not_alt_goal gs)  | b <- l0] = Some l1 ->
          exists g, run prog n (not_alt_goal g) [::] = Some l1.
  Proof.
    (* intros.
    assert (all_goals_have_cut [::]).
    constructor.
    epose proof (bah1 H H1 H0) as (?&?&?&?).
    apply (pumping_leq _ _ _ _ _ _ H2) in H3.
    exists x; auto. *)
    revert l l0 gs l1.
    induction n; try by [].
    destruct l; unfold save_alt; simpl.
      inversion 1; by [].
    destruct p; intros l0 gs l1; rewrite <-map_cat.
      exists (cut :: l ++ gs); simpl; auto.
    destruct (prog n0) eqn:PP; simpl.
      unfold more_alt.
      destruct l; inversion 1.
        inversion H0; by [].
      destruct l0; try by [].
      simpl.
      unfold save_alt in IHn.
      intro.
      eapply IHn in H2 as []; auto.
      (* if the goal is (p, !) and p fails then go to the choice point *)
      exists (cut :: x); simpl; auto.
      repeat rewrite map_cat_deep.
      pose ([seq [seq Goal x [::]  | x <- b ++ gs]  | b <- l0]) as T1; fold T1.
      pose ([seq Goal x [::]  | x <- l ++ gs]) as T2; fold T2.

      (*qui è difficile...*)
  Admitted.

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
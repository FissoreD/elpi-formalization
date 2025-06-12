From mathcomp Require Import all_ssreflect.
From det Require Import det2.

Lemma run_consistent_res {a b c1 c2 r1 r2}:
  run a b c1 r1 -> run a b c2 r2 -> c1 = c2.
Proof. by move=> H H1; apply (proj1 (run_consistent H H1)). Qed.

Lemma run_consistent_state {a b c1 c2 r1 r2}:
    run a b c1 r1 -> run a b c2 r2 -> (c1 <> Failed ->  r1 = r2).
Proof. by move=> H H1; apply (proj2 (run_consistent H H1)). Qed.

Lemma not_cut_brothers_cut {s A B}:
  not_cut_brothers s A -> expand s A = CutBrothers B -> False.
Proof. by move=> H; elim: H B; congruence. Qed.

Lemma run_CutBrothers_id {s2 s3 st1 st2 ir1 ir2}:
  expand s3 st1 = CutBrothers st2 -> 
  run s3 st2 (Done s2) ir1 -> 
  run s3 st1 (Done s2) ir2 ->
  ir1 = ir2.
Proof.
  move: s2 s3 st2 ir1 ir2.
  case: st1 => //=.
  + move=> pr [] //=.
    - move=> ????? [] <- H => //= H1.
      apply run_cut_simpl in H1 as []; subst; by inversion H.
    - move=> [] pn args s2 s3 st2 ir1 ir2 => //=; by case F: F => [|[]] //=.
  + move=> st0  [] s st1 s2 s3 st2 ir1 ir2; by case: expand; case: expand => //.
  + move=> st0 st1 s2 s3 st2 ir1 ir2 + + H.
    move: (run_and_complete H) => [il [ir [s'' [?[HL HR]]]]]; subst.
    case E: expand => //; inversion HL; try congruence; subst.
    + move: E; rewrite H0 => -[] ? [] ? H2; subst.
      move: (run_and_complete H2) => [il2 [ir2 [s'''[?[HL' HR']]]]]; subst.
      move: (run_consistent H1 HL') => [][] ? /(_ done_fail) ?; subst.
      by move: (run_consistent HR HR') => [] _ /(_ done_fail) ?; subst.
    + move: E; rewrite H3 => -[]?; subst.
      case F: expand => //= -[] ? H1; subst.
      move: (run_and_complete H1) => [il1 [ir2 [s''1 [?[HL1 HR1]]]]] {H1}; subst.
      move: (run_consistent HL1 HL) => [][] ? /(_ done_fail) ?; subst.
      inversion HR; try congruence; subst.
      move: H0; rewrite F => -[] ?; subst.
      by move: (run_consistent HR1 H1) => [] _ /(_ done_fail) ?; subst.
Qed.


Lemma not_cut_brothers_split {s A B sol st}:
  not_cut_brothers s (And A B) ->
    not_cut_brothers s A /\ (run s A (Done sol) st -> not_cut_brothers sol B).
Proof.
  remember (And _ _) as NA eqn:HNA.
  move=> H.
  move: A B sol st HNA.
  elim: H; clear.
  + move=> sol s ? H A B sol1 A' ?; subst.
    move: H => //=.
    case E: expand => //=.
    case F: expand => //= -[] ?; subst.
    split.
      - by apply: not_cut_brothers_solved E.
      - by move=> H1; destruct (run_Solved_id E H1); subst; apply: not_cut_brothers_solved F.
  + move=> s g + A B sol A' ?; subst => //=.
    case E: expand => //=.
    - move=> _; split.
      by apply: not_cut_brothers_failure.
      by move=> H; destruct (run_Failure_and_Done E H).
    - case F: expand => //=.
      move=> _; split.
      by apply: not_cut_brothers_solved E.
      move=> H; destruct (run_Solved_id E H); subst.
      by apply: not_cut_brothers_failure.
  + move=> s g g' + H1 IH A B sol A' ?; subst => //=.
    case E: expand => [|||sol'] //=.
    - move=> [] ?; subst.
      move: IH => /(_ _ _ sol A' erefl) [] H2 H3; split.
      - by apply: not_cut_brothers_expanded E H2.
      - by move=> H; apply H3; inversion H; subst; clear H; congruence.
    - case F: expand => [A''|||] //= -[] ?; subst.
      split.
      - by apply: not_cut_brothers_solved E.
      - move=> H.
        destruct (run_Solved_id E H); subst.
        move: IH => /(_ _ _ sol' A' erefl) => -[] H2 H3. 
        by apply: not_cut_brothers_expanded F (H3 H).
Qed.

Lemma run_cut_cut s B SOL X:
  run s (cut B) (Done SOL) X ->
    exists Y, run s B (Done SOL) Y.
Proof.
  remember (cut _) as CUT eqn:HCUT.
  remember (Done _) as D eqn:HD.
  move=> H.
  move: B SOL HCUT HD.
  elim: H; clear => //=.
  + move=> A ? ? H B SOL ? [] ?; subst.
    move: A SOL H.
Abort.

Lemma chooseB_split s A B C: chooseB s A B C -> C = B \/ C = cut B.
Proof. by move=> H; elim: H; auto. Qed.

Lemma chooseBP1 {s A X}:
  not_cut_brothers s A ->
    chooseB s A X X.
Proof.
  move=> H.
  elim: H X; clear.
  by move=> ??? H ?; apply: chooseB_Done H.
  by move=> ?? H ?; apply: chooseB_Fail H.
  by move=> ??? H H1 IH ?; apply: chooseB_Exp H (IH _).
Qed.

Lemma run_no_cut_failure_run {s A B}:
  run_no_cut_failure s A B -> run s A Failed B.
Proof.
  move=> H; elim: H; clear.
  + by constructor.
  + by move=> s A st1 B H H1 H2; apply: run_step H H2.
Qed.

Corollary run_or_fail1 s1 g1 g2 st:
  run s1 (Or g1 (s1,g2)) Failed st ->
    run s1 g1 Failed st /\ (not_cut_brothers s1 g1 -> run s1 g2 Failed st).
Proof. move=> H. apply: run_or_fail H. Qed. 

Lemma not_cut_brothers_choosB {s A B C}:
  chooseB s A B C ->
    not_cut_brothers s A ->
      C = B.
Proof.
  move=> H.
  elim: H => //=; clear.
  by move=> s A C B + H; inversion H; subst => //=; congruence.
  move=> s A A' B B' + H IH H1.
  inversion H1; subst; clear H1; try congruence.
  rewrite H0 => -[] ?; subst.
  auto.
Qed.

Lemma chooseB_expanded_and_left {s A B X Y ss}:
  chooseB s (And A B) X Y ->
    expand s A = Expanded ss ->
      chooseB s (And ss B) X Y.
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss.
  elim: H; clear => //=.
  by move=> s A B C + A1 B1 ?? H; subst => //=; rewrite H.
  by move=> ??? + ???? H; subst => //=; rewrite H.
  by move=> ???? + ???? H; subst => //=; rewrite H.
  by move=> s A A' B B' + HC IH A0 B0 ? ? H; subst => //=; rewrite H => -[] ?; subst.
Qed.

Lemma chooseB_expanded_and_right {s A B B2 X Y ss}:
  chooseB s (And A B) X Y ->
    expand s A = Solved ss ->
      expand ss B = Expanded B2 ->
        chooseB s (And A B2) X Y.
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B B2 HAnd ss.
  case: H; clear => //=.
  by move=> s A B C + ????? H H1; subst => //=; rewrite H H1.
  by move=> ??? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ???? + ????? H H1; subst => //=; rewrite H H1.
  by move=> s A A' B B' + HC ????? H H1; subst => //=; rewrite H H1 => -[] ?; subst.
Qed.

Lemma not_cut_borothers_expanded_and_left {s A B ss}:
  not_cut_brothers s (And A B) ->
    expand s A = Expanded ss ->
      not_cut_brothers s (And ss B).
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss.
  case: H; clear => //=.
  by move=> ??? + ???? H; subst => //=; rewrite H.
  by move=> ?? + ???? H; subst => //=; rewrite H.
  by move=> ??? + H1 ???? H2; subst => //=; rewrite H2 => -[] ?; subst; auto.
Qed.

Lemma not_cut_borothers_expanded_and_right {s A B B'' ss}:
  not_cut_brothers s (And A B) ->
    expand s A = Solved ss ->
    expand ss B = Expanded B'' ->
      not_cut_brothers s (And A B'').
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss B''.
  case: H; clear => //=.
  by move=> ??? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ?? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ??? + H1 H2 ???? H3 H4; subst => //=; rewrite H3 H4 => -[] ?; subst; auto.
Qed.

Lemma p_aorb_andc {sA sB sD A B C D E}:
  run sA (And (Or A (sB, B)) C) (Done sD) D ->
    run sA (And A C) Failed E ->
      exists D', run sB (And B C) (Done sD) D'.
Proof.
  move=> H H1.
  move: (run_and_complete H) => [il[ir[s'' [?[HAORB HC]]]]] {H}; subst.
  move: (run_or_complete HAORB) => [] {HAORB}.
    + move=> [A' [B' [HChA [? HA]]]]; subst.
      move: (run_and_fail H1) => {H1} [HA'|].
      + by move: (run_consistent HA HA') => [].
      + move=> [s [st [HA' HC']]].
        move: (run_consistent HA HA') => [[?]] /(_ done_fail) ?; subst.
        by move: (run_consistent HC HC') => [].
    + move=> [A' [B' [HA [? HB]]]]; subst.
      exists (And B' ir).
      apply: run_and_correct HB HC.
Qed.

(* ((A ∧ B) ∨ (A ∧ C)) -> (A ∧ (B ∨ C)) *)
Lemma or_is_distributive {A B C s sol E}:
    run s (Or (And A B) (s, (And A C))) (Done sol) E ->
      not_cut_brothers s (And A B) ->
        exists E' s' IGN, run s A (Done s') IGN /\
          run s (And A (Or B (s', C))) (Done sol) E' .
Proof.
  move=> H H1.
  apply run_or_complete in H as [[A' [B' [H [? H0]]]]|[A' [C' [H [? H0]]]]]; subst.
  (* left succeeds *)
  + move: (run_and_complete H0) => [il[ir[s'' [?[HA HB]]]]] {H}; subst.
    move: (chooseB_complete s'' B C) => [] ? HC.
    do 3 eexists; repeat split.
    + apply HA.
    + apply: run_and_correct HA _.
    + apply: run_or_correct; left; split; [apply HC|eassumption].
  (* right succeeds *)
  + move: (run_and_complete H0) => [il[ir[s'' [?[HA HC]]]]] {H0}; subst.
    move: (run_and_fail (run_run_no_cut_failure H)) => [H0|].
    + by move: (run_consistent H0 HA) => [].
    + move=> [s1 [s2 [HA' HB]]].
      move: (run_consistent HA HA') => [] [] ? /(_ done_fail) ?; subst.
      move: (run_no_cut_failure_split H) => [].
      + by move=> []? H2; move: (run_consistent (run_run_no_cut_failure H2) HA') => [].
        move=> [s' [X [H2 H3]]]; move: (run_expand_all_solved H2 HA') => ?; subst.
        do 3 eexists; split.
        + apply HA.
        + apply: run_and_correct HA _.
        + apply: run_or_correct; right; split; [apply H3|eassumption].
Qed.

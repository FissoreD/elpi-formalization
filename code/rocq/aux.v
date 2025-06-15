From mathcomp Require Import all_ssreflect.
From det Require Import det.

Lemma run_consistent_res {a b c1 c2}:
  run a b c1 -> run a b c2 -> c1 = c2.
Proof. by move=> H H1; apply ((run_consistent H H1)). Qed.

(* Corollary run_or_fail1 s1 g1 g2 b:
  run s1 (Or g1 s1 g2) Failed ->
    run s1 g1 Failed /\ (run_classic s1 g1 b -> run s1 g2 Failed).
Proof. move=> H. apply: run_or_fail H. Qed.  *)

(* Lemma not_cut_borothers_expanded_and_left {s A B ss}:
  run_classic s (And A B) ->
    expand s A = Expanded ss ->
      run_classic s (And ss B).
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss.
  case: H; clear => //=.
  by move=> ???? + ???? H; subst => //=; rewrite H.
  by move=> ?? + ???? H; subst => //=; rewrite H.
  by move=> ??? + H1 ???? H2; subst => //=; rewrite H2 => -[] ?; subst; auto.
Qed.

Lemma not_cut_borothers_expanded_and_right {s A B B'' ss altA}:
  run_classic s (And A B) ->
    expand s A = Solved ss altA ->
    expand ss B = Expanded B'' ->
      run_classic s (And A B'').
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss B''.
  case: H; clear => //=.
  by move=> ???? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ?? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ??? + H1 H2 ???? H3 H4; subst => //=; rewrite H3 H4 => -[] ?; subst; auto.
Qed. *)

Lemma p_aorb_andc {sA sB sD A B C alts}:
  run sA (And (Or A sB B) C) (Done sD alts) ->
    run sA (And A C) Failed ->
      exists alts, run sB (And B C) (Done sD alts).
Proof.
  move=> H H1.
  move: (run_and_complete H) => [s'' [altL [altR [? [HAORB HC]]]]] {H}; subst.
  move: (run_or_complete HAORB) => [].
    + move=> [altA HA]; move: (run_and_fail H1) => [].
      + move=> HA'; move: (run_consistent HA HA'); by [].
      + move=> [X [altA0 [HA' HC']]].
        move: (run_consistent HA HA') => [] ?; subst.
        by move: (run_consistent HC HC').
    + move=> [] alts [] HA HB.
      eexists; apply: run_and_correct HB HC.
Qed.

(* ((A ∧ B) ∨ (A ∧ C)) -> (A ∧ (B ∨ C)) *)
Lemma or_is_distributive {A B C s sol alts b}:
    run s (Or (And A B) s (And A C)) (Done sol alts) ->
      run_classic s (And A B) b ->
        exists s' altA altABC, run s A (Done s' altA) /\
          run s (And A (Or B s' C)) (Done sol altABC) .
Proof.
  move=> H H1.
  move: (run_or_complete H) => [].
  (* left succeeds *)
  + move=> [altAB HAB].
    move: (run_and_complete HAB) => [s'' [? [? [? [HA HB]]]]] {H}; subst.
    move: (run_or_correct_left HB s'' C) => [altB H].
    repeat eexists; [apply: HA|].
    apply: run_and_correct (HA) H.
  (* right succeeds *)
  + move=> [] altB [] EAB HAC; move: (run_and_complete HAC) => [s'' [?[?[?[HA HC]]]]] {HAC}; subst.
    move: (run_and_fail (run_run_classic_failure EAB)) => [H0|].
    + by move: (run_consistent H0 HA).
    + move=> [s1 [altA [HA' HB]]].
      move: (run_consistent HA HA') => [] ??; subst.
      move: (run_classic_failure_split EAB) => [].
      + by move=> H2; move: (run_consistent (run_run_classic_failure H2) HA').
      + move=> [s' [altA0 [H2 H3]]].
        (* move: (run_expand_all_solved H2 HA') => ?; subst. *)
        move: (run_or_correct_right H3 HC) => {}H.
        move: (run_consistent HA H2) => []?; subst.
        repeat eexists.
        + apply HA.
        + apply: run_and_correct H2 H.
Qed.

Lemma expand_cut_result {s A r}:
  expand s (cut A) = r -> (exists B, r = Expanded B) \/ r = Failure.
Proof.
  elim: A s r => //=; auto.
  + move=> A IH a A' HA' s r //=.
    case H: expand => //=.
    + by move=>?; subst; left; eexists.
    + by move=>?; subst; left; eexists.
    + case X: expand => //=?; subst; auto.
      + by left; eexists.
      + by left; eexists.
      + apply: HA' X.
    + apply IH in H as [[]|?] => //=.
  + move=> s1 IH1 s2 IH2 s3 r.
    case H: expand => ?; subst; auto.
    + by left; eexists.
    + apply IH1 in H as [[]|?] => //=.
    + apply IH1 in H as [[]|?] => //=.
Qed.

From mathcomp Require Import all_ssreflect.
From det Require Import det.

Lemma run_consistent_res {a b c1 c2 r1 r2}:
  run a b c1 r1 -> run a b c2 r2 -> c1 = c2.
Proof. by move=> H H1; apply (proj1 (run_consistent H H1)). Qed.

Lemma run_consistent_state {a b c1 c2 r1 r2}:
    run a b c1 r1 -> run a b c2 r2 -> (c1 <> Failed ->  r1 = r2).
Proof. by move=> H H1; apply (proj2 (run_consistent H H1)). Qed.

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
  + by move=> st0  s st1 s2 s3 st2 ir1 ir2; by case: expand; case: expand => //.
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


Lemma expand_no_cut_split {s A B sol st}:
  expand_no_cut s (And A B) ->
    expand_no_cut s A /\ (run s A (Done sol) st -> expand_no_cut sol B).
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
      - by apply: expand_no_cut_solved E.
      - move=> H1; move: (run_Solved_id E H1) => [][]??; subst.
        apply: expand_no_cut_solved F.
  + move=> s g + A B sol A' ?; subst => //=.
    case E: expand => //=.
    - move=> _; split.
      by apply: expand_no_cut_failure1.
      by move=> H; destruct (run_Failure_and_Done E H).
    - case F: expand => //=.
      move=> _; split.
      by apply: expand_no_cut_solved E.
      move=> H; move: (run_Solved_id E H) => [][]??; subst.
      by apply: expand_no_cut_failure1.
  + move=> s g g' + H1 IH A B sol A' ?; subst => //=.
    case E: expand => [|||sol'] //=.
    - move=> [] ?; subst.
      move: IH => /(_ _ _ sol A' erefl) [] H2 H3; split.
      - by apply: expand_no_cut_expanded E H2.
      - by move=> H; apply H3; inversion H; subst; clear H; congruence.
    - case F: expand => [A''|||] //= -[] ?; subst.
      split.
      - by apply: expand_no_cut_solved E.
      - move=> H.
        move: (run_Solved_id E H)=> [][]??; subst.
        move: IH => /(_ _ _ sol' A' erefl) => -[] H2 H3. 
        by apply: expand_no_cut_expanded F (H3 H).
Qed.

Lemma expand_no_cut_failure_run {s A B}:
  expand_no_cut_failure s A B -> run s A Failed B.
Proof.
  move=> H; elim: H; clear.
  + by constructor.
  + by move=> s A st1 B H H1 H2; apply: run_step H H2.
Qed.

Corollary run_or_fail1 s1 g1 g2 st:
  run s1 (Or g1 s1 g2) Failed st ->
    run s1 g1 Failed st /\ (expand_no_cut s1 g1 -> run s1 g2 Failed st).
Proof. move=> H. apply: run_or_fail H. Qed. 

Lemma not_cut_borothers_expanded_and_left {s A B ss}:
  expand_no_cut s (And A B) ->
    expand s A = Expanded ss ->
      expand_no_cut s (And ss B).
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
  expand_no_cut s (And A B) ->
    expand s A = Solved ss ->
    expand ss B = Expanded B'' ->
      expand_no_cut s (And A B'').
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
  run sA (And (Or A sB B) C) (Done sD) D ->
    run sA (And A C) Failed E ->
      exists D', run sB (And B C) (Done sD) D'.
Proof.
  move=> H H1.
  move: (run_and_complete H) => [il[ir[s'' [?[HAORB HC]]]]] {H}; subst.
  move: (run_or_done HAORB) => [A' [B' ?]]; subst.
  move: (run_or_complete HAORB) => [].
    + move=> HA; move: (run_and_fail H1) => [HA'|].
      + move: (run_consistent HA HA') => []; by [].
      + move=> [X[Y [HA' HC']]].
        move: (run_consistent HA HA') => [] [] ? /(_ done_fail) ?; subst.
        by move: (run_consistent HC HC') => [].
    + move=> [] HA HB.
      exists (And B' ir).
      apply: run_and_correct HB HC.
Qed.

(* ((A ∧ B) ∨ (A ∧ C)) -> (A ∧ (B ∨ C)) *)
Lemma or_is_distributive {A B C s sol E}:
    run s (Or (And A B) s (And A C)) (Done sol) E ->
      expand_no_cut s (And A B) ->
        exists E' s' IGN, run s A (Done s') IGN /\
          run s (And A (Or B s' C)) (Done sol) E' .
Proof.
  move=> H H1.
  move: (run_or_done H) => [AB [AC ?]]; subst.
  move: (run_or_complete H) => [].
  (* left succeeds *)
  + move=> HAB. move: (run_and_done HAB) => [A' [B' ?]]; subst.
    move: (run_and_complete HAB) => [il[ir[s'' [+ [HA HB]]]]] {H} => -[]??; subst.
    move: (run_or_correct_left HB s'' C) => [] X H.
    do 3 eexists; split; [apply: HA|].
    apply: run_and_correct (HA) H.
  (* right succeeds *)
  + move=> [] EAB HAC; move: (run_and_complete HAC) => [il[ir[s'' [?[HA HC]]]]] {HAC}; subst.
    move: (run_and_fail (run_expand_no_cut_failure EAB)) => [H0|].
    + by move: (run_consistent H0 HA) => [].
    + move=> [s1 [s2 [HA' HB]]].
      move: (run_consistent HA HA') => [] [] ? /(_ done_fail) ?; subst.
      move: (expand_no_cut_failure_split EAB) => [].
      + by move=> []? H2; move: (run_consistent (run_expand_no_cut_failure H2) HA') => [].
        move=> [s' [X [H2 H3]]]; move: (run_expand_all_solved H2 HA') => ?; subst.
        move: (run_or_correct_right H3 HC) => [] p {}H.
        do 3 eexists; split.
        + apply HA.
        + apply: run_and_correct HA H.
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

Lemma run_or_done_cut1 {s1 s2 SOL A A' B B'}:
  run s1 (Or A s2 (cut B)) (Done SOL) (Or A' s2 B') -> B' = (cut B).
Proof.
  remember (Or A _ _) as O1 eqn:HO1.
  remember (Or A' _ _) as O2 eqn:HO2.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H s2 A A' B B' SOL HO1 HO2 HD; clear => //=.
  + by move=> s st s' H s2 A A' B B' SOL H1; rewrite H1 => -[] ?? [] ?; subst.
  + move=> s st st1 st2 r + H1 IH s2 A A' B B' SOL ???; subst => //=.
    by case E: expand => //=; case: expand => //=.
  + move=> s st s1 st2 r + H1 IH s2 A A' B B' SOL ???; subst => //=.
    case E: expand => //=.
    + by move=> []?; subst; apply: IH erefl erefl erefl.
    + by move=> []?; subst; apply: IH erefl erefl; rewrite cut_cut_same.
    + case F: expand => //=.
      + by move: (expand_cut_expanded F).
      + by move: (expand_cut_CB F).
Qed.
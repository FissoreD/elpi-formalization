From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module RunP (A: Unif).
  Module Run := Run(A).
  Import Run.

  Inductive expanded_classic : Sigma -> state -> run_res -> Prop :=
    | expandedc_done {s s' A alt}   : expand s A = Solved s' alt  -> expanded_classic s A (Done s' alt)
    | expandedc_fail {s A B}        : expand s A = Failure B -> expanded_classic s A (Failed B)
    | expandedc_step {s s' A B}     : expand s A = Expanded B  -> expanded_classic s B s' -> expanded_classic s A s'.

  Inductive run_classic : Sigma -> state -> run_res -> Prop :=
    | run_classic_done {s s' A B}        : expanded_classic s A (Done s' B) -> run_classic s A (Done s' B)
    | run_classic_fail {s A B}           : expanded_classic s A (Failed B) -> next_alt s B = None -> run_classic s A (Failed B)
    | run_classic_backtrack {s s' s'' A B C} : expanded_classic s A (Failed B) -> next_alt s B = Some (s', C) ->  run_classic s' C s'' -> run_classic s A s''.

  Lemma expanded_classic_expanded {s A r}:
    expanded_classic s A r -> expanded s A r.
  Proof.
    move=> H; elim: H.
    + by move=> ???? H; apply: expanded_done H.
    + by move=> ??? H; apply: expanded_fail H.
    + move=> ???? H _ H2; apply: expanded_step H H2.
  Qed.
  
  Lemma run_classic_run {s A r}:
    run_classic s A r -> run s A r.
  Proof.
    move=> H; elim: H.
    + move=> ???? H; apply: run_done (expanded_classic_expanded H).
    + move=> ??? H; apply: run_fail (expanded_classic_expanded H).
    + move=> ?????? H H1 H2; apply: run_backtrack (expanded_classic_expanded H) H1.
  Qed.

  Lemma run_classic_cut {s A B b}:
    run_classic s A b -> expand s A = CutBrothers B -> False.
  Proof. move=> H; elim: H B; inversion 1; congruence. Qed.

  Lemma run_Solved_id {s s1 A r alt}:
      expand s A = Solved s1 alt -> expanded s A r -> r = Done s1 alt.
  Proof.
    move=> + H; by case: H => //=; clear; congruence.
  Qed.

  Lemma expanded_Failure_and_Done {s s' A A' A''}:
    expand s A = Failure A' -> expanded s A (Done s' A'') -> False.
  Proof. inversion 2; subst; congruence. Qed.

  Lemma expanded_consistent: forall {s0 A s1 s2},
    expanded s0 A s1 -> expanded s0 A s2 -> s1 = s2.
  Proof.
    move=> s0 A s1 + H.
    elim:H; clear.
    + move=> s s' A alt H B H1.
      by move: (run_Solved_id H H1).
    + move=> s A B HA r H0.
      by inversion H0; congruence.
    + move=> s st st1 st2 + H1 IH B H2.
      inversion H2; subst; clear H2; try congruence; rewrite H0 => -[]?; subst; by auto.
    + move=> s st st1 st2 + H1 IH B H2.
      inversion H2; subst; clear H2; try congruence; rewrite H0 => -[]?; subst; by auto.
  Qed.

  Lemma run_consistent {s A r1 r2}:
    run s A r1 -> run s A r2 -> r1 = r2.
  Proof.
    move=> H; elim: H r2; clear.
    + move=> s s' A B H r2; inversion 1; subst; have:= expanded_consistent H H1; congruence.
    + move=> s A B HA HB r; inversion 1; subst; have:= expanded_consistent HA H1; congruence.
    + move=> ?????? H Hz ? IH ?; inversion 1; subst; have:= expanded_consistent H H1; try congruence.
      move=> [] /[subst1]; apply: IH.
      by move: H2; rewrite Hz => -[] /[subst2].
  Qed.

  Lemma simpl_next_alt_aux_and_none {s A B0 B}:
    next_alt_aux true s (And A B0 B) = None -> next_alt_aux true s B = None /\  next_alt_aux true s A = None.
  Proof. 
    rewrite /next_alt //=. 
    case X: next_alt_aux => [x|].
    + by case x.
    + case Y: next_alt_aux => [x|] //.
      + by case x.
  Qed.

  Lemma simpl_next_alt_and_some {s A B0 B r}:
    next_alt_aux true s (And A B0 B) = Some r -> 
    (exists s' B',  next_alt_aux true s B = Some (s', B') /\ r = (s', And A B0 B')) \/ 
      (exists s' A', next_alt_aux true s B = None /\  next_alt_aux true s A = Some (s', A') /\ r = (s', And A' B0 ((if B == cut B then B else B0)))).
  Proof.
    move=> //=; case X: next_alt_aux => [x|].
    + case: x X => S C H -[] /[subst1].
      by left; do 2 eexists.
    + case Y: next_alt_aux => [x|] //; case: x Y.
      move=> s' C H -[] /[subst1]; right.
      by do 2 eexists.
  Qed.

  Lemma expanded_cut_simpl {pr s2 s3 alt}:
    expanded s3 (Goal pr Cut) (Done s2 alt) -> alt = OK.
  Proof. by inversion 1; move: H1 => //= [] ?; subst; inversion H2; subst => //; move: H5 => [? ->]. Qed.

  Lemma expanded_classic_expandedR {s1 A B b}:
    expand s1 A = Expanded B -> 
      expanded_classic s1 A b ->
          expanded_classic s1 B b.
  Proof.
    move=> + H; elim: H B => //=; congruence.
  Qed.

  Lemma expand_cut_failure {s A}: expand s (cut A) = Failure (cut A).
  Proof.
    elim: A s => //=; clear.
    - by move => A IHl s1 B IHr s2; rewrite IHl.
    - by move => A IHl B IHr C IHc s; rewrite IHl.
  Qed.

  Lemma expand_cut_solved {s s' A B}: expand s (cut A) = Solved s' B -> False.
  Proof.
    elim: A s s' B => //; clear.
    + move=> A HA s B HB s1 s2 C /=.
      case X: expand => // -[] /[subst2]; by apply: HA X.
    + move=> A HA B HB C HC s s' D /=; case X: expand => // _.
      apply: HA X.
  Qed.

  Lemma expand_cut_cb {s A B}: expand s (cut A) = CutBrothers B -> exists B', B = cut B'.
  Proof.
    elim: A s B => //; clear.
    + move=> A HA s B HB s' C /=; case G: expand => //.
    + move=> A HA B HB C HC s D /=; case G: expand => //.
      + move=> [] /[subst1].
        move: (HA _ _ G) => [B'] /[subst1].
        exists (cut (And B' B C)) => /=.
        by rewrite 2!cut_cut_same.
      + by move: (expand_cut_solved G).
  Qed.

  Lemma expand_cut_expanded {s A B}: expand s (cut A) = Expanded B -> exists B', B = cut B'.
  Proof.
    elim: A s B => //; clear.
    + move=> A HA s B HB s' C /=; case G: expand => // -[] /[subst1].
      + by move: (HA _ _ G) => [X] /[subst1]; exists (Or X s B).
      + by move: (expand_cut_cb G) => [X] /[subst1]; exists (Or X s B); rewrite cut_cut_same.
    + move=> A HA B HB C HC s D /=; case G: expand => //.
      + move=> [] /[subst1].
        move: (HA _ _ G) => [B'] /[subst1].
        exists (cut (And B' B C)) => /=.
        by rewrite 2!cut_cut_same.
      + by move: (expand_cut_solved G).
  Qed.

  Axiom classic : forall P : Prop, P \/ ~ P.

  Lemma next_alt_cut {b s s' A B}: next_alt_aux b s (cut A) = Some (s', B) -> exists A, B = cut A.
  Proof.
    elim: A b B s s' => //=; clear.
    + move=> A IH s2 B IHB bool C s s'; rewrite /next_alt //=.
      case G: next_alt_aux => [x|].
      + case: x G => a b G -[] /[subst2].
        move: (IH _ _ _ _ G) => [] X ->.
        by exists (Or X s2 B).
      + by move=> [] /[subst2]; eexists.
    + move=> A HA B0 HB0 B HB bool C s s'; rewrite /next_alt /=.
      case G: next_alt_aux => [x|].
      + case: x G => s2 b HN [] /[subst2].
        move: (HB _ _ _ _ HN) => [B'] /[subst1].
        by exists (And A B0 B').
      + case H: next_alt_aux => [x|] //.
        case: x H => s2 A' NA -[] /[subst2].
        rewrite cut_cut_same eq_refl.
        move: (HA _ _ _ _ NA) => [A2] /[subst1] //.
        by exists (And A2 B0 B).
  Qed.

  Lemma expanded_cut_done {s s' A B}:
    expanded s (cut A) (Done s' B) -> False.
  Proof.
    remember (cut _) as CA eqn:HCA.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A B HCA HD => //; clear.
    + move=> s s' A B H s2 C D /[subst1] -[] /[subst2].
      apply: expand_cut_solved H.
    + move=> s s' A B HA HB IHA s2 C D /[subst2].
      move: (expand_cut_cb HA) => [A'] /[subst1].
      by apply: IHA erefl.
    + move=> s s' A B HA HB IH s2 C D /[subst2].
      move: (expand_cut_expanded HA) => [B'] /[subst1].
      by apply: IH.
  Qed.

  Lemma expanded_cut_fail {s A B}:
    expanded s (cut A) (Failed B) -> exists B', B = cut B'.
  Proof.
    remember (cut _) as CA eqn:HCA.
    remember (Failed _) as D eqn:HD => H.
    elim: H A B HCA HD => //; clear.
    + move=> s A B + C D /[subst1].
      rewrite expand_cut_failure => -[] /[subst1] -[] /[subst1].
      by eexists.
    + move=> s r A B HA HB IHA C D /[subst2].
      move: (expand_cut_cb HA) => [A'] /[subst1].
      by apply: IHA erefl.
    + move=> s r A B HA HB IH C D /[subst2].
      move: (expand_cut_expanded HA) => [B'] /[subst1].
      by apply: IH.
  Qed.

  Lemma run_cut_fail {s s' A altA} :
    run s (cut A) (Done s' altA) -> False.
  Proof.
    remember (cut _) as CA eqn:HCA.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A altA HCA HD => //=; clear.
    + move=> s s' ? B HA s2 AC B' /[subst1] -[] /[subst2].
      apply: expanded_cut_done HA.
    + move=> s s1 r A B C + + HR IH s' D E /[subst2].
      move=> /expanded_cut_fail [B'] /[subst1].
      move=> /next_alt_cut [] ? /[subst1].
      by apply: IH.
  Qed.

  Lemma expand_flow {s s1 s2 A B C}: expand s A = Solved s1 B -> expand s B = Solved s2 C -> B = C /\ s1 = s2.
  Proof.
    elim: A s s1 s2 B C; clear => //.
    + by move=> s s1 s2 B C [] /[subst2] -[] /[subst2].
    + by move=> s s1 s2 B C [] /[subst2] -[] /[subst2].
    + by move=> p [].
    + move=> A HA s B HB s1 s2 s3 C D /simpl_expand_or_solved [E [HE]] /[subst1].
      move=> /simpl_expand_or_solved [F [HF]] /[subst1].
      by have := (HA _ _ _ _ _ HE HF) => -[] /[subst2].
    + move=> A HA B0 HB0 B HB s1 s2 s3 C D /simpl_expand_and_solved [s4 [E [F [HE [HF]]]]] /[subst1].
      move=> /simpl_expand_and_solved [s5 [G [H [HG [HH]]]]] /[subst1].
      have:= (HA _ _ _ _ _ HE HG) => -[] /[subst2].
      by have:= (HB _ _ _ _ _ HF HH) => -[] /[subst2].
  Qed.

  Lemma expand_flow_cut {s s1 A B C}: expand s A = Solved s1 B -> expand s B = CutBrothers C -> B = C.
  Proof.
    elim: A s s1 B C; clear => //.
    + move=> s s1 B C [] /[subst2] //.
    + move=> s s1 B C [] /[subst2] //.
    + by move=> p [].
    + move=> A HA s B HB s1 s2 C D /simpl_expand_or_solved [E [HE]] /[subst1].
      by move=> /simpl_expand_or_cut.
    + move=> A HA B0 HB0 B HB s1 s2 C D /simpl_expand_and_solved [s4 [E [F [HE [HF]]]]] /[subst1].
      move=> /simpl_expand_and_cut [].
      + move=> [G [HG]] /[subst1].
        by have:= (HA _ _ _ _ HE HG) => /[subst1].
      + move=> [s5 [G [H [HG [HH]]]]] /[subst1].
        have := expand_flow HE HG => -[] /[subst2].
        by have:= (HB _ _ _ _ HF HH) => /[subst1].
  Qed.

  Lemma expand_solved_cut {s s1 A} : expand s A = Solved s1 (cut A) -> False.
  Proof.
    elim: A s s1 => //.
    + move=> p [] //.
    + move=> A HA s B HB s1 s2 /simpl_expand_or_solved [C [HC]] [] /[subst2].
      apply: HA HC.
    + move=> A HA B HB C HC s1 s2 /simpl_expand_and_solved [s3[D[E[HD[HE]]]]] [] /[subst2].
      apply: HA HD.
  Qed.

  Lemma expanded_cut1 {s1 s2 A}: expanded s1 A (Done s2 (cut A)) -> False.
  Proof.
    (* elim: A s1 s2 => //=; try by move=> s1 s2; inversion 1. 
    + move=> p [].
    + move=> s1 s2; inversion 1 => //.
    + move=> s1 s2; inversion 1 => //. *)
  Admitted.

  Lemma xxx {s1 E}: expand s1 E = Expanded (cut E) -> E = cut E \/ (exists pr s t, E = Goal pr (Call t) /\ F pr t s = [::]).
  Proof.
  Admitted.

  Lemma expand_flow_expanded {s s1 A B C}: expand s A = Solved s1 B -> expand s B = Expanded C -> (B = C).
  Proof.
    elim: A s s1 B C; clear => //.
    + move=> s s1 B C [] /[subst2] //.
    + move=> s s1 B C [] /[subst2] //.
    + by move=> p [].
    + move=> A HA s B HB s1 s2 C D /simpl_expand_or_solved [E [HE]] /[subst1].
      move=> /simpl_expand_or_expanded [].
      + move=> [F [HF]] /[subst1].
        by have := (HA _ _ _ _ HE HF) => /[subst1].
      + move=> [G [HG]] /[subst1].
        rewrite (expand_flow_cut HE HG).
        admit.
    + move=> A HA B0 HB0 B HB s1 s2 C D /simpl_expand_and_solved [s4 [E [F [HE [HF]]]]] /[subst1].
      move=> /simpl_expand_and_expanded [].
      + move=> [G [HG]] /[subst1].
        by have:= (HA _ _ _ _ HE HG) => /[subst1].
      + move=> [s5 [G [H [HG [HH]]]]] /[subst1].
        have := expand_flow HE HG => -[] /[subst2].
        by have:= (HB _ _ _ _ HF HH) => /[subst1].
  Admitted.


  Lemma wip {s s1 s2 A B C}:
    expand s A = Solved s1 B -> expanded s B (Done s2 C) -> (B = C \/ C = cut B) /\ s1 = s2.
  Proof.
    (* remember (Done _ _) as D eqn: HD.
    move=> + H; elim: H s1 s2 A C HD => //; clear.
    + move=> s s1 A B + s2 s3 C D [] /[subst2] H H1.
      apply: expand_flow H1 H.
    + move=> s s1 A B HA HB IH s2 s3 C D /[subst1] H.
      have:= expand_flow_cut H HA => /[subst1].
      by have:= (IH _ _ _ _ erefl H).
    + move=> s s1 A B HA HB IH s2 s3 C D /[subst1] H.
      have:= (IH _ _ _ _ erefl). *)
  Admitted.
  (* Lemma expanded_and {s r A B0 B} : expanded s (And A B0 B) r -> exists A' B', r = (And A' B0 B'). *)

  Lemma expand_and_complete {s s' C A B0 B} :
    expanded s (And A B0 B) (Done s' C) ->
      (exists s'' A' B', expanded s A (Done s'' A') /\ expanded s'' B (Done s' B') /\ C = And A' B0 B').
  Proof.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => H.
    elim: H A B0 B C Hg0 s' Hs1; clear => //.
    - move=> s s' AB alt + A B0 B alt' ? s'' [] ??; subst => //=.
      move=> /simpl_expand_and_solved. 
      move => [s' [A' [B']]] => -[H1 [H2 H3]]; subst.
      do 3 eexists; repeat constructor; eassumption.
    - move=> s s' A B + HB IH A1 B01 B1 C ? s2 ? /[subst].
      move=> /simpl_expand_and_cut [].
      + move=> [A' [HA']] /[subst1].
        move: (IH _ _ _ _ erefl _ erefl) => [s3 [A2 [B2 [HA1 [HB2]]]]] /[subst1] {IH}.
        do 3 eexists; repeat split.
        + apply: expanded_cut HA' HA1.
        + apply: HB2.
      + move=> [s' [A' [B' [HA' [HB']]]]] /[subst1].
        move: (IH _ _ _ _ erefl _ erefl) => [s3 [A2 [B2 [EA2 [EB2]]]]] /[subst1] {IH}.
        have:= wip HA' EA2 => -[] [] /[subst2].
        + do 3 eexists; repeat split.
          + apply: expanded_done HA'. 
          + apply: expanded_cut HB' EB2.
        + by have := expanded_cut1 EA2.
    - move=> s ? A' C + H1 + A B ? s' ???; subst => //.
      move=> /simpl_expand_and_expanded [].
      - move=> [A' [H2]] /[subst1].
        move => /(_ _ _ _ _ erefl _ erefl) [s''' [altA [altB [IHl [IHr]]]]] /[subst1].
        do 3 eexists; repeat split => //=.
        apply: expanded_step H2 IHl.
        by apply IHr.
      - move=> [s2 [A' [B' [H2 [H3]]]]] /[subst1].
        move=> /(_ _ _ _ _ erefl _ erefl) [s''' [altA [altB [IHl [IHr]]]]] ?; subst.
        have := wip H2 IHl => -[] [] /[subst2].
        + do 3 eexists; repeat split => //=.
          + apply: expanded_done H2.
          + apply: expanded_step H3 IHr.
        + by have := expanded_cut1 IHl.
  Qed.

  (* Lemma run_and_correct {s0 s1 s2 A B altA altB} :
      run s0 A (Done s1 altA) -> run s1 B (Done s2 altB) ->
        run s0 (And A B) (Done s2 (And altA altB)).
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H altA s1 s2 B altB HD => //=; clear.
    + move=> + + + + + + s1' s2 B altB + H1.
      remember (Done s2 _) as D eqn:HD.
      elim: H1 s2 altB HD => //=; clear.
      + move=> s s' A altA H altB s2 [] ?? s0 s1 A' altA' H1 altA'' []??; subst.
        apply: run_done => //=; rewrite H1 H => //=.
      + move=> s s' A B H H1 IH s2 altB ? s0 s1 A' altA' H2 altA []??; subst.
        apply: run_cut => //=.
        + rewrite H2 H => //=.
        + apply: IH => //=.
        + eassumption.
      + move=> s ? A B H H1 IH s' ? s'' A' H2 A0 altA0 H3 altA'' [] ??; subst.
        apply: run_step => //=.
        + by rewrite H3 H.
        + by apply: IH erefl.
    + move=> s s' A CA H H1 IH altA s1 s2 B altB ? H2; subst.
      apply: run_cut => //=.
      + by rewrite H.
      + by apply: IH _ H2.
    + move=> s s' A AE H H1 IH altA s1 s2 B altB ? H2; subst.
      apply: run_step => //=.
      + by rewrite H.
      + by apply: IH erefl H2.
  Qed.

  Lemma run_and_fail {s A B}:
    run s (And A B) Failed ->
      run s A Failed \/ (exists s' altA, run s A (Done s' altA) /\ run s' B Failed).
  Proof.
    move=> H.
    remember (And _ _) as R eqn:HR.
    remember Failed as F eqn:HF.
    elim: H A B HR HF => //=; clear.
    + move=> s A + A1 B2 ? _; subst => /simpl_expand_and_fail [].
      + by move=> H; left; apply: run_fail.
      + move=> [s' [L' [H1 H2]]]; right.
        do 2 eexists; split.
        - apply: run_done H1.
        - by apply run_fail.
    + move=> s s' A B + H1 IH A1 B1 ? ?; subst => /simpl_expand_and_cut [].
      - move=> [A'' [H2]] /[subst1].
        move: (IH _ _ erefl erefl) => [].
        + by left; apply: run_cut H2 _.
        + move=> [] s' [] altA [] H4 H5.
          right; do 2 eexists; split; [|eassumption]; apply: run_cut H2 H4.
      - move=> [s' [A2 [B' [H2 [H3]]]]] /[subst1].
        move: (IH _ _ erefl erefl) => []; [by auto|].
        move=> [] s'' [] altA [] H4 H5.
        move: (run_Solved_id H2 H4) => []?; subst.
        right; repeat eexists; [eassumption|apply: run_cut H3 H5].
    + move=> s s' A B + H1 IH A1 B1 ??; subst => //=.
      move=> /simpl_expand_and_expanded [].
      + move=> [A'' [H]] /[subst1].
        move: (IH _ _ erefl erefl) => [] {IH}.
        + by left; apply: run_step H _.
        + move=> [] ? [] altA [] H2 H3.
          by right; repeat eexists; [apply: run_step H H2|].
      + move=> [s' [A2 [B' [H2 [H3]]]]] /[subst1].
        move: (IH _ _ erefl erefl) => [] {IH}; [by auto|].
        move=> [] ? [] altA [] H4 H5.
        move: (run_Solved_id H2 H4) => []?; subst.
        right; repeat eexists; [by eassumption|].
        by apply: run_step H3 H5.
  Qed.

  Lemma run_and_fail_left {s A}:
    run s A Failed ->
      forall B, run s (And A B) Failed.
  Proof.
    move=> H.
    remember Failed as F eqn:HF.
    elim: H HF => //=; clear.
    + move=> s A H _ B2.
      by apply: run_fail => //=; rewrite H.
    + move=> s s' A B H H1 IH B1 ?; subst => //=.
      apply: run_cut => //=.
      + by rewrite H.
      + by auto.
    + move=> s s' A B H H1 IH B1 ?; subst => //=.
      apply: run_step => //=.
      + by rewrite H.
      + by auto.
  Qed.

  Lemma run_and_fail_both {s s' A B alt}:
    run s A (Done s' alt) -> run s' B Failed ->
      run s (And A B) Failed.
  Proof.
    move=> H.
    remember (Done _ _) as D eqn:HD.
    elim: H B s' alt HD => //=; clear.
    + move=> + + + + + B s + + H.
      remember Failed as F eqn:HF.
      elim: H HF => //=; clear.
      + move=> s A H _ s1 s2 A1 alt H1 alt1 [] ??;subst.
        by apply: run_fail => //=; rewrite H1 H.
      + move=> s s' A B H H1 IH ? s1 s2 a1 alt H3 alt1 []??; subst.
        apply: run_cut => //=.
        + rewrite H3 H => //=.
        + apply: IH => //=.
          apply: H3.
      + move=> s s' A B H H1 IH ? s1 s2 a1 alt H3 alt1 []??; subst.
        apply: run_step => //=.
        + by rewrite H3 H.
        + apply: IH => //=.
          apply: H3.
    + move=> s s' A B H H1 IH B1 s1 alt ? H2; subst => //=.
      apply: run_cut => //=.
      + by rewrite H.
      + apply: IH => //=.
    + move=> s s' A B H H1 IH B1 s1 alt ? H2; subst => //=.
      apply: run_step => //=.
      + by rewrite H.
      + apply: IH => //=.
  Qed.

  Lemma run_classic_failure_split {s A B}: 
    run_classic s (And A B) Failed ->
      (run_classic s A Failed) \/ 
        (exists s' altA, run s A (Done s' altA) /\ run_classic s' B Failed).
  Proof.
    remember (And A B) as And eqn:HAnd.
    remember Failed as F eqn:HF.
    move=> H; elim: H A B HAnd HF; clear => //=.
    + move=> s A + A1 B /[subst1] /simpl_expand_and_fail [].
      + by left; apply: run_classic_fail.
      + move=> [s' [L' [H1 H2]]]; right; repeat eexists.
        + apply: run_done H1.
        + by apply: run_classic_fail.
    + move=> s st st1 b + H1 + A B /[subst2] /simpl_expand_and_expanded [].
      + move=> [A' [H2]] /[subst1].
        move=> /(_ _ _ erefl erefl) => -[].
        + move=> H; left; apply: run_classic_step H2 H.
        + move=> [X1 [altA [H3 H4]]]; right.
          repeat eexists.
          + apply: run_step H2 H3.
          + apply: H4.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1].
        move=> /(_ _ _ erefl erefl) [].
        + by left.
        + move=> [s'' [altA [H2 H3]]]; right.
          repeat eexists; try eassumption.
          inversion H2; subst; try congruence; clear H2.
          move: H6; rewrite HA => -[]??; subst.
          by apply: run_classic_step HB H3.
  Qed.

  Lemma run_or_done_cut {s1 s2 SOL A B altA}:
    run s1 A (Done SOL altA) ->
    run s1 (Or A s2 (cut B)) (Done SOL (Or altA s2 (cut B))).
  Proof.
    remember (Done _ _) as D eqn:HD.
    move=> H.
    elim: H altA s2 SOL B HD; clear => //=.
    + move=> s st s' alt H altA s2 SOL B [] ??; subst.
      by apply: run_done => //=; rewrite H.
    + move=> s st st1 st2 H H1 IH s2 SOL B H2 ?; subst.
      apply: run_step => //=.
      + by rewrite H.
      + by rewrite cut_cut_same; apply: IH erefl.
    + move=> s st st1 st2 H H1 IH s2 SOL B0 ??; subst.
      apply: run_step => //=.
      + by rewrite H.
      + by apply: IH.
  Qed.

  Lemma run_or_correct_left {s s' A altA}:
    run s A (Done s' altA) ->
      forall s2 B, exists altB, run s (Or A s2 B) (Done s' (Or altA s2 altB)).
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' altA HD => //=; clear.
    + move=> s st s' alt H s'' altA [] ?? s2 B; subst.
      by eexists; apply: run_done => //=; rewrite H.
    + move=> s A st1 st2 H H1 IH s' altA ? s2 B; subst.
      eexists; apply: run_step => //=.
      + by rewrite H.
      + by apply: run_or_done_cut H1.
    + move=> s st st1 st2 H H1 IH s' altA ? s2 B; subst.
      move: (IH s' altA erefl s2 B) => [altB H2].
      eexists; apply: run_step _ H2 => //=.
      by rewrite H.
  Qed. 

  Lemma run_or_correct_right {s1 s2 s3 A B altB}:
    run_classic s1 A Failed -> run s2 B (Done s3 altB) ->
      (run s1 (Or A s2 B) (Done s3 altB)).
  Proof.
    remember Failed as F eqn:HF.
    move=> H.
    elim: H HF s2 B altB s3; clear => //=.
    + move=> + + + _ s2 B altB s3 H1.
      remember (Done s3 _) as DS eqn:HDS.
      elim: H1 altB s3 HDS => //=; clear.
      + move=> s2 s3 B altB H s3' s4 [] ?? s1 A H1; subst.
        by apply: run_done =>//=; rewrite H1 H.
      + move=> s2 s' B BC H H1 + s3 A ? s1 A' H2; subst.
        move=> /(_ _ _ erefl _ _ H2) IH.
        apply: run_step _ IH => //=.
        by rewrite H2 H.
      + move=> s2 s' B BE H H1 + altB s3 ? s1 A H2; subst.
        move=> /(_ _ _ erefl _ _ H2) IH.
        apply: run_step _ IH => //=.
        by rewrite H2 H.
    + move=> s1 A EA ? H H1 + ? s2 B altB B' H2; subst.
      move=> /(_ erefl _ _ _ _ H2) => IH.
      apply: run_step _ IH => //=.
      by rewrite H.
  Qed.

  Lemma run_or_correct {s1 s2 A B SOL altA altB}:
    (run s1 A (Done SOL altA)) \/ 
      (run_classic s1 A Failed /\ run s2 B (Done SOL altB)) ->
        exists altAB, run s1 (Or A s2 B) (Done SOL altAB).
  Proof.
    move=> [].
    + move=> H; move: (run_or_correct_left H s2 B) => [altB1 H1]; eexists; apply H1.
    + by move=> [] H1 H2; move: (run_or_correct_right H1 H2); exists altB.
  Qed.

  Lemma run_and_done {s A B SOL r}:
    run s (And A B) (Done SOL r) -> exists x y, r = And x y.
  Proof.
    remember (And _ _) as O eqn:HO.
    remember (Done _ _) as D eqn:HD.
    move=> H.
    elim: H A B SOL HO HD; clear => //=.
    + move=> s s' A altA + A' B H SOL [] ??; subst => //=.
      move=> /simpl_expand_and_solved [s' [L [R [H1 [H2]]]]] /[subst1].
      by do 2 eexists.
    + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
      move=> /simpl_expand_and_cut [].
      + by move=> [? [?]] /[subst1]; apply: IH erefl erefl.
      + by move=> [?[?[?[?[?]]]]] /[subst1]; apply: IH erefl erefl.
    + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
      move=> /simpl_expand_and_expanded [].
      + by move=> [?[?]] /[subst1]; apply: IH erefl erefl.
      + by move=> [?[?[?[?[?]]]]] /[subst1]; apply: IH erefl erefl.
  Qed.

  Lemma run_or_complete {s1 s2 A B SOL altAB}:
    run s1 (Or A s2 B) (Done SOL altAB) ->
      (exists altA, run s1 A (Done SOL altA)) \/ 
        (exists altB, run_classic s1 A Failed /\ run s2 B (Done SOL altB)).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1.
    remember (Done _ _) as D eqn:HD.
    move=> H.
    elim: H s2 A B altAB SOL HO1 HD; clear => //=.
    + move=> s st s' alt + s2 A B altAB SOL ? [] /[subst2] /simpl_expand_or_solved [].
      + move=> [HA HB].
        right; eexists; repeat split.
        + apply: run_classic_fail HA.
        + apply: run_done HB.
      + move=> [X [HA HB]]; left.
        eexists; apply: run_done HA.
    + by move=> s ? st1 st2 + H1 IH s2 A B altAB SOL /[subst2] /simpl_expand_or_cut.
    + move=> s ? st1 st2 + H1 IH s2 A B altAB SOL /[subst2] /simpl_expand_or_expanded [|[|[|]]].
      + move=> [A' [HA]] /[subst1].
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[altA[HL HR]]].
        - left; eexists; apply: run_step HA H.
        - right; eexists; split; [apply: run_classic_step HA HL|apply: HR].
      + move=> [A' [HA]] /[subst1].
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[?[HL HR]]].
        - by left; eexists; apply: run_cut HA H.
        - by move: (run_cut_fail HR).
      + move=> [B' [HA [HB]]] /[subst1].
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[?[HL HR]]].
        by destruct (run_Failure_and_Done HA H).
        right; eexists; split; auto; apply: run_step HB HR.
      + move=> [B' [HA [HB]]] /[subst1].
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[? [HL HR]]].
        by destruct (run_Failure_and_Done HA H).
        right; eexists; split; auto; apply: run_cut HB HR.
  Qed.

  Lemma run_run_classic_failure {s A} : 
    run_classic s A Failed -> 
      run s A Failed.
  Proof.
    remember Failed as F eqn:HF.
    move=> H; elim: H HF; clear => //=.
    + move=> ?? H _; by apply: run_fail H.
    + by move=> ???? H H1 H2 ?; subst; apply: run_step H (H2 _).
  Qed.

  Lemma run_or_fail {s1 s2 A B b}:
    run s1 (Or A s2 B) Failed ->
      run s1 A Failed /\ (run_classic s1 A b -> run s2 B Failed).
  Proof.
    move=> H.
    remember (Or _ _ _) as O eqn:HO.
    remember Failed as F eqn:HF.
    move: b s2 A B HO HF.
    elim: H; clear => //=.
    + move=> s s' + b s2 A B /[subst1] /simpl_expand_or_fail [] H1 H2 _.
      by split; intros; apply run_fail.
    + by move=> s st1 st2 ? + H1 IH b s2 A B /[subst2] /simpl_expand_or_cut.
    + move=> s st1 st2 ? + H1 IH b s2 A B /[subst2] /simpl_expand_or_expanded [|[|[|]]].
      + move=> [A' [HA]] /[subst1].
        move: (IH b _ _ _ erefl erefl) => [] HL HR {IH}.
        split; [by apply: run_step HA _|] => H.
        inversion H1; subst; clear H1; move: H0.
        + move=> /simpl_expand_or_fail [HA' HB].
          apply: HR; inversion H; subst; try congruence.
        + by move=> /simpl_expand_or_cut.
        + by epose proof (run_classic_expandedR HA H); auto.
      + move=> [A' [HA]] /[subst1].
        move: (IH b _ _ _ erefl erefl) => [] HL HR.
        split; [by apply: run_cut HA HL|] => H.
        by inversion H; clear H; subst; rewrite HA in H0 => //=.
      + move=> [B' [HA [HB]]] /[subst1].
        move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_step HB (HR HH).
      + move=> [B' [HA [HB]]] /[subst1].
        move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_cut HB (HR HH).
  Qed.

  Lemma run_Failed_cut {s s2 A B}:
    run s A Failed ->
      run s (Or A s2 (cut B)) Failed.
  Proof.
    remember Failed as F eqn:HF.
    move=> H.
    elim: H s2 B HF; clear => //=.
    + move=> s A H s2 B _.
      by apply: run_fail; rewrite /= H /= expand_cut_failure.
    + move=> s s' st1 st2 H H1 IH s2 B ?; subst.
      apply: run_step => //=.
      + by rewrite H.
      + apply: IH erefl.
    + move=> s s' st1 st2 H H1 IH s2 B ?; subst.
      apply: run_step => //=.
      + by rewrite H.
      + apply: IH erefl.
  Qed.

  Lemma run_or_fail1 {s1 s2 g1 g2}:
      run s1 g1 Failed -> (run_classic s1 g1 Failed -> run s2 g2 Failed) ->
        run s1 (Or g1 s2 g2) Failed.
  Proof.
    move: (classic (run_classic s1 g1 Failed)) => [].
    + move=> H + /(_ H) => H1; move: H.  
      remember Failed as F eqn:HF.
      elim: H1 s2 g2 HF; clear => //=.
      + move=> s A H s2 B _ H1 H2; subst.
        remember Failed as F eqn:HF.
        elim: H2 s A H H1 HF; clear => //=.
        + by intros; apply run_fail => //=; rewrite H0 H1.
        + intros; subst. 
          apply: run_step => //=.
          rewrite H3 H0 => //=.
          by apply H2 => //=.
        + intros.
          apply: run_step => //=.
          rewrite H3 H0 => //=.
          by auto.
      + intros; subst.
        by move: (run_classic_cut H3 H0).
      + intros; subst.
        apply: run_step=> //=.
        + by rewrite H0 => //=.
        + by apply: H2 => //=; apply: run_classic_expandedR H0 H3.
    + remember Failed as F eqn:HF.
      move=> + H _.
      elim: H s2 g2 HF; clear => //=.
      + by move=> s st1 H ?? _ []; apply run_classic_fail.
      + move=> s st1 st2 r H H1 IH s2 g2 ? H2; subst.
        apply: run_step => //=.
        + rewrite H => //=.
        + apply: run_Failed_cut H1.
      + move=> s s' A B H H1 IH s2 C ? H2; subst.
        apply: run_step => //=.
        + by rewrite H.
        + apply: IH erefl _.
          move=> H3.
          apply: H2.
          apply: run_classic_step H H3.
  Qed.

  Lemma run_or_fail2 {s1 s2 g1 g2 g3}:
      run s1 g1 Failed -> expand s1 g1 = CutBrothers g3 -> (* g1 coulbe not an immediate cut, but expand... to a cut *)
        run s1 (Or g1 s2 g2) Failed.
  Proof.
    move=> H H1; apply: run_or_fail1 H _ => H2.
    inversion H2; subst; congruence.
  Qed. *)
End RunP.
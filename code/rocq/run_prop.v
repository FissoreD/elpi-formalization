From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import valid_state.

Module RunP (A: Unif).
  Module VS := valid_state(A).
  Include VS.

  Lemma expanded_classic_expanded {s A r}:
    expanded_classic s A r -> expanded s A r.
  Proof. by exists false. Qed.
  
  Lemma run_classic_run {s A r}:
    run_classic s A r -> run s A r.
  Proof. by exists false. Qed.

  Lemma run_classic_cut {s s2 A B r}:
    run_classic s A r -> expand s A = CutBrothers s2 B -> False.
  Proof.
    rewrite /run_classic; remember false as f eqn:Hf => H.
    elim: H s2 B Hf; clear.
    + inversion 1; congruence.
    + inversion 1; congruence.
    + move=> s1 s2 r A A' B b1 b2 b3 HE HN HR IH + s4 A2 /[subst1] +.
      destruct b1, b2 => // _ HC.
      inversion HE; congruence.
  Qed.

  Lemma run_Solved_id {s s1 A r alt}:
      expand s A = Solved s1 alt -> expanded s A r -> r = Done s1 alt.
  Proof.
    move=> + [b H]; by case: H => //=; clear; congruence.
  Qed.

  Lemma expanded_consistent: forall {s0 A s1 s2 b1 b2},
    expandedb s0 A s1 b1 -> expandedb s0 A s2 b2 -> s1 = s2 /\ b1 = b2.
  Proof.
    move=> s0 A s1 + b1 + H.
    elim:H; clear.
    + move=> s s' A alt H b1 b2 H1.
      move: (run_Solved_id H (ex_intro _ _ H1)) => /[subst1].
      by inversion H1; try congruence; subst.
    + move=> s A B HA r b H0.
      inversion H0; try congruence; subst.
      by move: H1; rewrite HA => -[] /[subst1].
    + move=> s1 s2 r A B b HA HB IH s3 b1; inversion 1; try congruence; subst.
      move: H1; rewrite HA => -[] /[subst2].
      by have:= IH _ _ H2 => -[] /[subst2].
    + move=> s1 s2 r A B b1 + HB IH r2 b2 HA.
      by inversion HA; try congruence; subst; rewrite H0 => -[] /[subst2]; auto.
  Qed.

  Lemma next_alt_consistent {s A r1 r2}:
    next_alt s A r1 -> next_alt s A r2 -> r1 = r2.
  Proof.
    move=> H; elim: H r2 => //; clear.
    + move=> s A HA r H1; inversion H1; congruence.
    + move=> s1 s2 A B HA F r1; inversion 1; congruence.
    + move=> ??? ?? H FA NA IH ? H1; inversion H1; try congruence; subst.
      by move: H0; rewrite H => -[] /[subst2]; auto.
  Qed.

  Lemma run_consistent {s A r1 r2 b1 b2}:
    runb s A r1 b1 -> runb s A r2 b2 -> r1 = r2 /\ b1 = b2.
  Proof.
    move=> H; elim: H r2 b2; clear.
    + move=> s s' A B b H r2 b2; inversion 1; subst; have:= expanded_consistent H H1; try congruence.
      by move => -[].
    + move=> s A B b HA HB r b2; inversion 1; subst; have:= expanded_consistent HA H1; try congruence.
      move=> [] [] /[subst2].
      by have:= next_alt_consistent HB H2.
    + move=> ????????? H HN HR IH ???; subst; inversion 1; subst; have:= expanded_consistent H H1; try congruence; move=> [] // [] /[subst2].
      + by have:= next_alt_consistent HN H2.
      + have:= next_alt_consistent HN H2 => -[] /[subst2].
        by have:= IH _ _ H3 => -[] /[subst2].
  Qed.

  Lemma expanded_Failure_and_Done {s s' A A' A''}:
    expand s A = Failure A' -> expanded s A (Done s' A'') -> False.
  Proof. move=> + []; inversion 2; congruence. Qed.


  Lemma expanded_cut_simpl {pr s1 s2 A}:
    expanded s2 (Goal pr Cut) (Done s1 A) -> A = OK.
  Proof.
    inversion 1; inversion H1; subst; simpl in *; try congruence.
    move: H2 => /= [] /[subst2].
    inversion H3; subst; simpl in *; congruence.
  Qed.

  (* Lemma expanded_classic_expandedR {s1 s2 A B b}:
    expand s1 A = Expanded s2 B -> 
      expanded_classic s1 A b ->
        expanded_classic s2 B b.
  Proof.
    move=> + H; elim: H B => //=; congruence.
  Qed. *)

  Lemma expand_cut_failure s A: exists X, expand s (cut A) = Failure X .
  Proof.
    elim: A s => //; clear; try by eexists.
    - move => A + s1 B + s2 /=.
      case X: eq_op; try by eexists.
      move=> /(_ s2) [A'] /= -> /(_ s2) [B'] -> /=.
      destruct A' => //; destruct B'; eexists => //.
    - move => A + B0 _ B + s /=.
      case X: eq_op; try by eexists.
      by move=> /(_ s) [A'] /= -> _; destruct A'; eexists => //=.
  Qed.

  (* Lemma expand_cut_solved {s s' A B}: expand s (cut A) = Solved s' B -> False.
  Proof.
    elim: A s s' B => //; clear.
    + move=> A HA s B HB s1 s2 C /=.
      case X: expand => // -[] /[subst2]; by apply: HA X.
    + move=> A HA B HB C HC s s' D /=; case X: expand => // _.
      apply: HA X.
  Qed. *)

  (* Lemma expand_cut_cb {s s2 A B}: expand s (cut A) = CutBrothers s2 B -> exists B', B = cut B'.
  Proof.
    by rewrite expand_cut_failure.
    elim: A s B => //; clear.
    + move=> A HA s B HB s' C /=; case G: expand => //.
    + move=> A HA B HB C HC s D /=; case G: expand => //.
      + move=> [] /[subst1].
        move: (HA _ _ G) => [B'] /[subst1].
        exists (cut (And B' B C)) => /=.
        by rewrite 3!cut_cut_same.
      + by move: (expand_cut_solved G).
  Qed. *)

  (* Lemma expand_cut_expanded {s s2 A B}: expand s (cut A) = Expanded s2 B -> exists B', B = cut B'.
  Proof.
    elim: A s B => //; clear.
    + move=> A HA s B HB s' C /=; case G: expand => // -[] /[subst2].
      + by move: (HA _ _ G) => [X] /[subst1]; exists (Or X s B).
      + by move: (expand_cut_cb G) => [X] /[subst1]; exists (Or X s B); rewrite cut_cut_same.
    + move=> A HA B HB C HC s D /=; case G: expand => //.
      + move=> [] /[subst1].
        move: (HA _ _ G) => [B'] /[subst1].
        exists (cut (And B' B C)) => /=.
        by rewrite 3!cut_cut_same.
      + by move: (expand_cut_solved G).
  Qed. *)

  (* Lemma next_alt_cut {b s s' A B}: next_alt_aux b s (cut A) = Some (s', B) -> exists A, B = cut A.
  Proof.
    elim: A b B s s' => //; clear.
    + move=> A IH s2 B IHB bool C s s'; simpl cut => /simpl_next_alt_aux_some [|[]].
      + move=> [B'[]]; destruct A => // _ [] /IHB [B2] /[subst2].
        by exists (Or Dead s2 B2) => //=.
      + by move=> [A'[_ [+]]] /[subst1] /IH [C] /[subst1]; exists (Or C s2 B) => /=.
      + move=> [_ [H]] /[subst1] .
        by exists (Or Dead s2 B) => /=.
    + move=> A HA B0 HB0 B HB bool C s s'; rewrite /next_alt /=.
      case G: next_alt_aux => [x|].
      + case: x G => s2 b HN [] /[subst2].
        move: (HB _ _ _ _ HN) => [B'] /[subst1].
        by exists (And A B0 B').
      + case H: next_alt_aux => [x|] //.
        case: x H => s2 A' NA -[] /[subst2].
        move: (HA _ _ _ _ NA) => [A2] /[subst1] //.
        by exists (And A2 B0 B0).
  Qed. *)

  Lemma expanded_cut_done {s s' A B}:
    expanded s (cut A) (Done s' B) -> False.
  Proof.
    remember (cut _) as CA eqn:HCA.
    remember (Done _ _) as D eqn:HD => -[b H].
    elim: H s' A B HCA HD => //; clear.
    + move=> s s' A B + s2 C D ? -[] ?? /[subst].
      have [? H]:= expand_cut_failure s C.
      by rewrite H.
    + move=> s s' r A B b + HB IHA s2 C D ?? /[subst].
      have [? H]:= expand_cut_failure s C.
      by rewrite H.
    + move=> s s' r A B b + HB IH s2 C D ?? /[subst].
      have [? H]:= expand_cut_failure s C.
      by rewrite H.
  Qed.

  (* Lemma expanded_cut_fail {s A}:
    exists B, expanded s (cut A) (Failed B).
  Proof.
    elim: A s=> //; try by by eexists; econstructor; econstructor.
    + move=> A + s B + s1 => /(_ s1) [A' HA] /(_ s1) [B' HB] /=.
      eexists; eexists.
      apply: expanded_step.
      by rewrite (expand_cut_failure).
    + move=> s s' r A B b + HB IH C D /[subst2].
      by rewrite (expand_cut_failure).
  Qed. *)

  (* Lemma next_alt_cut_some {s s1 A B}: next_alt s (cut A) (Some (s1, B)) -> False.
  Proof.
    remember (cut _) as C eqn:HC.
    remember (Some _) as S eqn:HS => H.
    elim: H s1 A B HC HS => //; clear.
    + move=> s1 s2 A B + FB s3 C D ? -[] ??; subst => /next_alt_cut [A' H]; subst.
      by rewrite failed_cut in FB.
    + move=> s s1 ? A B NA FA NB IH ??? /[subst2].
      have:= next_alt_cut NA => -[B'] /[subst1].
      apply: IH erefl erefl.
  Qed. *)

  (* Lemma run_cut_fail {s s' A altA} :
    run s (cut A) (Done s' altA) -> False.
  Proof.
    remember (cut _) as CA eqn:HCA.
    remember (Done _ _) as D eqn:HD => -[b H].
    elim: H s' A altA HCA HD => //=; clear.
    + move=> s s' ? B ? HA s2 AC B' /[subst1] -[] /[subst2].
      apply: expanded_cut_done (ex_intro _ _ HA).
    + move=> s s1 r A B C ??? HA + HC IH ? ??? ?? /[subst].
      (* have := ex_intro _ _ HA. *)
      move=> /expanded_cut_fail [B'] /[subst1]. /next_alt_cut_some.
  Qed. *)

  (* Lemma expand_flow {s s1 s2 A B C}: expand s A = Solved s1 B -> expand s B = Solved s2 C -> B = C /\ s1 = s2.
  Proof.
    elim: A s s1 s2 B C; clear => //.
    + by move=> s s1 s2 B C [] /[subst2] -[] /[subst2].
    + by move=> p [].
    + move=> A HA s B HB s1 s2 s3 C D /simpl_expand_or_solved [E [HE]] /[subst1].
      move=> /simpl_expand_or_solved [F [HF]] /[subst1].
      by have := (HA _ _ _ _ _ HE HF) => -[] /[subst2].
    + move=> A HA B0 HB0 B HB s1 s2 s3 C D /simpl_expand_and_solved [s4 [E [F [HE [HF]]]]] /[subst1].
      move=> /simpl_expand_and_solved [s5 [G [H [HG [HH]]]]] /[subst1].
      have:= (HA _ _ _ _ _ HE HG) => -[] /[subst2].
      by have:= (HB _ _ _ _ _ HF HH) => -[] /[subst2].
  Qed. *)

  (* Lemma expand_flow_cut {s s1 sE A B C}: expand s A = Solved s1 B -> expand s B = CutBrothers sE C -> B = C.
  Proof.
    elim: A s s1 sE B C; clear => //.
    + move=> s s1 ? B C [] /[subst2] //.
    + by move=> p [].
    + move=> A HA s B HB s1 ? s2 C D /simpl_expand_or_solved [E [HE]] /[subst1].
      by move=> /simpl_expand_or_cut.
    + move=> A HA B0 HB0 B HB s1 ? s2 C D /simpl_expand_and_solved [s4 [E [F [HE [HF]]]]] /[subst1].
      move=> /simpl_expand_and_cut [].
      + move=> [G [HG]] /[subst1].
        by have:= (HA _ _ _ _ _ HE HG) => /[subst1].
      + move=> [s5 [G [H [HG [HH]]]]] /[subst1].
        have := expand_flow HE HG => -[] /[subst2].
        by have:= (HB _ _ _ _ _ HF HH) => /[subst1].
  Qed. *)

  (* Lemma expand_solved_cut {s s1 A} : expand s A = Solved s1 (cut A) -> False.
  Proof.
    elim: A s s1 => //.
    + move=> p [] //.
    + move=> A HA s B HB s1 s2 /simpl_expand_or_solved [C [HC]] [] /[subst2].
      apply: HA HC.
    + move=> A HA B HB C HC s1 s2 /simpl_expand_and_solved [s3[D[E[HD[HE]]]]] [] /[subst2] /[subst1].
      apply: HA HD.
  Qed. *)

  (* Lemma expanded_big_or_KO {s1 s2 s3 p t}:
    expanded s1 (big_or p s2 t) (Done s3 KO) -> False.
  Proof.
    remember (big_or _ _ _) as B eqn:HB.
    remember (Done _ _) as D eqn:HD => -[b H].
    elim: H s2 s3 p t HB HD => //; clear.
    + move=> ???? + ??? t ? [] ??; subst.
      by rewrite /big_or; case: F => // -[] //.
    + move=> s s' r A B ? + HB IH s1 s2 p t ??; subst.
      by rewrite /big_or; case: F => // -[] //.
    + move=> s s' r A B ? + HB IH s1 s2 p t ??; subst.
      by rewrite /big_or; case: F => // -[] //.
  Qed. *)

  (* Lemma expanded_cut1 {s1 s2 A}: expanded s1 A (Done s2 (cut A)) -> False.
  Proof.
    elim: A s1 s2 => //=; try by move=> s1 s2; inversion 1. 
    + move=> s1 s2; inversion 1; subst; simpl in *; try congruence.
      injection H1 => /[subst1]; inversion H2; subst; simpl in *; try congruence.
    + move=> s1 s2; inversion 1; subst; simpl in *; try congruence.
      injection H1 => /[subst1]; inversion H2; subst; simpl in *; try congruence.
    + move=> p [] s1 s2; inversion 1; subst; simpl in *; try congruence.
      injection H1 => /[subst1]; inversion H2; subst; simpl in *; try congruence.
      injection H1 => /[subst2]; apply: expanded_big_or_KO H2.
    + move=> A HA s B HB s1 s2.
      inversion 1 ; subst.
      + move: H4 => /simpl_expand_or_solved [A' [HA']] [] /[subst2].
        by have:= expand_solved_cut HA'.
      + by move: H1 => /simpl_expand_or_cut.
      + admit.
    + move=> A HA B0 HB0 B HB s1 s2; inversion 1; subst.
      + move: H4 => /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] [] ??? /[subst].
        by have:= expand_solved_cut HA'.
      + move: H1 => /simpl_expand_and_cut [].
        + move=> [A'[HA']] /[subst1].
  Admitted. *)

  (* Lemma xxx {s1 E}: expand s1 E = Expanded (cut E) -> E = cut E \/ (exists pr s t, E = Goal pr (Call t) /\ F pr t s = [::]).
  Proof.
  Admitted. *)

  (* Lemma wip {s s1 s2 A B C}:
    expand s A = Solved s1 B -> expanded s B (Done s2 C) -> (B = C \/ C = cut B) /\ s1 = s2.
  Proof.
    remember (Done _ _) as D eqn: HD.
    move=> + H; elim: H s1 s2 A C HD => //; clear.
    + move=> s s1 A B + s2 s3 C D [] /[subst2] H H1.
      apply: expand_flow H1 H.
    + move=> s s1 A B HA HB IH s2 s3 C D /[subst1] H.
      have:= expand_flow_cut H HA => /[subst1].
      by have:= (IH _ _ _ _ erefl H).
    + move=> s s1 A B HA HB IH s2 s3 C D /[subst1] H.
      have:= (IH _ _ _ _ erefl).
  Admitted. *)
  (* Lemma expanded_and {s r A B0 B} : expanded s (And A B0 B) r -> exists A' B', r = (And A' B0 B'). *)

  (* Fixpoint same_state A B :=
    match A B with
    |  *)

  Lemma expand_solved_solved {s s1 s2 s3 A B C}: expand s A = Solved s1 B -> expand s2 B = Solved s3 C -> B = C /\ s2 = s3.
  Proof.
    elim: A s s1 s2 s3 B C => //.
    + by move=> ?????? [] /[subst2] -[] /[subst2].
    + by move=> ? [] //.
    + move=> A HA s B HB s1 s2 s3 s4 C D /simpl_expand_or_solved [].
      + move=> [A'[HA']] /[subst1] /simpl_expand_or_solved [].
        + move=> [A2[HA2]] /[subst1].
          have:= HA _ _ _ _ _ _ HA' HA2.
          by destruct A' => //; try by move=> [] <- <-.
        + move=> [B'[HA2[HB']]] /[subst1].
          by have []:= expand_solved_success HA' => _ /(succes_is_solved s3); rewrite HA2 => -[] //.
      + move=> [B' [HA'[HB']]] /[subst1] /simpl_expand_or_solved [].
        + by move=> [A2[HA2]] /[subst1].
        + move=> [B2[HA2[HB2]]] /[subst1].
          by have:= HB _ _ _ _ _ _ HB' HB2 => -[] -> ->.
    + move=> A HA B0 HB0 B HB s1 s2 s3 s4 C D /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1] /simpl_expand_and_solved [s7[A2[B2[HA2[HB2]]]]] /[subst1].
      have:= HA _ _ _ _ _ _ HA' HA2 => -[] /[subst2].
      by have:= HB _ _ _ _ _ _ HB' HB2 => -[] /[subst2].
  Qed.

  Lemma expand_solved_is_solved {s s1 s2 A B}: expand s A = Solved s1 B -> expand s2 B = Solved s2 B.
  Proof.
    elim: A s s1 s2 B => //.
    + by move=> ???? [] /[subst2].
    + by move=> ? [] //.
    + move=> A HA s B HB s1 s2 s3 C /simpl_expand_or_solved [].
      + move=> [A' [HA']] /[subst1] /=; by rewrite (HA _ _ _ _ HA').
      + move=> [B'[HA'[HB']]] /[subst1] /=; rewrite (HB _ _ _ _ HB') //.
    + move=> A HA B0 HB0 B HB s1 s2 s3 C /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1]/=.
      by rewrite (HA _ _ _ _ HA') (HB _ _ _ _ HB').
  Qed.

  Lemma expand_solved_expand {s s1 s2 s3 A B C}: expand s A = Solved s2 B -> expanded s1 B (Done s3 C) -> B = C /\ s1 = s3.
  Proof.
    remember (Done _ _) as D eqn:HD => + [b H].
    elim: H s s2 s3 A C HD => //; clear.
    + move=> ???? H ????? [] ?? /[subst] /expand_solved_solved => /(_ _ _ _ H)[] ??; subst => //.
    + move=> s s1 r A B ? HA HB IH s2 s3 s4 C D /[subst1] /expand_solved_is_solved => /(_ s); congruence.
    + move=> s s1 r A B ? HA HB IH s2 s3 s4 C D /[subst1] /expand_solved_is_solved => /(_ s); congruence.
  Qed.

  Lemma expanded_and_failed_split {s A B0 B C}: 
    expanded s (And A B0 B) (Failed C) -> (A = dead A /\ C = Dead) \/ exists A' B', (A <> dead A /\ C = And A' B0 B').
  Proof.
    remember (And _ _ _) as RA eqn:HRA.
    remember (Failed _) as RF eqn:HRF => -[? H].
    elim: H A B HRA HRF; subst => //.
    + move=> ??? + ??? [] ? /[subst] => /simpl_expand_and_fail [|[]].
      + by move=> [] /expand_failure_is_dead <- <-; auto.
      + move=> [A' [X[HA']]] /[subst1]; right; do 2 eexists.
        Search expand Failure Dead.
        by have:= expand_failure_not_dead_left HA' X.
      + move=> [s'[A'[B'[HA'[HB']]]]] /[subst1]; right.
        by have:= expand_solved_success HA' => -[] /success_failed /failed_dead H; do 2 eexists.
    + move=> s1 s2 r D E ? + H2 IH ?? /[subst2] => /simpl_expand_and_cut [].
      + move=> [A'[HA']] /[subst1].
        have {IH}:= IH _ _ erefl erefl => -[].
        + move=> []; by have:= expand_cb_not_dead HA'.
        + move => -[?[?[?]]] /[subst1] => []; right; do 2 eexists; split => //.
          move=> /(expand_is_dead_flow s1); congruence.
      + move=> [?[?[? [HA'[HB']]]]] /[subst1].
        have:= IH _ _ erefl erefl => -[[]|].
        + by have:= expand_solved_success HA' => -[] _ /success_failed/failed_dead.
        + move=> [A[B[D ]]] /[subst1]; right; do 2 eexists; split => //.
          move=> /(expand_is_dead_flow s1); congruence.
    + move=> s1 ????? + HB IH ?? /[subst2] => /simpl_expand_and_expanded [].
      + move=> [A'[HA']] /[subst1].
        have:= IH _ _ erefl erefl => -[[]|].
        + by have:= expand_expanded_not_dead HA'.
        + move=> [A2[B2[?]]] /[subst1].
          right; do 2 eexists; split => //.
          move=> /(expand_is_dead_flow s1); congruence.
      + move=> [?[?[? [HA'[HB']]]]] /[subst1].
        have:= IH _ _ erefl erefl => -[[]|].
        + by have:= expand_solved_success HA' => -[] _ /success_failed/failed_dead.
        + move=> [A2[B2[?]]] /[subst1].
          right; do 2 eexists; split => //.
          move=> /(expand_is_dead_flow s1); congruence.
  Qed.

  Lemma expanded_and_complete {s s' C A B0 B} :
    expanded s (And A B0 B) (Done s' C) ->
      (exists s'' A' B', expanded s A (Done s'' A') /\ expanded s'' B (Done s' B') /\ C = And A' B0 B').
  Proof.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => -[b H].
    elim: H A B0 B C Hg0 s' Hs1; clear => //.
    - move=> s s' AB alt + A B0 B alt' ? s'' [] ??; subst => //.
      move=> /simpl_expand_and_solved. 
      move => [s' [A' [B']]] => -[H1 [H2 H3]]; subst.
      do 3 eexists; repeat split; eexists; apply: expanded_done; eassumption.
    - move=> s s' r A B ? + HB IH A1 B01 B1 C ? s2 ? /[subst].
      move=> /simpl_expand_and_cut [].
      + move=> [A' [HA']] /[subst1].
        move: (IH _ _ _ _ erefl _ erefl) => [s3 [A2 [B2 [[? HA1] [HB2]]]]] /[subst1] {IH}.
        do 3 eexists; repeat split.
          + eexists; apply: expanded_cut HA' HA1.
          + apply: HB2.
      + move=> [s'' [A' [B' [HA' [HB']]]]] /[subst1].
        move: (IH _ _ _ _ erefl _ erefl) => [s3 [A2 [B2 [EA2 [[? EB2]]]]]] /[subst1] {IH}.
        have:= expand_solved_expand HA' EA2 => -[] /[subst2].
        do 3 eexists; repeat split.
        + eexists; apply: expanded_done HA'.
        + eexists; apply: expanded_cut (HB') EB2.
    - move=> s ? r A' C ? + H1 + A B ? ? ? ??; subst => /simpl_expand_and_expanded [].
      - move=> [A' [EA]] /[subst1].
        move => /(_ _ _ _ _ erefl _ erefl) [s' [A2 [B2 [[? HA'] [HB']]]]] /[subst1].
        + do 3 eexists; repeat split => //=.
          eexists. apply: expanded_step EA HA'.
        + by apply HB'.
      - move=> [s2 [A' [B' [EA' [EB']]]]] /[subst1].
        move=> /(_ _ _ _ _ erefl _ erefl) [s' [A2 [B2 [[? HA'] [[? HB']]]]]] ?; subst.
        have:= expand_solved_expand EA' (ex_intro _ _ HA') => -[] /[subst2].
        do 3 eexists; repeat split => //=.
        + eexists; apply: expanded_done EA'.
        + eexists; apply: expanded_step EB' HB'.
  Qed.

  Lemma expanded_and_correct {s0 s1 s2 A C B0 B D} :
      expanded s0 A (Done s1 B) -> expanded s1 C (Done s2 D) ->
        expanded s0 (And A B0 C) (Done s2 (And B B0 D)).
  Proof.
    remember (Done _ _) as RD eqn:HRD => -[b H].
    elim: H s1 s2 C B0 B D HRD => //=; clear.
    + move=> + s1 + B + s2 s3 C + E F [] ?? [b H1] /[subst].
      remember (Done s3 _) as RD eqn:HRD.
      elim: H1 s3 E F HRD => //=; clear.
      + move=> s s' A B EA s2 C D [] /[subst2] s3 E EE F.
        by eexists; apply: expanded_done => /=; rewrite EE EA.
      + move=> s s' r A B ? HA HB IH s2 C D /[subst1] s3 E HE B0.
        have HE':= expand_solved_is_solved HE.
        have [? {}IH] := IH _ _ _ erefl _ _ (HE' _) B0.
        eexists; apply: expanded_cut => //=.
        + rewrite HE HA => //=.
        + apply: IH => //=.
      + move=> s ? r A B ? H H1 IH s' ?? /[subst1] ?? H2 B0.
        have HE':= expand_solved_is_solved H2.
        have [? {}IH] := IH _ _ _ erefl _ _ (HE' _) B0.
        eexists; apply: expanded_step => //=.
        + by rewrite H2 H.
        + by apply: IH.
    + move=> s s' r A CA ? H H1 IH ?? ? B0 ?? /[subst1] H2.
      have [? {}IH]:= IH _ _ _ B0 _ _ erefl H2.
      eexists; apply: expanded_cut => //=.
      + by rewrite H.
      + by apply: IH.
    + move=> s s' r A AE ? H H1 IH ?? ? B0 ?? /[subst1] H2.
      have [? {}IH]:= IH _ _ _ B0 _ _ erefl H2.
      eexists; apply: expanded_step => //=.
      + by rewrite H.
      + by apply: IH.
  Qed.

  Search expanded Failed And.

  Lemma success_is_not_failed {s s' A2}: success A2 -> expanded s' A2 (Failed s) -> False.
  Proof.
    remember (Failed _) as RF eqn:HRF => + [? H].
    elim: H s HRF => //; clear.
    + move=> ??? /expand_failure_failed [] /failed_success -> //.
    + by move=> s s' r A B ? HA HB IH C /[subst1] /(succes_is_solved s) [] ss; rewrite HA.
    + move=> s s' r A B ? HA HB IH C /[subst1].
      move=> /(succes_is_solved s) [? ? ]; congruence.
  Qed.

  Lemma expandes_and_fail {s A B0 B C}:
    expanded s (And A B0 B) (Failed C) ->
      (exists C', expanded s A (Failed C')) \/ (exists s' A' B', expanded s A (Done s' A') /\ expanded s' B (Failed B')).
  Proof.
    move=> /[dup] /expanded_and_failed_split [D[E]]/[subst1].
    remember (And _ _ _) as R eqn:HR.
    remember (Failed _) as F eqn:HF => -[? H].
    elim: H A B0 B C D E HR HF => //=; clear.
    + move=> ??? + ?????? /[subst1] => + [] ?; subst => /simpl_expand_and_fail [].
      + move=> [?[HA]] [] /[subst2]; left; do 2 eexists ; apply: expanded_fail HA.
      + move=> [?[?[?[L' [H1]]]]] [] /[subst2]; right.
        do 3 eexists; split.
        - eexists; apply: expanded_done L'.
        - eexists; apply: expanded_fail H1.
    + move=> s s' r A B ? + H1 IH A1 B1 ? Mh ? ??? ; subst => /simpl_expand_and_cut [].
      - move=> [A'' [H2]] /[subst1].
        move: (IH _ _ _ Mh _ _ erefl erefl) => [].
        + move=> [? [? H]]; left ; do 2 eexists ; apply: expanded_cut H2 H.
        + move=> [] s2 [] altA [] ? [] [? H4] H5.
          right; do 3 eexists; split; [|eassumption]; eexists; apply: expanded_cut H2 H4.
      - move=> [s2 [A2 [B' [H[H2]]]]] /[subst1].
        move: (IH _ _ _ Mh _ _ erefl erefl) => [].
        + move=> [? H3]; have:= expand_solved_success H.
          by move=> /success_is_not_failed => /(_ _ _ H3).
        + move=> [] s'' [] altA [] ? [] H4 [? H5].
          have:= expand_solved_expand (H) (H4) => - [] /[subst2]; right.
          do 3 eexists; split.
          + eexists; apply: expanded_done H.
          + eexists; apply: expanded_cut H2 H5.
    + move=> s s' r A B ? + H1 IH A1 B1 ? Mh ????; subst => /simpl_expand_and_expanded [].
      + move=> [A'' [HA'']] /[subst1].
        move: (IH _ _ _ Mh _ _ erefl erefl) => [] {IH}.
        + move=> [? [? H]]; left; do 2  eexists; apply: expanded_step HA'' H.
        + move=> [] ? [] altA [] ? [] [? H2] [? H3].
          right; repeat eexists; [apply: expanded_step HA'' H2|apply H3].
      + move=> [s2 [A2 [B' [H2 [H3]]]]] /[subst1].
        move: (IH _ _ _ Mh _ _ erefl erefl) => [] {IH}.
        + move=> [? H].
          have:= expand_solved_success H2.
          by move=> /success_is_not_failed => /(_ _ _ H).
        + move=> [] ? [] altA [] ? [] H4 [? H5]; right.
          have:= expand_solved_expand H2 H4 => -[] /[subst2].
          do 3 eexists; split.
          + eexists; apply: expanded_done H2.
          + eexists; apply: expanded_step H3 H5.
  Qed.

  Lemma expanded_and_fail_left {s A B0 FA}:
    expanded s A (Failed FA) ->
      forall B, expanded s (And A B0 B) (Failed (And FA B0 B)).
  Proof.
    move=> [? H].
    remember (Failed _) as F eqn:HF.
    elim: H FA B0 HF => //=; clear.
    + move=> s A H H1 ?? [] /[subst1] ?.
      by eexists; apply: expanded_fail => //=; rewrite H1.
    + move=> s s' r A B ? H H1 IH ? B0 ? B1; subst => //=.
      have [?{}IH]:= IH _ B0 erefl B1.
      eexists; apply: expanded_cut => //=.
      + by rewrite H.
      + apply: IH.
    + move=> s s' r A B ? H H1 IH ? B0 ? B1; subst => //=.
      have [?{}IH]:= IH _ B0 erefl B1.
      eexists; apply: expanded_step => //=.
      + by rewrite H.
      + apply: IH.
  Qed.

  Lemma run_and_fail_both {s s' A B B0 SA FB}:
    expanded s A (Done s' SA) -> expanded s' B (Failed FB) ->
      expanded s (And A B0 B) (Failed (And SA B0 FB)).
  Proof.
    move=> [? H].
    remember (Done _ _) as D eqn:HD.
    elim: H B s' SA HD => //=; clear.
    + move=> s1 s2 A B HA C s3 D [] /[subst2] -[? H].
      remember (Failed _) as F eqn:HF.
      elim: H B0 FB s1 A D HA HF; clear => //.
      + move=> s A ? H ????? EA [] /[subst1].
        by eexists; apply: expanded_fail => //= ; rewrite EA H .
      + move=> s s' r A B ? HA HB IH B0 ???? HA' /[subst1].
        have := expand_solved_is_solved HA' => /(_ s') HA2.
        have [? {}IH]:= (IH B0 _ _ _ _ HA2 erefl).
        eexists; apply: expanded_cut => //=.
        + rewrite HA' HA => //=.
        + apply: IH.
      + move=> s s' r A A' ? HA HB IH B0 D s2 B B' EB /[subst1].
        have := expand_solved_is_solved EB => /(_ s') HA2.
        have [? {}IH] := (IH B0 _ _ _ _ HA2 erefl).
        eexists; apply: expanded_step => //=.
        + rewrite EB HA => //=.
        + apply: IH.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? H2; subst => //=.
      have [? {}IH] := IH _ _ _ erefl H2.
      eexists;apply: expanded_cut => /=.
      + by rewrite H.
      + by apply IH.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? H2; subst.
      have [? {}IH] := IH _ _ _ erefl H2.
      eexists ; apply: expanded_step => /=.
      + by rewrite H.
      + by apply: IH.
  Qed.

  (* Lemma expand_classic_failure_split {s A B B0 FAB}: 
    expand_classic s (And A B0 B) (Failed FAB) ->
      exists FA, expand_classic s A (Failed FA).
  Proof.
    (* remember (And A B) as And eqn:HAnd.
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
          by apply: run_classic_step HB H3. *)
  Admitted. *)

  (* Lemma expanded_or_failed_split {s s1 A s3 B C}: 
    expanded s (Or A s3 B) (Done s1 C) -> exists A' B', C = Or A' s3 B'.
  Proof.
    remember (Or _ _ _) as RA eqn:HRA.
    remember (Done _ _) as RF eqn:HRF => -[? H].
    elim: H s1 s3 A B HRA HRF; subst => //.
    + move=> ???? + ????? [] ?? /[subst] => /simpl_expand_or_solved [].
      + by move=> [A'[HA']] /[subst1]; do 2 eexists.
      + move=> [B'[HA'[HB']]] /[subst1]; by do 2 eexists.
    + move=> ?? r D E ? + H2 IH ????? /[subst] => /simpl_expand_or_cut [s2[B'[?[HA']]]] /[subst2].
      apply: IH.
    + move=> ?????? + HB IH ???? /[subst] => /simpl_expand_or_expanded [].
      + move=> [A'[HA']] /[subst1].
        by have:= IH _ _ erefl erefl => -[?[?]] /[subst1] => []; do 2 eexists.
      + move=> [? [HA']] /[subst1].
        by have:= IH _ _ erefl erefl => -[?[?]] /[subst1] => []; do 2 eexists.
  Qed. *)

  Lemma expanded_or_correct_left {s s' A A'} b:
    expandedb s A (Done s' A') b ->
      forall s2 B, expanded s (Or A s2 B) (Done s' (Or A' s2 (if b then cut B else B))).
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A' HD => //=; clear.
    + move=> s s' A A' HA s2 B [] ?? s3 C; subst.
      by eexists; apply: expanded_done => //= ; rewrite HA.
    + move=> s1 s2 r A B b HA HB IH s3 C ? s4 D /[subst].
      have [? {}IH]:= IH _ _ erefl s4 (cut D).
      eexists; apply: expanded_step => //=.
      + by rewrite HA.
      + move: IH; rewrite cut_cut_same if_same => H; eassumption.
    + move=> s1 s2 r A B b HA HB IH s' C ? s4 D /[subst].
      have [? {}IH] := IH _ _ erefl s4 D.
      eexists; apply: expanded_step => //=.
      + by rewrite HA.
      + apply IH. 
  Qed.

  Lemma expanded_or_cut {s' s3 s2 E A' B B'}:
    expanded s3 (Or E s2 (cut B)) (Done s' (Or A' s2 B')) -> B' = cut B.
  Proof.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or E _ _) as RO eqn:HRO => -[b1 H].
    elim: H E HRD HRO => //.
    + move=> s ??? + ? [] ? ? ? /[subst] => /simpl_expand_or_solved [].
      + move=> [? [H]] [] /[subst2] //.
      + move=> [? [H]] []; by have [? H1]:= expand_cut_failure s B; rewrite H1.
    + move=> ?????? + H2 IH H3 ?? /[subst] => /simpl_expand_or_cut [s1 [B2[?[+]]]] /[subst1].
      by have [? H1]:= expand_cut_failure s2 B; rewrite H1.
    + move=> s ????? + H1 IH ??? /[subst] => /simpl_expand_or_expanded [|[]].
      + by move=> [?[H2]] ?/[subst]; apply: IH erefl erefl.
      + by move=> [?[H2]] ?/[subst]; apply: IH erefl _; rewrite cut_cut_same; apply: erefl.
      + by move=> [HA] [B2[?]] /[subst]; have [? H2]:= expand_cut_failure s B; rewrite H2 => -[].
  Qed.

  Lemma expanded_or_complete_left {s s' s2 A A' B B'} b:
    expandedb s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
      (is_dead A = false /\ expanded s A (Done s' A')) \/ (is_dead A /\ expanded s B (Done s' B')).
  Proof.
    rewrite /expanded.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s' s2 A' B' A B HRO HRD => //=.
    + move=> s1 s3 C D + A B HRO ???? [] ??; subst => /simpl_expand_or_solved [].
      + move=> [A2 [HA']] [] ?/[subst]; left; split.
        + rewrite (expand_solved_not_is_dead_left HA') //.
        + eexists; apply: expanded_done HA'.
      + move=> [B'[HA'[HB']]] [] /[subst2]; right; rewrite (expand_failure_is_dead HA'); split => //.
        by eexists; apply: expanded_done.
    + move=> s1 s3 r C D b2 + HB IH ??????? /[subst] => /simpl_expand_or_cut [s4[B'[?[HA']]]] /[subst2].
      right => /=; split => //=.
      have:= IH _ _ _ _ _ _ erefl.
      (* eexists; apply: expanded_cut. HA' _.


    + move=> s1 s3 r C D b2 + HB IH ? F ? /[subst] => /simpl_expand_or_expanded [].
      + move=> [E [HE]] /[subst2].
        have [? {}IH]:= IH _ _ erefl erefl.
        eexists; apply: expanded_step HE IH.
      + move=> [E[HE]] /[subst2].
        have H:= expanded_or_cut (ex_intro _ _ HB).
        have := IH E (cut F) erefl; rewrite cut_cut_same; rewrite H if_same => /(_ erefl) [? {}IH].
        eexists; apply: expanded_cut HE IH. *)
  Admitted.

  Lemma expanded_or_done_cut {s1 s2 s3 A B A'}:
    expanded s1 A (Done s3 A') ->
    expanded s1 (Or A s2 (cut B)) (Done s3 (Or A' s2 (cut B))).
  Proof.
    by move=> [] ? /expanded_or_correct_left /(_ s2 (cut B)); rewrite cut_cut_same if_same.
  Qed.
  
  Lemma expanded_or_complete {s s1 s2 A A' B B'}:
    expanded s (Or A s2 B) (Done s1 (Or A' s2 B')) ->
      expanded s A (Done s1 A').
  Proof.
    remember (Or _ _ _) as RO eqn:HRO.
    remember (Done _ _) as RD eqn:HRD => -[? H].
    elim: H s1 s2 A A' B B' HRD HRO => //; clear.
    + move=> ???? + s2 A B altAB ?? [] ??? /[subst] => /simpl_expand_or_solved [].
      + move=> [A' [HA]] [] /[subst2]; by eexists; apply: expanded_done.
      (* + move=> [B'[HA[HB]]] [] /[subst2].
    + by move=> ?????? + H1 IH ?????? /[subst] => /simpl_expand_or_cut.
    + move=> ?????? + H1 IH s2 A B altAB ?? /[subst] => /simpl_expand_or_expanded [].
      + move=> [A' [HA]] /[subst1].
        have [? {}IH]:= IH _ _ _ _ erefl erefl.
        eexists; apply: expanded_step HA IH.
      + move=> [A' [HA]] /[subst1].
        have [? {}IH]:= IH _ _ _ _ erefl erefl.
        eexists; apply: expanded_cut HA IH.
  Qed. *)
Admitted.

  (* Lemma expanded_or_correct_left_fail {s A A'} b:
    expandedb s A (Failed A') b ->
      forall s2 B, expanded s (Or A s2 B) (Failed (Or A' s2 (if b then cut B else B))).
  Proof.
    remember (Failed _) as D eqn:HD => H.
    elim: H A' HD => //=; clear.
    + move=> s A A' HA B [] ? s3 C; subst.
      by eexists; apply: expanded_fail => //= ; rewrite HA.
    + move=> s1 s2 r A B b HA HB IH C ? s4 D /[subst].
      have [? {}IH]:= IH _ erefl s4 (cut D).
      eexists; apply: expanded_step => //=.
      + by rewrite HA.
      + move: IH; rewrite cut_cut_same if_same => H; eassumption.
    + move=> s1 s2 r A B b HA HB IH C ? s4 D /[subst].
      have [? {}IH] := IH _ erefl s4 D.
      eexists; apply: expanded_step => //=.
      + by rewrite HA.
      + apply IH. 
  Qed. *)

  (*Lemma run_or_correct {s1 s2 A B SOL A'}:
    (run s1 A (Done SOL A')) \/ 
      (exists FA, run_classic s1 A (Failed FA)) ->
        exists AB', run s1 (Or A s2 B) (Done SOL AB').
  Proof. *)
    (* move=> [].
    + move=> H; move: (run_or_correct_left H s2 B) => [altB1 H1]; eexists; apply H1.
    + move=> [] FA [] H1 H2. ; move: (run_or_correct_right H1 H2); exists B'.
  Qed. *)
  (* Admitted. *)

  (* Lemma run_and_done {s A B SOL r}:
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
  Qed. *)

  (* Lemma run_run_classic_failure {s A} : 
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
  Qed.  *)
End RunP.
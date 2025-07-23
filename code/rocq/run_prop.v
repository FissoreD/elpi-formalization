From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Module RunP (A: Unif).
  Module Run := Run(A).
  Import Run Language.

  Lemma expanded_classic_expanded {s A r}:
    Run.expanded_classic s A r -> Run.expanded s A r.
  Proof. by exists false. Qed.
  
  Lemma run_classic_run {s A r}:
    run_classic s A r -> run s A r.
  Proof. by exists false. Qed.

  Lemma expand_cutr {A s1 r}: expand s1 (cutr A) = r -> is_fail r.
  Proof.
    move=><-; clear.
    elim: A s1 => //.
    - move=> A HA s B HB s1 /=.
      case: ifP=> //.
        have:= HB s1; by case: expand => //[s3 D] /(_ D s3)//.
      have:= HA s1; by case: expand => //[s3 D] /(_ D s3)//.
    - move=> A HA B0 _ B HB s1 /=.
      have:= HA s1; by case: expand => //[s3 D] /(_ D s3)//.
  Qed.

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

  Lemma run_consistent {s A r1 r2 b1 b2}:
    runb s A r1 b1 -> runb s A r2 b2 -> r1 = r2 /\ b1 = b2.
  Proof.
    move=> H; elim: H r2 b2; clear.
    + move=> s s' A B b H r2 b2; inversion 1; subst; have:= expanded_consistent H H1; try congruence.
      by move => -[].
    + move=> s A B b HA HB r b2; inversion 1; subst; have:= expanded_consistent HA H1; try congruence.
      move=> [] [] /[subst2].
      congruence.
    + move=> ????????? H HN HR IH ???; subst; inversion 1; subst; have:= expanded_consistent H H1; try congruence; move=> [] // [] /[subst2].
      + congruence.
      + move: H2; rewrite HN => -[]??;subst.
        by have:= IH _ _ H3 => -[] /[subst2].
  Qed.

  Lemma expanded_Failure_and_Done {s s' A A' A''}:
    expand s A = Failure A' -> expanded s A (Done s' A'') -> False.
  Proof. move=> + []; inversion 2; congruence. Qed.


  Lemma expanded_cut_simpl {pr s1 s2 A}:
    expanded s2 (Goal pr Cut) (Done s1 A) -> A = OK true.
  Proof.
    inversion 1; inversion H1; subst; simpl in *; try congruence.
    move: H2 => /= [] /[subst2].
    inversion H3; subst; simpl in *; congruence.
  Qed.

  (* Lemma next_alt_cut {b s s' A B}: next_alt_aux b s (cutl A) = Some (s', B) -> exists A, B = cutl A.
  Proof.
    elim: A b B s s' => //; clear.
    + move=> A IH s2 B IHB bool C s s'; simpl cutl => /simpl_next_alt_aux_some [|[]].
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

  (* Lemma expanded_cut_done {s s' A B}:
    solved A -> expanded s (cutl A) (Done s' B) -> s = s'.
  Proof.
    remember (cutl _) as CA eqn:HCA.
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

  Lemma expand_solved_solved {s s1 s2 s3 A B C}: 
    expand s A = Solved s1 B -> 
      expand s2 B = Solved s3 C -> B = C /\ s2 = s3.
  Proof.
    elim: A s s1 s2 s3 B C => //.
    + by move=> ??????? [] /[subst2] -[] /[subst2].
    + by move=> ? [] //.
    + move=> A HA s B HB s1 s2 s3 s4 C D.
      move=>/=.
      case:ifP.
        case X: expand => //= + -[]?<-/= => ->; subst.
        case Y: expand => //-[]?<-/=;subst.
        by have[->->]:= HB _ _ _ _ _ _ X Y.
      case X: expand => //= /eqP dA -[]?<-/=; subst.
      have /=/eqP/negbTE-> :=expand_not_dead dA X.
      case Y: expand => //-[]?<-/=;subst.
      by have [->->]:= HA _ _ _ _ _ _ X Y.
    + move=> A HA B0 _ B HB s1 s2 s3 s4 C D.
      move=> /simpl_expand_and_solved [s'[A'[B'[HA' [HB' ->]]]]].
      move=> /simpl_expand_and_solved [s''[A2[B2[HA2 [HB2 ->]]]]].
      have:= HA _ _ _ _ _ _ HA' HA2 => -[]->->.
      by have:= HB _ _ _ _ _ _ HB' HB2 => -[]->->.
  Qed.

  Lemma expand_solved_is_solved {s s1 s2 A B}: expand s A = Solved s1 B -> expand s2 B = Solved s2 B.
  Proof.
    elim: A s s1 s2 B => //.
    + by move=> ????? [] /[subst2].
    + by move=> ? [] //.
    + move=> A HA s B HB s1 s2 s3 C /=.
      case: ifP => [dA|/eqP dAP].
        case X: expand => //= -[??];subst.
        by rewrite /= dA (HB _ _ _ _ X).
      case X: expand => //= -[??];subst.
      have /=/eqP /negbTE -> := expand_not_dead dAP X.
      by rewrite (HA _ _ _ _ X).
    + move=> A HA B0 HB0 B HB s1 s2 s3 C.
      move=>/simpl_expand_and_solved[s'[A'[B'[HA'[HB' ->]]]]]/=.
      by rewrite (HA _ _ _ _ HA') (HB _ _ _ _ HB').
  Qed.

  Lemma expand_solved_expand {s s1 s2 s3 A B C}: 
    expand s A = Solved s2 B -> expanded s1 B (Done s3 C) -> B = C /\ s1 = s3.
  Proof.
    remember (Done _ _) as D eqn:HD => + [b H].
    elim: H s s2 s3 A C HD => //; clear.
    + move=> s s' A B + s1 s2 s3 C D [??]; subst.
      move=> H1 H3.
      by have:= expand_solved_solved H3 H1.
    + move=> s s1 r A B ? + HB IH s2 s3 s4 C D? HC;subst.
      have:= expand_solved_is_solved HC => /(_ s) HA'.
      by rewrite HA'.
    + move=> s s1 r A B ? + HB IH s2 s3 s4 C D? HC;subst.
      have:= expand_solved_is_solved HC => /(_ s) HA'.
      by rewrite HA'.
  Qed.

  Definition get_backup_and s := match s with And _ B0 _ => B0 | _ => KO end.

  Fixpoint same_structure A B :=
    match A with
    | And A1 B0 B1 =>
      match B with 
      | And A' B0' B' => [&& B0 == B0', same_structure A1 A' & same_structure B1 B']
      | _ => false
      end
    | Or A1 s B1 =>
      match B with 
      | Or A' s' B' => [&& s == s', same_structure A1 A' & same_structure B1 B']
      | _ => false
      end
    | _ => true
    end.

  Lemma same_structure_id {A}: same_structure A A.
  Proof. 
    elim: A => //=.
      by move=>?->??->; rewrite eqxx.
    by move=> ?->? _?->; rewrite eqxx.
  Qed.

  Lemma same_structure_cut {A B}: same_structure A B -> same_structure A (cutl B).
  Proof. 
    elim: A B => //=.
      by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
    by move=> A HA B0 _ B HB []//A' B0' B'/=/and3P[/eqP<-]/HA->->; rewrite eqxx.
  Qed.

  Lemma same_structure_cutr {A B}: same_structure A B -> same_structure A (cutr B).
  Proof. 
    elim: A B => //=.
      by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
    by move=> A HA B0 _ B HB []//A' B0' B'/=/and3P[/eqP<-]/HA->->; rewrite eqxx.
  Qed.

  Lemma same_structure_trans {A B C}: 
    same_structure A B -> same_structure B C -> same_structure A C.
  Proof.
    elim: A B C => //.
      move=> A HA s B HB []// A1 s1 B1 /= []// A2 s2 B2.
      move=>/and3P[/eqP<- ssA ssB]/and3P[/eqP<- ssA1 ssB2].
      by rewrite eqxx (HA A1 A2)//(HB B1 B2)//.
    move=> A HA B0 _ B HB []// A1 B01 B1[]// A2 B02 B2/=.
    move=>/and3P[/eqP<- ssA ssB]/and3P[/eqP<- ssA1 ssB2].
      by rewrite eqxx (HA A1 A2)//(HB B1 B2)//.
  Qed.

  Lemma expand_same_structure {s A r}: 
    expand s A = r -> same_structure A (get_state r).
  Proof.
    elim: A s r => //.
      move=> A HA s B HB s1 [s2|s2||s2] C.
      - move=> /simpl_expand_or_expanded => -[].
          by move=> [A'[dA[HA'->]]]/=; rewrite same_structure_id eqxx (HA _ _ HA').
        move=>[].
          move=> [A'[dA[HA'->]]]/=; rewrite eqxx (HA _ _ HA') same_structure_cutr//same_structure_id//.
        by move=>[->[B'[[]]]]/HB/=+->=>->; rewrite eqxx same_structure_id.
      - move=> /simpl_expand_or_cut [B'[->[HB'->]]]/=.
        by rewrite eqxx same_structure_id (HB _ _ HB').
      - move=> /simpl_expand_or_fail [].
          by move=>[A'[_[HA'->]]]/=; rewrite eqxx (HA _ _ HA') same_structure_id.
        by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
      - move=> /simpl_expand_or_solved[].
          by move=>[A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
        by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
    move=> A HA B0 _ B HB s1 [s2|s2||s2]C.
    - move=> /simpl_expand_and_expanded[].
        by move=>[A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
      by move=> [s'[A'[B' [HA'[HB' ->]]]]]/=; rewrite eqxx (HA _ _ HA') (HB _ _ HB').
    - move=> /simpl_expand_and_cut[].
        by move=>[A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
      by move=>[s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite eqxx (HB _ _ HB') same_structure_cut// (HA _ _ HA').
    - move=> /simpl_expand_and_fail[].
        by move=> [A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
      by move=> [s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite eqxx (HA _ _ HA') (HB _ _ HB').
    - by move=> /simpl_expand_and_solved [s'[A'[B'[HA'[HB'->]]]]]/=; rewrite eqxx (HA _ _ HA') (HB _ _ HB').
  Qed.

  Lemma expanded_same_structure {s A r}: 
    expanded s A r -> same_structure A (get_state_run r).
  Proof.
    move=> [b H].
    elim: H; clear => /=.
    + move=> s1 s2 A B.
      apply: expand_same_structure.
    + move=> ???; apply: expand_same_structure.
    + move=> ??????/expand_same_structure/= + _.
      apply: same_structure_trans.
    + move=> ??????/expand_same_structure/= + _.
      apply: same_structure_trans.
  Qed.

  Lemma expanded_success_same_subst {s A s1 A2}: 
    success A -> expanded s A (Done s1 A2) -> s = s1 /\ A = A2.
  Proof.
    remember (Done _ _) as d eqn:Hd.
    move=> + [b H].
    elim: H s1 A2 Hd; clear => //.
    - move=> s1 s2 A B H s3 C [??] SA; subst.
      have := succes_is_solved s1 SA.
      by rewrite H => -[]??;subst.
    - move=> s1 s2 r A B b H1 H2 IH s3 C? SA; subst.
      have := succes_is_solved s1 SA; congruence.
    - move=> s1 s2 r A B b H1 H2 IH s3 C? SA; subst.
      have := succes_is_solved s1 SA; congruence.
    Qed.

  Lemma expanded_and_complete {s s' C A B0 B} :
    expanded s (And A B0 B) (Done s' C) ->
      (exists s'' A' B', expanded s A (Done s'' A') /\ expanded s'' B (Done s' B')).
  Proof.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => -[b H].
    elim: H A B0 B C Hg0 s' Hs1; clear => //.
    - move=> s s' AB alt + A B0 B alt' ? s'' [] ??; subst.
      move=> /simpl_expand_and_solved. 
      move => [s' [A' [B']]] => -[H1 [H2 H3]]; subst.
      do 3 eexists; repeat split; eexists; apply: expanded_done; eassumption.
    - move=> s s' r A B ? + HB IH A1 B01 B1 C ? s2 ?; subst.
      move=> /simpl_expand_and_cut [].
        move=> [A'[HA']]?;subst.
        have:= IH _ _ _ _ erefl _ erefl.
        move=> [s3 [A2 [B2 [[? HA1] HB2]]]].
        do 3 eexists; repeat split.
          eexists; apply: expanded_cut HA' HA1.
        apply HB2.
      move=> [s'' [A' [B' [HA'[HB' ?]]]]]; subst.
      have {IH} := IH _ _ _ _ erefl _ erefl.
      move=> /= [s3 [A2 [B2 [EA2 [b1 EB2]]]]].
      have [_ +]:= expand_solved_success HA'.
      rewrite -success_cut.
      move=> scA1.
      have /=[??] := expanded_success_same_subst scA1 EA2.
      subst.
      do 3 eexists; split.
        eexists; apply: expanded_done HA'.
      eexists; apply: expanded_cut HB' EB2.
    - move=> s1 s2 r ? D b + H IH A B0 B C ? s3 ?; subst.
      move=> /simpl_expand_and_expanded [].
        move=> [A' [EA ?]];subst.
        have:= IH _ _ _ _ erefl _ erefl.
        move=> [s' [A2 [B2 [[b1 HA'] HB']]]].
        do 3 eexists; repeat split => //=.
          eexists.
          apply: expanded_step EA HA'.
        apply: HB'.
      move=> [s4 [A' [B' [EA' [EB' ?]]]]]; subst.
      have:= IH _ _ _ _ erefl _ erefl.
      move=> [s''[A1[B1[HA2 [b1 HB2]]]]].
      have [_ sA']:= expand_solved_success EA'.
      have /= [??] := expanded_success_same_subst sA' HA2.
      subst.
      do 3 eexists; repeat split; eexists.
        apply: expanded_done EA'.
      apply: expanded_step EB' HB2.
  Qed.

  Lemma expanded_and_correct {s0 s1 s2 A C B0 B D x} :
      expanded s0 A (Done s1 B) -> expandedb s1 C (Done s2 D) x ->
        expanded s0 (And A B0 C) (Done s2 (And (if x then cutl B else B) B0 D)).
  Proof.
    remember (Done _ _) as RD eqn:HRD => -[b H].
    elim: H s1 s2 C B0 B D HRD x => //=; clear.
    + move=> s1 s2 A B + s3 s4 C D E F [??] b H;subst.
      remember (Done s4 F) as RD eqn:HRD.
      elim: H s1 A s4 D E F HRD => //=; clear.
      + move=> s1 s2 A A' HA s4 B s3 D B' ? [<-<-] HB.
        eexists; apply: expanded_done => /=; by rewrite HB HA.
      + move=> s s' r A B b HA HB IH s2 C s3 D E F? HC;subst.
        have [_ +] := expand_solved_success HC.
        rewrite -success_cut => H.
        have /= H1 := succes_is_solved _ H.
        have /= [b1 {}IH] := IH _ _ _ D _ _ erefl (H1 _).
        rewrite cut_cut_same in IH.
        eexists; apply: expanded_cut => //=.
          rewrite HC HA => //=.
        destruct b; apply: IH.
      + move=> s1 s2 r A B b HA HB IH s3 C s4 F0 D F ? HC; subst.
        have HC':= expand_solved_is_solved HC.
        have [b1 {}IH] := IH s2 D _ F0 D _ erefl (HC' _).
        eexists.
        apply: expanded_step => /=.
          by rewrite HC HA.
        by apply: IH.
    + move=> s s' r A CA ? H H1 IH ?? ? B0 ?? /[subst1] b H2.
      have [b1 {}IH]:= IH _ _ _ B0 _ _ erefl _ H2.
      eexists; apply: expanded_cut => //=.
        by rewrite H.
      by apply: IH.
    + move=> s s' r A CA ? H H1 IH ?? ? B0 ?? /[subst1] b H2.
      have [b1 {}IH]:= IH _ _ _ B0 _ _ erefl _ H2.
      eexists; apply: expanded_step => //=.
        by rewrite H.
      by apply: IH.
  Qed.

  Lemma success_is_not_failed {s A r}: 
    success A -> expanded s A r -> is_failed r = false.
  Proof. 
    move=> SA [b H]; inversion H; subst; by have //:= succes_is_solved s SA; congruence. 
  Qed.

  Lemma expandes_and_fail {s A B0 B C}:
    expanded s (And A B0 B) (Failed C) ->
      (exists C', expanded s A (Failed C')) \/ (exists s' A' B', expanded s A (Done s' A') /\ expanded s' B (Failed B')).
  Proof.
    remember (And _ _ _) as R eqn:HR.
    remember (Failed _) as F eqn:HF => -[b H].
    elim: H A B0 B C HR HF => //=; clear.
    + move=> ??? + ???? ? [] ?;subst => /simpl_expand_and_fail [].
        move=>[A'[HA' _]].
        left; do 2 eexists; apply: expanded_fail HA'.
      move=> [s'[A'[B'[HA'[HB' _]]]]].
      right; do 3 eexists; split.
        eexists; apply: expanded_done HA'.
      eexists; apply: expanded_fail HB'.
    + move=> s s' r A B b + HB IH C D E F ??; subst.
      move=> /simpl_expand_and_cut[].
        move=>[A'[HA' ?]];subst.
        have [] := IH _ _ _ _ erefl erefl.
          move=> [C' [b1 {}HA]].
          left; do 2 eexists; apply: expanded_cut HA' HA.
        move=>[s1[A1[B2[[b1 HA2] HB2]]]].
        right; do 3 eexists; split; [|eassumption]; eexists; apply: expanded_cut HA' HA2.
      move=> [s2 [A2 [B' [H[H2]]]]] /[subst1].
      have [] := IH _ _ _ _ erefl erefl.
        move=> [? [b1 H3]].
        have [_ +]:= expand_solved_success H.
        rewrite -success_cut => scA2.
        by have /= := success_is_not_failed scA2 (ex_intro _ _ H3).
      move=> [] s'' [] altA [] ? [] H4 [? H5].
      right.
      have [_ +]:= expand_solved_success H.
      rewrite -success_cut => scA2.
      have /= H6 := succes_is_solved s' scA2.
      have [??]:= expand_solved_expand H6 H4; subst.
      do 3 eexists; split.
        eexists; apply: expanded_done H.
      eexists; apply: expanded_cut H2 H5.
    + move=> s s' r A B b + H1 IH A1 B1 C1 D1 ??;subst.
      move=> /simpl_expand_and_expanded [].
        move=> [A'' [HA'']] /[subst1].
        have []:= IH _ _ _ _ erefl erefl.
          move=> [? [? H]]; left; do 2  eexists; apply: expanded_step HA'' H.
        move=> [] ? [] altA [] ? [] [? H2] [? H3].
        right; repeat eexists; [apply: expanded_step HA'' H2|apply H3].
      move=> [s2 [A2 [B' [H2 [H3]]]]] /[subst1].
      have [] := IH _ _ _ _ erefl erefl.
        move=> [? H].
        by have:= success_is_not_failed (proj2 (expand_solved_success H2)) H.
      move=> [] ? [] altA [] ? [] H4 [? H5]; right.
      have:= expand_solved_expand H2 H4 => -[] /[subst2].
      do 3 eexists; split.
        eexists; apply: expanded_done H2.
      eexists; apply: expanded_step H3 H5.
  Qed.

  Lemma expanded_and_fail_left {s A B0 FA}:
    expanded s A (Failed FA) ->
      forall B, expanded s (And A B0 B) (Failed (And FA B0 B)).
  Proof.
    move=> [? H].
    remember (Failed _) as F eqn:HF.
    elim: H FA B0 HF => //=; clear.
    + move=> s A H H1 FA ? [] /[subst1] ?.
      eexists; apply: expanded_fail => //=; rewrite H1.
      case: FA {H1} => //.
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

  Lemma run_and_fail_both {s s' A B B0 SA FB b}:
    expanded s A (Done s' SA) -> expandedb s' B (Failed FB) b ->
      expanded s (And A B0 B) (Failed (And (if b then cutl SA else SA) B0 FB)).
  Proof.
    move=> [b1 H].
    remember (Done _ _) as D eqn:HD.
    elim: H B s' SA HD b => //=; clear.
    + move=> s1 s2 A B HA C s3 D [??] b H; subst.
      remember (Failed _) as F eqn:HF.
      elim: H B0 FB s1 A D HA HF; clear => //.
      + move=> s A ? H ????? EA [] /[subst1].
        eexists; apply: expanded_fail => //= ; rewrite EA H //=.
      + move=> s s' r A B b HA HB IH B0 F s1 C D HC ?;subst.
        have H := succes_is_solved s' (success_cut1 (proj2 (expand_solved_success HC))).
        have [b' H1 ]:= IH B0 F s' (cutl D) (cutl D) H erefl.
        rewrite cut_cut_same if_same in H1.
        eexists; apply: expanded_cut => /=.
          by rewrite HC HA.
        apply: H1.
      + move=> s s' r A B b HA HB IH B0 F s1 C D HC ?;subst.
        have [b1 H1] := IH B0 F s' D D (succes_is_solved s' ((proj2 (expand_solved_success HC)))) erefl.
        eexists; apply: expanded_step => /=.
          by rewrite HC HA.
        apply: H1.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? b H2; subst => //=.
      have [b1 H3] := IH _ _ _ erefl b H2.
      eexists;apply: expanded_cut => /=.
        by rewrite H.
      by apply H3.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? b H2; subst => //=.
      have [b1 H3] := IH _ _ _ erefl b H2.
      eexists;apply: expanded_step => /=.
        by rewrite H.
      by apply H3.
  Qed.

  Lemma expanded_or_correct_left {s s' A A'} b:
    expandedb s A (Done s' A') b ->
      forall s2 B, expanded s (Or A s2 B) (Done s' (Or A' s2 (if b then cutr B else B))).
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A' HD => //=; clear.
    + move=> s s' A A' HA s2 B [] ?? s3 C; subst.
      eexists; apply: expanded_done => //= ; rewrite HA.
      case: ifP => ///eqP H.
      by rewrite (expand_dead H) in HA.
    + move=> s1 s2 r A B b HA HB IH s3 C ? s4 D /[subst].
      have /= [? {IH}]:= IH _ _ erefl s4 (cutr D).
      rewrite cutr2_same if_same => IH.
      eexists; apply: expanded_step => //=.
        case: ifP => ///eqP dA.
          by rewrite (expand_dead dA) in HA.
        by rewrite HA.
      apply: IH.
    + move=> s1 s2 r A B b HA HB IH s' C ? s4 D /[subst].
      have [? {}IH] := IH _ _ erefl s4 D.
      eexists; apply: expanded_step => //=.
        case: ifP=>/eqP dA.
          by rewrite (expand_dead dA) in HA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma expanded_or_complete_left {s s' s2 A A' B B'} b:
    expandedb s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
      (A <> dead A /\ exists b, expandedb s A (Done s' A') b /\ B' = if b then cutr B else B) \/ 
        (A = dead A /\ expanded s B (Done s' B')).
  Proof.
    rewrite /expanded.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s' s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 s3 C D + A B HRO ???? [] ??; subst.
      move=> /simpl_expand_or_solved [].
        move=> [A2 [HA']] [??];subst.
        have dA := success_dead1 (proj1 (expand_solved_success HA')).
        left; repeat split => //.
        exists false; split => //; apply: expanded_done HA'.
      move=> [B' [dA [HB' [??]]]];subst.
      right; repeat split; auto; eexists.
      apply: expanded_done HB'.
    + move=> s s1 r C D b2 + HB IH s' s2 A' B' A B ??; subst. 
      move=> /simpl_expand_or_cut.
      move=> [B2[dB1[HB' ?]]]; subst.
      have:= IH _ _ _ _ _ _ erefl erefl.
      move=> [[]|]// [_ [b H]].
      right; repeat split; auto; eexists.
      apply: expanded_cut HB' H.
    + move=> s s1 r C D b2 + HB IH s' s2 A' B' A B ??; subst. 
      move=> /simpl_expand_or_expanded[].
        move=> [A2 [dA [HA ?]]]; subst.
        have := IH _ _ _ _ _ _ erefl erefl.
        have /= dA2:= expand_not_dead dA HA.
        move=> [][]// _ [b1[H1 ?]]; subst.
        left; repeat eexists => //.
        apply: expanded_step HA H1.
      move=> [].
        move=>[A1[dA[HA?]]]; subst.
        have := IH _ _ _ _ _ _ erefl erefl.
        have /= dA2:= expand_not_dead dA HA.
        move=> [][]// _ [b1 [H1 ?]]; subst.
        rewrite cutr2_same if_same.
        left; repeat eexists => //.
          apply: expanded_cut HA H1.
        by [].
      move=> [dA [B1 [HB1]]]?;subst.
      have := IH _ _ _ _ _ _ erefl erefl.
      move=> [][]// _ [b H]; right.
      move: HB1 => [] HB1.
        repeat eexists => //.
        apply: expanded_step HB1 H.
      repeat eexists => //.
      apply: expanded_cut HB1 H.
  Qed.
  
  Lemma expanded_or_complete {s s1 s2 A A' B B'}:
    A <> dead A ->
    (* TODO: the two call to expanded should return the same bool... *)
    expanded s (Or A s2 B) (Done s1 (Or A' s2 B')) ->
      exists b, expandedb s A (Done s1 A') b /\ B' = if b then cutr B else B.
  Proof.
    remember (Or _ _ _) as RO eqn:HRO.
    remember (Done _ _) as RD eqn:HRD => + [b H].
    elim: H s1 s2 A A' B B' HRD HRO => //; clear.
    + move=> s s' A A' + ss1 s2 A1 A2 B B' [] ??? dA1; subst.
      move => /simpl_expand_or_solved [].
        move=> [A'[HA' [??]]]; subst.
        repeat eexists; [apply: expanded_done|] => //.
      move=> [B1[dA]]//.
    + move=> s s' r A0 B0 b + H IH s1 s2 A A' B B' ?? dA;subst.
      move=> /simpl_expand_or_cut.
      move=> [B2 []]//.
    + move=> s s' r A0 B0 b + H IH s1 s2 A A' B B' ?? dA; subst.
      move=> /simpl_expand_or_expanded[].
        move=>[A1[? [HA1 ?]]]; subst.
        have:= IH _ _ _ _ _ _ erefl erefl (expand_not_dead dA HA1).
        move=> [b1 [H1 ->]]; repeat eexists.
        apply: expanded_step HA1 H1.
      move=>[].
        move=>[A1 [? [HA1 ?]]]; subst.
        have:= IH _ _ _ _ _ _ erefl erefl (expand_not_dead dA HA1).
        move=> [b1 [H1 H2]].
        rewrite cutr2_same if_same in H2; subst.
        repeat eexists.
          apply: expanded_cut HA1 H1.
        by [].
      move=> []//.
  Qed.

  Lemma expanded_or_correct_left_fail {s A A'} b:
    A <> dead A ->
    expandedb s A (Failed A') b ->
      forall s2 B, expanded s (Or A s2 B) (Failed (Or A' s2 (if b then cutr B else B))).
  Proof.
    remember (Failed _) as D eqn:HD => + H.
    elim: H A' HD => //=; clear.
    + move=> s A A' HA B [] ? s3 C; subst.
      eexists; apply: expanded_fail => /=.
      rewrite HA.
      case: ifP => /eqP => //.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH]:= IH _ erefl (expand_not_dead dA HA) s4 (cutr D).
      eexists; apply: expanded_step => //=.
      case: ifP => /eqP // _.
      + by rewrite HA.
      + move: IH; rewrite cutr2_same if_same => H; eassumption.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH] := IH _ erefl (expand_not_dead dA HA) s4 D.
      eexists; apply: expanded_step => //=.
      case: ifP => /eqP // _.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma run_or_correct_left {s1 A s2 A' b sB B}:
    runb s1 A (Done s2 A') b ->
      B <> dead B -> run s1 (Or A sB B) (Done s2 (Or A' sB (if b then cutr B else B))).
  Proof.
    remember (Done _ _) as rD eqn:HrD => H.
    elim: H s2 A' sB B HrD => //; clear.
    + move=> s s' A B b H s2 A' sB B' [??]; subst.
      have [? H1]:= expanded_or_correct_left _ H sB B'.
      eexists.
      apply: run_done H1.
    + move=> s s' r A B C b1 b2 b3 HE HN HR IH ? s2 D sB E ? dE;subst.
      case: (A =P dead A) => dA.
        have H := expanded_dead s dA.
        have [[?]?] := expanded_consistent H HE; subst.
        by rewrite dA next_alt_dead1 in HN.
      have /= dB := expanded_not_dead dA HE.
      have:= expanded_or_correct_left_fail _ dA HE sB E.
      have cdE : cutr E <> dead (cutr E).
        rewrite dead_cutr_is_dead.
        by move=> /cutr_dead1/esym.
      have [b H] := IH _ _ sB (cutr E) erefl cdE.
      rewrite cutr2_same if_same in H.
      have [b3 H2] := IH _ _ sB E erefl dE.
      have H3 := next_alt_or_some HN.
      case: b1 HE => //=; move=> H1 [b4 H4]/=;
        eexists; apply: run_backtrack H4 (H3 _ _ _) _ erefl; 
        eassumption.
  Qed.

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
      run s (Or A s2 (cutl B)) Failed.
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
      run s1 g1 Failed -> expand s1 g1 = CutBrothers g3 -> (* g1 coulbe not an immediate cutl, but expand... to a cutl *)
        run s1 (Or g1 s2 g2) Failed.
  Proof.
    move=> H H1; apply: run_or_fail1 H _ => H2.
    inversion H2; subst; congruence.
  Qed.  *)

  Lemma expandedb_failed {s1 A B b1}: expandedb s1 A (Failed B) b1 -> failed B.
  Proof.
    remember (Failed B) as fB eqn:HfB => H.
    elim: H B HfB => //; clear.
    move=> s1 A B H C []<-.
    have []:= expand_failure_failed H => //.
  Qed.
End RunP.
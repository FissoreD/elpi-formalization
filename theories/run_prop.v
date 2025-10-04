From mathcomp Require Import all_ssreflect.
From det Require Import run.

Module RunP (A: Unif).
  Module Run := Run(A).
  Import Run Language.

  Lemma expanded_classic_expanded {s A r}:
    Run.expanded_classic s A r -> Run.expanded s A r.
  Proof. by exists false. Qed.
  
  Lemma run_classic_run {s A s1 B}:
    run_classic s A s1 B -> run s A s1 B.
  Proof. by exists false. Qed.

  Lemma run_classic_cut {s s2 A B s3 C}:
    run_classic s A s3 C -> expand s A = CutBrothers s2 B -> False.
  Proof.
    rewrite /run_classic; remember false as f eqn:Hf => H.
    elim: H s2 B Hf; clear.
    + inversion 1; congruence.
    + move=> s1 s2 r A A' B C b1 b2 b3 HE HN HR IH + s4 A2 /[subst1] +.
      destruct b1, b2 => // _ HC.
      inversion HE; congruence.
  Qed.

  Lemma run_Solved_id {s s1 A r alt}:
      expand s A = Success s1 alt -> expanded s A r -> r = Done s1 alt.
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

  Lemma run_consistent {s A s1 B b1}:
    runb s A s1 B b1 -> forall {s2 C b2}, runb s A s2 C b2 -> s1 = s2 /\ B = C /\ b1 = b2.
  Proof.
    move=> H; elim: H; clear.
    + move=> s s' A B C b H -> s2 D b2 H1.
      inversion H1; clear H1; subst;
        by have:= expanded_consistent H H0 => -[] // [->->]->.
    (* + move=> s A B b HA HB r b2 H1.
      inversion H1; clear H1; subst => //; have []:= expanded_consistent HA H0; try congruence.
      by move=> [_ <-]. *)
    + move=> s s1 s2 A B C D b1 b2 b3 HA HB HC IH ? s3 E s4 H1; subst.
      inversion H1; subst; have [] := expanded_consistent HA H0 => //.
      move=>[??]; subst.
      move: H2; rewrite HB => -[??]; subst.
      by have:= IH _ _ _ H3 => -[?[??]]; subst.
  Qed.

  Lemma expand_solved_expand {s s1 s2 s3 A B C}: 
    expand s A = Success s2 B -> expanded s1 B (Done s3 C) -> B = C /\ s1 = s3.
  Proof.
    move=>/expand_solved_success[_ sB][v].
    move=>/expanded_success => /(_ sB)[][]//.
  Qed.

  Section same_structure.

    Fixpoint same_structure A B :=
      match A with
      | And A1 B0 B1 =>
        match B with 
        | And A' B0' B' => [&& same_structure B0 B0', same_structure A1 A' & same_structure B1 B']
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
      by move=> ?->? ->?->.
    Qed.

    Lemma same_structure_trans: transitive same_structure.
    Proof.
      move=> + A; elim: A => //.
      - move=> A HA s B HB []//A' s' B'[]//A2 s2 B2/=.
        move=>/and3P[/eqP<-HA' HB']/and3P[/eqP<-HA2 HB2].
        rewrite eqxx (HA A' A2)//(HB B' B2)//.
      - move=> A HA B0 HB0 B HB[]//A1 B01 B1[]//A2 B02 B2/=.
        move=>/and3P[HA1 HB01 HB1]/and3P[HA2 HB02 HB2].
        rewrite (HA A1 A2)//(HB B1 B2)//(HB0 B01 B02)//.
    Qed.

    Lemma same_structure_cutr {A B}: same_structure A B -> same_structure A (cutr B).
    Proof. 
      elim: A B => //=.
        by move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<-/HA->/HB->]; rewrite eqxx.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=/and3P[/HB0-> /HA-> /HB->]//.
    Qed.
    
    Lemma same_structure_cut {A B}: same_structure A B -> same_structure A (cutl B).
    Proof. 
      elim: A B => //=.
        move=> A HA s B HB []// A' s' B' /= /and3P[/eqP<- H2 H3].
        case: ifP => //.
          by rewrite H2 HB//eqxx.
        by rewrite eqxx HA// same_structure_cutr//.
      move=> A HA B0 HB0 B HB []//A' B0' B'/=. 
      move=> /and3P[sB0 sA sB].
      rewrite HA//HB0//HB//.
    Qed.
    
    Lemma same_structure_dead {B}: same_structure B (dead1 B).
    Proof. 
      elim: B => //=.
        move=> A HA s B HB; rewrite eqxx HA HB//.
      move=> A HA B0 HB0 B HB; rewrite HA HB0 HB//.
    Qed.

    Lemma expand_same_structure {s A r}: 
      expand s A = r -> same_structure A (get_state r).
    Proof.
      elim: A s r => //.
        move=> A HA s B HB s1 [s2|s2||s2] C.
        - move=> /=.
          case: ifP => dA.
            case eB: expand => //[s1' B'|s1' B'][_<-]; rewrite eqxx same_structure_id (HB _ _ eB)//.
          case eA: expand => //[s1' A'|s1' A'][_<-]; rewrite eqxx (HA _ _ eA)?same_structure_id// same_structure_cutr//same_structure_id//.
        - move=> /=; case: ifP => dA; case: expand => //.
        - move=> /simpl_expand_or_fail [].
            by move=>[A'[_[HA'->]]]/=; rewrite eqxx (HA _ _ HA') same_structure_id.
          by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
        - move=> /simpl_expand_or_solved[].
            by move=>[A'[HA'->]]/=; rewrite eqxx same_structure_id (HA _ _ HA').
          by move=> [B'[_ [HB'->]]]/=; rewrite eqxx same_structure_id (HB _ _ HB').
      move=> A HA B0 HB0 B HB s1 [s2|s2||s2]C.
      - move=> /simpl_expand_and_expanded[].
          by move=>[A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        by move=> [s'[A'[B' [HA'[HB' ->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
      - move=> /simpl_expand_and_cut[].
          by move=>[A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        move=>[s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite (HB _ _ HB')//(same_structure_cut same_structure_id).
        by have:= (HA _ _ HA') => /same_structure_cut->.
      - move=> /simpl_expand_and_fail[].
          by move=> [A'[HA'->]]/=; rewrite !same_structure_id (HA _ _ HA').
        by move=> [s'[A'[B'[HA'[HB' ->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
      - by move=> /simpl_expand_and_solved [s'[A'[B'[HA'[HB'->]]]]]/=; rewrite (HA _ _ HA') (HB _ _ HB') same_structure_id.
    Qed.

    Lemma expandedb_same_structure {s A r b}: 
      expandedb s A r b -> same_structure A (get_state_exp r).
    Proof.
      move=> H; elim: H; clear => /=.
      + move=> s1 s2 A B.
        apply: expand_same_structure.
      + move=> ???; apply: expand_same_structure.
      + move=> ??????/expand_same_structure/= + _.
        apply: same_structure_trans.
      + move=> ??????/expand_same_structure/= + _.
        apply: same_structure_trans.
    Qed.

    Lemma same_structure_clean_success {A}:
      same_structure A (clean_success A).
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=; case: ifP => //_; rewrite ?HA?HB same_structure_id eqxx//.
      - move=> A HA B0 _ B HB/=; case: ifP => _; rewrite !same_structure_id//?HA//.
    Qed.
  End same_structure.
  

  Lemma expanded_and_complete {s s' C A B0 B b} :
    expandedb s (And A B0 B) (Done s' C) b ->
      exists s'' A' B' b1 b2, expandedb s A (Done s'' A') b1 /\ expandedb s'' B (Done s' B') b2 /\ b = b1 || b2.
  Proof.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => H.
    elim: H A B0 B C Hg0 s' Hs1; clear => //.
    - move=> s s' AB alt + A B0 B alt' ? s'' [] ??; subst.
      move=> /simpl_expand_and_solved. 
      move => [s' [A' [B']]] => -[H1 [H2 H3]]; subst.
      do 3 eexists; exists false, false; repeat split; apply: expanded_done; eassumption.
    - move=> s s' r A B b + HB IH A1 B01 B1 C ? s2 ?; subst.
      move=> /simpl_expand_and_cut [].
        move=> [A'[HA']]?;subst.
        have := IH _ _ _ _ erefl _ erefl.
        move=> [s''[A2[B2[b1[b2 [HA1 HB2]]]]]].
        (* move=> [s3 [A2 [B2 [[? HA1] HB2]]]]. *)
        do 5 eexists; repeat split.
        - apply: expanded_cut HA' HA1.
        - apply HB2.
        - reflexivity.
      move=> [s'' [A' [B' [HA'[HB' ?]]]]]; subst.
      have {IH} := IH _ _ _ _ erefl _ erefl.
      move=> /= [s3 [A2 [B2 [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
      have [_ +]:= expand_solved_success HA'.
      move=>/success_cut.
      move=> scA1.
      have[[??]?] := expanded_success scA1 EA2; subst.
      do 5 eexists; repeat split.
      - apply: expanded_done HA'.
      - apply: expanded_cut HB' EB2.
      - reflexivity.
    - move=> s1 s2 r ? D b + H IH A B0 B C ? s3 ?; subst.
      move=> /simpl_expand_and_expanded [].
        move=> [A' [EA ?]];subst.
        have:= IH _ _ _ _ erefl _ erefl.
        move=> /= [s4 [A2 [B2 [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
        do 5 eexists; repeat split => //=.
          apply: expanded_step EA EA2.
        apply: EB2.
      move=> [s4 [A' [B' [EA' [EB' ?]]]]]; subst.
      have:= IH _ _ _ _ erefl _ erefl.
      move=> /= [s5 [A2 [B2 [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
      have [_ sA']:= expand_solved_success EA'.
      have /= [[??]?] := expanded_success sA' EA2; subst.
      subst.
      do 5 eexists; repeat split.
        apply: expanded_done EA'.
      apply: expanded_step EB' EB2.
  Qed.

  Lemma expand_success_done {A B0 s1 B s2 B' b}: 
    success A -> expandedb s1 B (Done s2 B') b ->
      expanded s1 (And A B0 B) 
        (Done s2 (And (if b then cutl A else A) (if b then cutl B0 else B0) B')).
  Proof.
    remember (Done _ _) as RD eqn:HRD => + H.
    elim: H A B0 s2 B' HRD => //; clear.
    - move=> s s' A A' H A0 B0 _ _ [<-<-] sA0.
      exists false.
      apply: expanded_done.
      rewrite /= (succes_is_solved _ sA0) H//.
    - move=> s s' r A B b HA HB IH A0 B0 s2 C? sA0; subst.
      exists true.
      have [b1 {}IH]:= IH _ (cutl B0) _ _ erefl (success_cut sA0).
      rewrite !cutl2 !if_same in IH.
      apply: expanded_cut.
      move=>/=; rewrite (succes_is_solved _ sA0) HA//.
      apply: IH.
    - move=> s s' r A B b HA HB IH A0 B0 s2 C ? sA0; subst.
      have [b1 H]:= IH A0 B0 _ _ erefl sA0.
      eexists.
      apply: expanded_step.
        rewrite /= (succes_is_solved _ sA0) HA//.
      apply H.
  Qed.

  (* This can be factored with the previous proof... *)
  Lemma expand_success_fail {A B0 s1 B B' b}: 
    success A -> expandedb s1 B (Failed B') b ->
      expandedb s1 (And A B0 B) 
        (Failed (And (if b then cutl A else A) (if b then cutl B0 else B0) B')) b.
  Proof.
    remember (Failed _) as RD eqn:HRD => + H.
    elim: H A B0 B' HRD => //; clear.
    - move=> s A A' HA X B0 _ [<-] sX.
      apply: expanded_fail.
      rewrite /= (succes_is_solved _ sX) HA//.
    - move=> s s' r A B b HA HB IH A0 B0 C? sA0; subst.
      have {}IH := IH _ (cutl B0) _ erefl (success_cut sA0).
      rewrite !cutl2 !if_same in IH.
      apply: expanded_cut.
      move=>/=; rewrite (succes_is_solved _ sA0) HA//.
      apply: IH.
    - move=> s s' r A B b HA HB IH A0 B0 C ? sA0; subst.
      have {}IH := IH A0 B0 _ erefl sA0.
      apply: expanded_step.
        rewrite /= (succes_is_solved _ sA0) HA//.
      apply IH.
  Qed.

  Lemma expanded_and_correct {s0 s1 s2 A C B0 B D x} :
      expanded s0 A (Done s1 B) -> expandedb s1 C (Done s2 D) x ->
        expanded s0 (And A B0 C) 
          (Done s2 (And (if x then cutl B else B) (if x then cutl B0 else B0) D)).
  Proof.
    remember (Done _ _) as RD eqn:HRD => -[b H].
    elim: H s1 s2 C B0 B D HRD x => //=; clear.
    + move=> s1 s2 A B eA s3 s4 C D E F [??] b;subst.
      have [??]:= expand_solved_same eA; subst.
      have:= (expand_solved_success eA).1.
      apply: expand_success_done.
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
        move=>/success_cut scA2.
        by have [] /= := expanded_success scA2 H3.
      move=> [] s'' [] altA [] ? [] H4 [? H5].
      right.
      have [_ +]:= expand_solved_success H.
      move=>/success_cut scA2.
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
        move=> [? [? H]].
        by have [] := expanded_success (expand_solved_success H2).2 H.
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
      expanded s (And A B0 B) (Failed (And (if b then cutl SA else SA) (if b then cutl B0 else B0) FB)).
  Proof.
    move=> [b1 H].
    remember (Done _ _) as D eqn:HD.
    elim: H B s' SA HD b => //=; clear.
    + move=> s1 s2 A B HA C s3 D [??] b H; subst.
      eexists.
      have H1:= expand_solved_same HA; rewrite 2!H1.
      apply: expand_success_fail (expand_solved_success HA).2 H.
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
      case: ifP => //H.
      by rewrite (is_dead_expand H) in HA.
    + move=> s1 s2 r A B b HA HB IH s3 C ? s4 D /[subst].
      have /= [? {IH}]:= IH _ _ erefl s4 (cutr D).
      rewrite cutr2 if_same => IH.
      eexists; apply: expanded_step => //=.
        case: ifP => // dA.
          by rewrite (is_dead_expand dA) in HA.
        by rewrite HA.
      apply: IH.
    + move=> s1 s2 r A B b HA HB IH s' C ? s4 D /[subst].
      have [? {}IH] := IH _ _ erefl s4 D.
      eexists; apply: expanded_step => //=.
        case: ifP=> dA.
          by rewrite (is_dead_expand dA) in HA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma expanded_or_complete {s s' s2 A A' B B' b}:
    expandedb s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
      (is_dead A = false /\ 
        exists b, expandedb s A (Done s' A') b /\ B' = if b then cutr B else B) \/ 
        (is_dead A /\ A = A' /\ expanded s B (Done s' B')).
  Proof.
    rewrite /expanded.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s' s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 s3 C D + A B HRO ???? [] ??; subst.
      move=> /simpl_expand_or_solved [].
        move=> [A2 [HA']] [??];subst.
        have dA := success_is_dead (expand_solved_success HA').1.
        left; repeat split => //.
        exists false; split => //; apply: expanded_done HA'.
      move=> [B' [dA [HB' [??]]]];subst.
      right; repeat split; auto; eexists.
      apply: expanded_done HB'.
    + move=> s s1 r C D b2 + HB IH s' s2 A' B' A B ??; subst.
      move=> /=; case: ifP => //dA.
        case eB: expand => //[s1' B1'][??]; subst.
      case eA: expand => //.
    + move=> s s1 r C D b2 + HB IH s' s2 A' B' A B ??; subst.
      move=> /=.
      case: ifP => dA.
        case eB: expand => //[s1' B1'|s1' B1'][??]; subst.
          have:= IH _ _ _ _ _ _ erefl erefl; rewrite dA => -[][]// _[->][b H].
          right; repeat eexists; apply: expanded_step eB H.
        have:= IH _ _ _ _ _ _ erefl erefl; rewrite dA => -[][]// _[->][b H].
        right; repeat split; eexists; apply: expanded_cut eB H.
      case eA: expand => //[s1' A1'|s1' A1'][??]; subst; left; repeat split;
        have:= IH _ _ _ _ _ _ erefl erefl => -[][]; 
        rewrite (expand_not_dead dA eA)// => _ [b [H1 H2]]; subst.
        eexists; split => //; apply: expanded_step eA H1.
      eexists; split.
        apply: expanded_cut eA H1.
      move=>/=; rewrite cutr2 if_same//.
  Qed.
  
  Lemma expanded_or_correct_left_fail {s A A'} b:
    is_dead A = false ->
    expandedb s A (Failed A') b ->
      forall s2 B, expanded s (Or A s2 B) (Failed (Or A' s2 (if b then cutr B else B))).
  Proof.
    remember (Failed _) as D eqn:HD => + H.
    elim: H A' HD => //=; clear.
    + move=> s A A' HA B [] ? s3 C; subst.
      eexists; apply: expanded_fail => /=.
      rewrite HA s3//.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH]:= IH _ erefl (expand_not_dead dA HA) s4 (cutr D).
      eexists; apply: expanded_step => //=.
        rewrite dA HA//.
      move: IH; rewrite cutr2 if_same => H; eassumption.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH] := IH _ erefl (expand_not_dead dA HA) s4 D.
      eexists; apply: expanded_step => //=.
      rewrite dA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma run_or_correct_left {s1 A s2 A' b sB B}:
    runb s1 A s2 A' b ->
      run s1 (Or A sB B) s2 (Or A' sB (if b then cutr B else B)).
  Proof.
    move => H.
    elim: H sB B => //; clear.
    + move=> s s' A B C b H -> s2 A'.
      have [? H1]:= expanded_or_correct_left _ H s2 A'.
      eexists.
      apply: run_done H1 _.
      have sB := expanded_Done_success H.
      move=>/=.
      rewrite success_is_dead//.
    + move=> s s' r A B C D b1 b2 b3 HE HN HR IH ? s2 E;subst.
      case dA: (is_dead A).
        have H := is_dead_expanded s dA.
        have [[?]?] := expanded_consistent H HE; subst.
        by rewrite (is_dead_next_alt dA) in HN.
      have /= dB := expanded_not_dead dA HE.
      have [b3 H] := expanded_or_correct_left_fail _ dA HE s2 E.
      (* have {}HN: next_alt s (Or B s2 (if b1 then cutr E else E)) = Some (s', Or C s2 (if b1 then cutr E else E)).
        move=>/=; rewrite ((next_alt_dead HN)) HN//. *)
      have [b4 {}IH1]:= IH s2 E.
      have [b5]:= IH s2 (cutr E).
      rewrite cutr2 if_same => IH2.
      case: b1 H HN {HE} => //=H HN.
        eexists; apply: run_backtrack H _ _ erefl.
        rewrite/=dB HN//.
        apply: IH2.
      eexists; apply: run_backtrack H _ _ erefl.
      rewrite/=dB HN//.
      apply: IH1.
  Qed.

  Lemma run_or_complete {s1 s2 A B SOL altAB}:
    run s1 (Or A s2 B) SOL altAB ->
      (exists altA, run s1 A SOL altA) \/ 
        (exists altB, run s2 B SOL altB).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1.
    move=> [b H].
    elim: H s2 A B HO1 => //=; clear.
    + move=> s st s' alt C b H ? s2 D E ?; subst.
      have /= := expandedb_same_structure H.
      case: alt H => //= D' s2' E' H /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete H.
      move=> [][dD].
        move=> [b'[H1?]]; subst.
        left.
        eexists (clean_success D'), _.
        apply: run_done H1 erefl.
      move=> [?[H1]] H2; subst.
      admit.
    + move=> s s1 s2 A B C D b1 b2 b3 H1 H2 H3 IH ? s4 E F ?; subst.
      have /= := expandedb_same_structure H1.
      case: B H1 H2 => //= D' s2' E' H1 + /and3P[/eqP? _ _]; subst.
      case: ifP => dD'.
        case X: next_alt => //=[[s4 E2]][??]; subst.
        have [[x [b {}IH]]|[x [b{}IH]]] := IH _ _ _ erefl.
          admit.
        left; do 2 eexists.
        apply: run_backtrack _ _ IH erefl.
        admit.
        admit.
      case X: next_alt => //=[[s4 E2]|].
        move=> [??]; subst.
        have [[x [b {}IH]]|[x [b{}IH]]] := IH _ _ _ erefl.
          admit.
        admit.
      case: ifP => //dE.
      case Y: next_alt => //=[[s4 E2]][??]; subst.
      have [[x [b {}IH]]|[x [b{}IH]]] := IH _ _ _ erefl.
        admit.
      admit.
  Abort.

  (*   Lemma run_or_fail {s1 s2 A B b}:
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
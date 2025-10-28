From mathcomp Require Import all_ssreflect.
From det Require Import run.
From det Require Import zify_ssreflect.

Section RunP.
  Variable u: Unif.
  (* Notation *)

  (* Lemma expanded_classic_expanded {s A r}:
    expanded_classic u s A r -> expandedb u s A r.
  Proof. by exists false. Qed. *)
  
  (* Lemma run_classic_run {s A s1 B}:
    run_classic u s A s1 B -> run u s A s1 B.
  Proof. by exists false. Qed. *)

  (* Lemma run_classic_cut {s s2 A B s3 C}:
    run_classic u s A s3 C -> expand u s A = CutBrothers s2 B -> False.
  Proof.
    rewrite /run_classic; remember false as f eqn:Hf => H.
    elim: H s2 B Hf; clear.
    + inversion 1; congruence.
    + move=> s1 s2 r A A' B C b1 b2 b3 HE HN HR IH + s4 A2 /[subst1] +.
      destruct b1, b2 => // _ HC.
      inversion HE; congruence.
  Qed. *)

  Lemma ges_subst_cutl {s A} : get_substS s (cutl A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//.
    - move=> A HA B0 _ B HB s; case:ifP; rewrite success_cut => sA; rewrite sA HA//.
  Qed.

  (* Lemma ges_subst_3 {s A B} :
    success A -> get_substS (get_substS (get_substS s A) B) A = get_substS (get_substS s A) B.
  Proof.
    elim: A s B => //=.
    - move=> A HA s B HB s1 C; case: ifP => //dA. rewrite dA//.
    - move=> A HA B0 _ B HB s1 C; case: ifP => sA; rewrite sA//.
      rewrite -HB.
    elim: A s => //=.
    - move=> A HA s B HB s1; case:ifP => //=dA; rewrite ?is_dead_cutl dA//.
    - move=> A HA B0 _ B HB s; case:ifP; rewrite success_cut => sA; rewrite sA HA//.
  Qed. *)

  (* Lemma expanded_and_complete {s s' A B0 B A' B0' B' b} :
    expandedb u s (And A B0 B) (Done s' (And A' B0' B')) b -> 
      Texists s'' b1 b2 A'', 
        expandedb u s A (Done s'' A'') b1 /\
        expandedb u s'' B (Done s'  B') b2 /\ 
        (b = (addn b1 b2)) /\
        (if b2 == 0 then A' = A'' else A' = cutl A'').
  Proof.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => H.
    elim: H A B0 B A' B0' B' Hg0 s' Hs1; clear => //.
    - move=> s1 s2 A A' + B C0 C B' C0' C' ? s3 [??]; subst.
      move=> /simpl_expand_and_solved. 
      move => [s' [Ax [Bx']]] => -[H1 [H2 [???]]]; subst.
      by repeat eexists; (try apply: expanded_done); simpl; try eassumption.
    - move=> s1 s2 r A A' b + HB IH B C0 C B2 C0' C2 ? s3 ?; subst => /=.
      case HA: expand => //=[s4 B1|s4 B1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl _ erefl.
        move=> [s'[b1[b2[A''[HB2 [HA2 [HC ?]]]]]]]; subst.
        (repeat eexists; try eassumption).
        - apply: expanded_cut HA HB2.
        - lia.
      case HB1':expand => //[s5 C1][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl _ erefl.
      move=> /= [s5 [b1[b2[A''[EA2 [EB2 [? HH]]]]]]]; subst.
      have [[??]+]:= expand_solved_same _ HA; subst.
      rewrite -success_cut => scA1.
      have ?:= expand_cb_same_subst _ HB1'; subst.
      have[[??]?] := expanded_success _ scA1 EA2; subst.
      repeat eexists.
      - apply: expanded_done HA.
      - rewrite ges_subst_cutl in EB2.
        apply: expanded_cut HB1' EB2.
      - lia.
      - rewrite cutl2 if_same in HH; subst => //.
    - move=> s1 s2 r A A' b + HB IH B C0 C B2 C0' C2 ? s3 ?; subst.
      move=> /=; case X: expand => //[s1' B'|s1' B'].
        move=> [??]; subst.
        have:= IH _ _ _ _ _ _ erefl _ erefl.
        move=> /= [s4 [b1[b2[A''[EA2 [EB2 [? HH]]]]]]]; subst.
        do 5 eexists; repeat split => //=; eauto.
        apply: expanded_step X EA2.
      case Y: expand => //=[s1'' C'][??]; subst.
      have {IH} [s''[b1[b2[A''[H1 [H2 [? HH]]]]]]] := IH _ _ _ _ _ _ erefl _ erefl; subst.
      have [[??] sA']:= expand_solved_same _ X; subst.
      have /= [[??]?] := expanded_success _ sA' H1; subst.
      do 5 eexists; repeat split; eauto.
      apply: expanded_step Y H2.
  Qed. *)

  Definition choose_cutl b1 A := (if (b1 == 0) then A else cutl A).
  
  Lemma choose_cutl_id {A}: choose_cutl 0 A = A.
  Proof. rewrite/choose_cutl eqxx//. Qed.

  Lemma choose_cutl_cutl {b2 A}: choose_cutl b2 (cutl A) = (cutl A).
  Proof. rewrite/choose_cutl cutl2 if_same//. Qed.

  Lemma choose_cutl_lt {b2 A}: 0 < b2 -> choose_cutl b2 A = cutl A.
  Proof. rewrite/choose_cutl; case: eqP => //; lia. Qed.

  (* Definition mirror_res F r :=
    match r with
    | Done s2 B => Done s2 (F B)
    | Failed B => Failed (F B)
    end. *)

  (* Lemma exp_and_left_succ {A} B0 {s1 B b1 r}: 
    success A -> expandedb u (get_substS s1 A) B r b1 ->
      expandedb u s1 (And A B0 B) 
        (mirror_res (fun x => (And (choose_cutl b1 A) (choose_cutl b1 B0) x)) r) b1.
  Proof.
    remember (get_substS _ _) as S eqn:HS => + H.
    elim: H A B0 s1 HS => //=; clear.
    - move=> s s' A A' H A0 B0 s1 ? sA; subst.
      have [[??]sA']:= expand_solved_same _ H; subst.
      apply: expanded_done.
      rewrite /= succes_is_solved//!choose_cutl_id succes_is_solved//.
    - move=> s A A' HA B C s1 ? sB; subst.
      apply: expanded_fail.
      rewrite /= (succes_is_solved _ _ sB) HA//=!choose_cutl_id//.
    - move=> s s' r A B b HA HB IH A0 B0 s1 ? sA0; subst.
      rewrite -success_cut in sA0.
      have:= IH (cutl A0) (cutl B0) s1.
      rewrite ges_subst_cutl => /(_ erefl sA0).
      rewrite !choose_cutl_cutl => {}IH.
      rewrite success_cut in sA0.
      apply: expanded_cut .
        move=>/=; rewrite (succes_is_solved _ _ sA0) HA//.
      rewrite !choose_cutl_lt//.
    - move=> s s' r A B b HA HB IH A0 B0 s1 ? sA0; subst.
      have {}IH := IH A0 B0 _ erefl sA0.
      apply: expanded_step IH.
      rewrite /= (succes_is_solved _ _ sA0) HA//.
  Qed. *)

  (* Lemma expanded_and_correct_done {s0 s1 s2 A C b1 b3} B0 {B D} :
      expandedb u s0 A (Done s1 B) b1 -> expandedb u s1 C (Done s2 D) b3 ->
        expandedb u s0 (And A B0 C)
          (Done s2 (And (choose_cutl b3 B) (choose_cutl b3 B0) D)) (b1+b3).
  Proof.
    remember (Done _ _) as RD eqn:HRD => H.
    elim: H s1 s2 C B0 B D HRD b3 => //=; clear.
    + move=> s1 s2 A B eA s3 s4 C D E F [??] b1 H; subst.
      have [[??]sE]:= expand_solved_same _ eA; subst.
      have:= exp_and_left_succ D sE H => /= H1.
      apply: H1.
    + move=> s s' r A B b1 HA HB IH s1 s2 C D E F ? b3 H1; subst.
      have {}IH := IH _ _ _ D _ _ erefl _ H1.
      apply: expanded_cut IH => //=.
      rewrite HA//.
    + move=> s s' r A B b1 HA HB IH s1 s2 C D E F ? b3 H1; subst.
      have {}IH := IH _ _ _ D _ _ erefl _ H1.
      apply: expanded_step IH => //=.
      rewrite HA//.
  Qed. *)

  Lemma expand_cutl_cb {s C s' B}: expand u s (cutl C) = CutBrothers s' B -> False.
  Proof.
    elim: C s s' B=> //=.
    - move=> A HA s B HB s1 s2 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA; case expand => //.
    - move=> A HA B0 _ B HB s1 s2 C.
      case e: expand => //[s1' A'|s1' A'].
        by have:= HA _ _ _ e.
      case f: expand => //[s1'' B'].
      by have:= HB _ _ _ f.
  Qed.

  Lemma expand_cutl_exp {s C s' B}: expand u s (cutl C) = Expanded s' B -> False.
  Proof.
    elim: C s s' B=> //=.
    - move=> A HA s B HB s1 s2 C; rewrite fun_if/=.
      case: ifP => //=dA; rewrite ?is_dead_cutl dA.
        case X: expand => //=.
          by have:= HB _ _ _ X.
        by have:= expand_cutl_cb X.
      case X: expand => //.
        by have:= HA _ _ _ X.
      by have:= expand_cutl_cb X.
    - move=> A HA B0 _ B HB s1 s2 C.
      case e: expand => //[s1' A'|s1' A'].
        by have:= HA _ _ _ e.
      case f: expand => //[s1'' B'].
      by have:= HB _ _ _ f.
  Qed.

  Lemma run_or_correct_left {s1 A s2 n r b} sX X:
    runb u s1 A s2 r n b ->
      Texists r', 
        runb u s1 (Or A sX X) s2 r' 0 b /\
          if n == 0 then
            if r is Some A' 
              then (r' = (Some (Or A' sX X))) :> Type
            else if next_alt false X is Some X' 
              then Texists A'', is_dead A'' /\ (r' = Some (Or A'' sX X'))
            else r' = None
          else r' = omap (fun x => Or x sX (cutr X)) r
           .
  Proof.
    move=> H; elim: H X; clear.
    + move=> s s' r A B /[dup] /(expand_solved_same) [[??]sA] H ? X; subst.
      repeat eexists.
        apply: run_done erefl; rewrite /= H success_is_dead//.
      rewrite//= success_is_dead//.
      case W: next_alt => //=.
      case Z: next_alt => //=[C'|].
        rewrite (next_alt_dead Z); repeat eexists; rewrite is_dead_dead//.
      rewrite if_same//.
    + move=> s1 s2 s3 r A B n b HA HB IH X/=.
      case: n HB IH => //=.
        move=> + /(_ (cutr X)) [r'[{}H1]].
        case: r => [B'|].
          move=> HB?; subst.
          repeat eexists => //.
          apply: run_step.
            by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
          by [].
        rewrite (is_ko_next_alt _ is_ko_cutr) => H2 ?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move=> n + /(_ (cutr X)) [r'[{}H1]].
      rewrite cutr2.
      case: r => [B'|].
      move=> HB?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move => H2 ?; subst.
      repeat eexists => //.
      apply: run_step.
        by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      by [].
    + move=> s1 s2 s3 r A B n b HA HB IH X/=.
      case: n HB IH => //=.
        move=> + /(_ X) [r'[{}H1]].
        case: r => [B'|].
          move=> HB?; subst.
          repeat eexists => //.
          apply: run_step.
            by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
          by [].
        case Y: next_alt => [X'|].
          move=> HB [A'' [dA'' ?]]; subst.
          repeat eexists; eauto.
          apply: run_step; eauto; rewrite/= HA.
          by case: ifP => // dA; rewrite is_dead_expand in HA.
        move=> rB ?; subst.
        repeat eexists => //.
        apply: run_step.
          by move=> /=; rewrite HA; case: ifP => //dA;rewrite is_dead_expand in HA.
        by [].
      move=> n + /(_ (X)) [r'[{}H1]].
      case: r => [B'|].
      move=> HB?; subst.
        repeat eexists => //.
        apply: run_step.
          by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
        by [].
      move => H2 ?; subst.
      repeat eexists => //.
      apply: run_step.
        by rewrite/=HA; case: ifP => //dA; rewrite is_dead_expand in HA.
      by [].
    + move=> s1 s2 A B C r n b HA HB HC + X.
      move=> /(_ X)[r' [H1 H2]].
      repeat eexists; try eassumption.
      apply: run_fail H1.
        move=> /=; rewrite HA; case: ifP => //dA.
        move: HA; rewrite is_dead_expand// =>-[?]; subst.
        by rewrite is_dead_next_alt in HB.
      by rewrite/= HB (next_alt_dead HB).
  Qed.

  (* Lemma run_or_complete:
    runb u sA (Or A sB B) s3 r n1 ->
      (runb u sA A srA rA n /\ ()) \/ () *)

  (* Lemma run_or_correct_right {sA A srA rA bA} {sB B srB rB bB}:
    (runb u sA A srA rA bA -> False) -> runb u sB B srB rB bB ->
      if bA == 0 then (runb u sA (Or A sB B) srB (omap (fun x => Or (if is_dead A then A else dead1 A) srB x) rB) 0 :> Type)
      else dead_run u sA (Or A sB B).
  Proof.
    case: bA => /=[|n]; last first.
      move=> HA _ s3 s4 n1 H.
      apply: HA.
      admit.
    move=> + H.
    elim: H sA A srA rA; clear.
    + move=> s1 s2 r B B' /[dup] /expand_solved_same [[??]SB] eB ? sA A srA rA H1.
      case: ifP => dA.
        admit.
      apply: run_fail.
      apply: H1.
  Qed. *)

End RunP.
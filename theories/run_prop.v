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

  Lemma expanded_and_complete {s s' A B0 B A' B0' B' b} :
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
  Qed.

  Definition choose_cutl b1 A := (if (b1 == 0) then A else cutl A).
  
  Lemma choose_cutl_id {A}: choose_cutl 0 A = A.
  Proof. rewrite/choose_cutl eqxx//. Qed.

  Lemma choose_cutl_cutl {b2 A}: choose_cutl b2 (cutl A) = (cutl A).
  Proof. rewrite/choose_cutl cutl2 if_same//. Qed.

  Lemma choose_cutl_lt {b2 A}: 0 < b2 -> choose_cutl b2 A = cutl A.
  Proof. rewrite/choose_cutl; case: eqP => //; lia. Qed.

  Definition mirror_res F r :=
    match r with
    | Done s2 B => Done s2 (F B)
    | Failed B => Failed (F B)
    end.

  Lemma exp_and_left_succ {A} B0 {s1 B b1 r}: 
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
  Qed.

  Lemma expanded_and_correct_done {s0 s1 s2 A C b1 b3} B0 {B D} :
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
  Qed.

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

  Lemma expandedb_cutl_success {s1 A sm C b1}:
    expandedb u s1 (cutl A) (Done sm C) b1 -> success A.
  Proof.
    remember (cutl _) as c eqn:Hc.
    remember (Done _ _) as d eqn:Hd.
    move=> H.
    elim: H A C sm Hc Hd; clear => //.
    - move=> s s' A A' HA B B' sm ? []??; subst.
      have [[??]?]:= expand_solved_same _ HA; subst.
      rewrite -success_cut//.
    - move=> s s' r A B b HA HB IH C D sm ??; subst; by have:= expand_cutl_cb HA.
    - move=> s s' r A B b HA HB IH C D sm ??; subst; by have:= expand_cutl_exp HA.
  Qed.

  (* TODO: here *)
  Lemma expandes_and_fail {s A B0 B A' B0' B' b3}:
    expandedb u s (And A B0 B) (Failed (And A' B0' B')) b3 ->
      ((expandedb u s A (Failed A') b3) /\ (B0 = B0') /\ (B = B'))%type2 +
        (Texists s' b1 b2 A'', (*TODO: who is A'' wrt A' and who is B0' wrt B0? *)
          expandedb u s A (Done s' A'') b1 /\  
          expandedb u s' B (Failed B') b2 /\ 
          (b3 = addn b1 b2) /\
          (if b2 == 0 then A' = A'' else A' = cutl A'') /\
          (if b2 == 0 then B0' = B0 else B0' = cutl B0)
        ).
  Proof.
    remember (And A _ _) as R eqn:HR.
    remember (Failed _) as F eqn:HF => H.
    elim: H A B0 B A' B0' B' HR HF => //=; clear.
    + move=> s A B + C D0 D C' D0' D' ? [?]; subst => /=.
      case X: expand => //[C1|s' C1].
        move=> [???]; subst.
        left; split => //; apply: expanded_fail X.
      case Y: expand => //[D1][???]; subst.
      right; repeat eexists.
        apply: expanded_done X.
      apply: expanded_fail Y.
      all: try by move=> //.
    + move=> s1 s2 r A B b + HB IH C D0 D C' D0' D' ??; subst => /=.
      case X: expand => //[s1' C1|s1' C1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move => [[IH ?]|[sm [b1 [b2 [A'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]; subst.
          left; split=> //; apply: expanded_cut X IH.
        right; repeat eexists; (try eassumption) => /=.
        - apply: expanded_cut X IH1.
        - lia.
      case Y: expand => //[s1'' D''][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      have [[??] sC1] := expand_solved_same _ X; subst C1 s1'.
      have H1 := expanded_success1 u  s1 sC1.
      rewrite -success_cut in sC1.
      have H := expanded_success1 u  s1 sC1.
      move => [[IH ?]|[sm [b1 [b2 [A'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]; subst.
        by have [] //:= expanded_consistent _ H IH.
      have {H} [[? H4] ?] //:= expanded_consistent _ H IH1; subst.
      rewrite ges_subst_cutl in IH1.
      rewrite ges_subst_cutl in IH2.
      right; repeat eexists.
      - rewrite success_cut in sC1; apply: expanded_success1 sC1.
      - apply: expanded_cut Y IH2.
      - move=> //.
      - rewrite cutl2 if_same in IH4; subst => //.
      - rewrite cutl2 if_same in IH5; subst => //.
    + move=> s1 s2 r A B b + HB IH C D0 D C' D0' D' ??; subst => /=.
      case X: expand => //[s1' C1|s1' C1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move => [[IH?]|[sm [b1 [b2 [A''[IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]; subst.
          left; split => //; apply: expanded_step X IH.
        right; repeat eexists; try eassumption.
        apply: expanded_step X IH1.
      case Y: expand => //[s1'' D''][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      have [[??] sC1] := expand_solved_same _ X; subst.
      have H := expanded_success1 u s1 sC1.
      move => [[IH [??]]|[sm [b1 [b2 [A'' [IH1 [IH2 [IH3 [IH4 IH5]]]]]]]]]; subst.
        by have [] := expanded_consistent _ H IH.
      have [[??]?] := expanded_consistent _ IH1 H; subst.
      right; repeat eexists; try eassumption.
      apply: expanded_step Y IH2.
  Qed.

  Lemma expandedb_or0 {s A s1 B r b}:
    expandedb u s (Or A s1 B) r b -> b = 0.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s1 B Ho; clear => //.
    - move=> s s' r A B b + H2 IH C s2 D ?; subst => /=; case: ifP => dC; case e: expand => //.
    - move=> s s' r A B b + H2 IH C s2 D ?; subst => /=; case: ifP => dC;
        by case e: expand => // [s2' D'|s2' D'][??]; subst; apply: IH.
  Qed.

  Lemma runb_or0 {s A s1 B s' r b}:
    runb u s (Or A s1 B) s' r b -> b = 0.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s1 B Ho; clear => //.
    - move=> s s' A B C b H _ ????; subst.
      apply: expandedb_or0 H.
    - move=> s1 s2 A B C D b1 b2 b3 H1 H2 H3 IH ?????; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 H2 => //??? H1 H2 _.
      rewrite (expandedb_or0 H1).
      move: H2 => /=; case: ifP => H.
        case w: next_alt => // -[?]; subst.
        rewrite (IH _ _ _ erefl)//.
      case W: next_alt => //=.
        move=> []?; subst; rewrite (IH _ _ _ erefl)//.
      case: ifP => //.
      case: next_alt => // ? _ [?]; subst.
      rewrite (IH _ _ _ erefl)//.
  Qed.

  Lemma expanded_and_fail_left {s A FA b1}:
    expandedb u s A (Failed FA) b1 ->
      forall B0 B, Texists b2, expandedb u s (And A B0 B) (Failed (And FA B0 B)) b2.
  Proof.
    move=> H.
    remember (Failed _) as F eqn:HF.
    elim: H FA HF => //=; clear.
    + move=> s A B H FA [<-].
      eexists; apply: expanded_fail => //=; rewrite H//.
    + move=> s s' r A B ? H H1 IH FA ? B0 B1; subst => //=.
      have [?{}IH]:= IH _ erefl B0 B1.
      eexists; apply: expanded_cut IH.
      rewrite /= H//.
    + move=> s s' r A B ? H H1 IH FA ? B0 B1; subst => //=.
      have [?{}IH]:= IH _ erefl B0 B1.
      eexists; apply: expanded_step IH.
      rewrite /= H//.
  Qed.

  Lemma run_and_fail_both {s s' A B} B0 {SA FB b1 b}:
    expandedb u s A (Done s' SA) b1 -> expandedb u s' B (Failed FB) b ->
      expandedb u s (And A B0 B) (Failed (And (choose_cutl b SA) (choose_cutl b B0) FB)) (b1+b).
  Proof.
    move=> H.
    remember (Done _ _) as D eqn:HD.
    elim: H B s' SA HD b => //=; clear.
    + move=> s1 s2 A B HA C s3 D [??] b H; subst.
      have [[??]sA]:= expand_solved_same _ HA; subst.
      apply: exp_and_left_succ sA H.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? b H2; subst => //=.
      have {}IH := IH _ _ _ erefl b H2.
      rewrite addSn.
      apply: expanded_cut IH.
      by rewrite /=H.
    + move=> s s' r A B ? H H1 IH B1 s1 alt ? b H2; subst => //=.
      have {}IH := IH _ _ _ erefl b H2.
      apply: expanded_step IH.
      by rewrite /=H.
  Qed.

  Lemma expanded_or_correct_left {s s' A A'} b:
    expandedb u s A (Done s' A') b ->
      forall s2 B, expandedb u s (Or A s2 B) (Done s' (Or A' s2 (if b == 0 then B else cutr B))) 0.
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A' HD => //=; clear.
    + move=> s s' A A' HA s2 B [] ?? s3 C; subst.
      apply: expanded_done => //= ; rewrite HA.
      case: ifP => //H.
      by rewrite (is_dead_expand _ H) in HA.
    + move=> s1 s2 r A B b HA HB IH s3 C ? s4 D /[subst].
      have /= {IH} := IH _ _ erefl s4 (cutr D).
      rewrite cutr2 if_same => IH.
      apply: expanded_step IH.
      move=> //=; case: ifP => // dA.
        by rewrite (is_dead_expand _ dA) in HA.
      by rewrite HA.
    + move=> s1 s2 r A B b HA HB IH s' C ? s4 D /[subst].
      have /={}IH := IH _ _ erefl s4 D.
      apply: expanded_step IH.
      move=> /=; case: ifP=> dA.
        by rewrite (is_dead_expand _ dA) in HA.
      by rewrite HA.
  Qed.

  Lemma expanded_or_correct_right {s s' X A A' b} sIgn:
    is_dead X ->
    expandedb u s A (Done s' A') b ->
      expandedb u sIgn (Or X s A) (Done s' (Or X s A')) 0.
  Proof.
    remember (Done _ _) as D eqn:HD => dX H.
    elim: H s' A' HD; clear -dX => //.
    + move=> s s' A A' HA s2 B [] ??; subst.
      apply: expanded_done => //= ; rewrite HA dX//.
    + move=> s1 s2 r A B b HA HB IH s3 C ?; subst.
      have {IH} H := IH _ _ erefl.
      apply: expanded_step H => /=; rewrite dX HA//=.
    + move=> s1 s2 r A B b HA HB IH s3 C ?; subst.
      have {}IH := IH _ _ erefl.
      apply: expanded_step IH => /=; rewrite dX HA//.
  Qed.

  Lemma expanded_or_complete_done {s s' s2 A A' B B' b}:
    expandedb u s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
      (((is_dead A = false) *
        Texists b, expandedb u s A (Done s' A') b /\ B' = if b == 0 then B else cutr B) +
        (is_dead A /\ A = A' /\ Texists b1, expandedb u s2 B (Done s' B') b1)%type2).
  Proof.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s' s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 s3 A A' + s2 s4 B C D E ? [??]; subst.
      move=> /simpl_expand_or_solved [].
        move=> [A2 [HA']] [??];subst.
        have [[??]sA] := expand_solved_same _ HA'; subst.
        have dA := success_is_dead sA => //.
        left; repeat split => //.
        exists false; split => //; apply: expanded_done HA'.
      move=> [B' [dA [HB' [??]]]];subst => //.
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
          have:= IH _ _ _ _ _ _ erefl erefl; rewrite dA => -[][]//.
          move=> _ [?][b H]; subst.
          right; repeat eexists.
          apply: expanded_step eB H.
        have:= IH _ _ _ _ _ _ erefl erefl; rewrite dA => -[][]// _ [?][b H]; subst.
        right; repeat eexists; apply: expanded_cut eB H.
      case eA: expand => //[s1' A1'|s1' A1'][??]; subst;
      have:= IH _ _ _ _ _ _ erefl erefl => -[];
      rewrite (expand_not_dead _ dA eA)// => -[]// _ [b [H1 H2]]; subst => //.
        left; repeat eexists; apply: expanded_step eA H1.
      left; repeat eexists.
        apply: expanded_cut eA H1.
      move=>/=; rewrite cutr2 if_same//.
  Qed.

  Lemma expanded_or_complete_fail {s s2 A A' B B' b}:
    expandedb u s (Or A s2 B) (Failed (Or A' s2 B')) b ->
      (is_dead A = false /\ 
        Texists b1, expandedb u s A (Failed A') b1 /\
        (if b1 == 0 then (B' = B) :> Type else (B' = cutr B) :> Type ))%type2 +
      (is_dead A /\ A = A' /\ Texists b1, expandedb u s2 B (Failed B') b1)%type2.
  Proof.
    remember (Failed _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 A A' + s2 B C D E ? [?]; subst.
      move=> /simpl_expand_or_fail [].
        move=> [A2 [HA']] [H [??]];subst.
        rewrite HA'; left; repeat split; auto.
        repeat eexists.
          apply: expanded_fail H.
        rewrite eqxx//.
      move=> [B' [dA [HB' [??]]]];subst.
      right; repeat split; auto; eexists.
      apply: expanded_fail HB'.
    + move=> s s1 r C D b2 + HB IH s' A' B' A B ??; subst.
      move=> /=; case: ifP => //dA; case: expand => //.
    + move=> s s1 r C D b2 + HB IH s' A' B' A B ??/=; subst => /=.
      case: ifP => dA.
        case eB: expand => //[s1' B1'|s1' B1'][??]; subst.
          have:= IH _ _ _ _ _ erefl erefl; rewrite dA => -[].
            move=> [?][]//.
          move=> [] _ [?] [b1 H]; subst.
          right; repeat eexists.
          apply: expanded_step eB H.
        have:= IH _ _ _ _ _ erefl erefl; rewrite dA => -[].
          move=> [] _ []//.
        move=> [] _ [?] [b1 H]; subst.
        right; repeat split; eexists; apply: expanded_cut eB H.
      case eA: expand => //[s1' A1'|s1' A1'][??]; subst; left.
        have {IH} := IH _ _ _ _ _ erefl erefl => -[].
          move=> []dA' [b1[H1 H2]]; subst.
          repeat eexists; try eassumption.
          apply: expanded_step eA H1.
        move=> []dA'.
        by rewrite (expand_not_dead _ dA eA) in dA'.
      have {IH} := IH _ _ _ _ _ erefl erefl => -[].
        rewrite cutr2.
        move=> [dA'] [b1 [H H1]]; subst.
        rewrite if_same in H1; subst.
        repeat eexists; try eassumption.
          apply: expanded_cut eA H.
        move=> //.
      move=> [dA'].
      by rewrite (expand_not_dead _ dA eA) in dA'.
  Qed.
  
  Lemma expanded_or_correct_left_fail {s A A'} b:
    is_dead A = false ->
    expandedb u s A (Failed A') b ->
      forall s2 B,
        expandedb u s (Or A s2 B) (Failed (Or A' s2 (if b == 0 then B else cutr B))) 0.
  Proof.
    remember (Failed _) as D eqn:HD => + H.
    elim: H A' HD => //=; clear.
    + move=> s A A' HA B []? dA s3 C; subst.
      apply: expanded_fail => /=.
      rewrite dA HA//.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D; subst.
      have {}IH:= IH _ erefl (expand_not_dead _ dA HA) s4 (cutr D).
      apply: expanded_step => //=.
        rewrite dA HA//.
      move: IH; rewrite cutr2 if_same => H//.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D; subst.
      have {}IH := IH _ erefl (expand_not_dead _ dA HA) s4 D.
      apply: expanded_step => //=.
      rewrite dA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma expanded_or_correct_right_fail {s2 X A A' b}:
    is_dead X = true ->
    expandedb u s2 A (Failed A') b ->
      forall s, expandedb u s (Or X s2 A) (Failed (Or X s2 A')) 0.
  Proof.
    remember (Failed _) as D eqn:HD => dX H.
    elim: H A' HD => //=; clear -dX.
    + move=> s A A' HA B [<-] s2.
      apply: expanded_fail; rewrite /=dX HA//.
    + move=> s1 s2 r A B b HA HB IH A' ? s; subst.
      have {}IH:= IH _ erefl s.
      apply: expanded_step IH; rewrite /=dX HA//.
    + move=> s1 s2 r A B b HA HB IH A' ? s; subst.
      have {}IH:= IH _ erefl s.
      apply: expanded_step IH.
      rewrite /=dX HA//.
  Qed.

  Lemma run_or_correct_left {s1 A s2 A' b sB B}:
    runb u s1 A s2 A' b ->
      runb u s1 (Or A sB B) s2 (Or A' sB (if b == 0 then B else cutr B)) 0.
  Proof.
    move => H.
    elim: H sB B => //; clear.
    + move=> s s' A B C b H -> s2 A'.
      have H1 := expanded_or_correct_left _ H s2 A'.
      apply: run_done H1 _.
      have sB := expanded_Done_success _ H.
      move=>/=.
      rewrite success_is_dead//.
    + move=> s s' A B C D b1 b2 b3 HE HN HR IH ? s2 E;subst.
      case dA: (is_dead A).
        have H := is_dead_expanded _ s dA.
        have [[?]?] := expanded_consistent _ (H _) HE; subst.
        by rewrite (is_dead_next_alt dA) in HN.
      have /= dB := expanded_not_dead _ dA HE.
      have H := expanded_or_correct_left_fail _ dA HE s2 E.
      move: H; case: eqP => Hb1 H; subst.
        case: eqP => ?; subst.
          destruct b2 => //.
          rewrite eqxx in IH.
          apply: run_backtrack H _ (IH _ _) erefl.
          move=> /=; rewrite dB HN//.
        destruct b2 => //=; simpl in IH.
        apply: run_backtrack H _ (IH _ _) erefl.
        move=> /=; rewrite dB HN//.
      destruct b1 => //=.
      have {}IH := IH s2 (cutr E); rewrite cutr2 if_same in IH.
      apply: run_backtrack H _ IH erefl.
      move=> /=; rewrite dB HN//.
  Qed.

  Lemma is_dead_runb {s1 s2 A B b}: is_dead A -> runb u s1 A s2 B b -> False.
  Proof. move=> H; apply: is_ko_runb (is_dead_is_ko H). Qed.

  Lemma next_alt_cutr {A}:
    next_alt (cutr A) = None.
  Proof. apply: is_ko_next_alt is_ko_cutr. Qed.

  Lemma runb_dead {s s1 A B b}: runb u s (dead1 A) s1 B b -> False.
  Proof. apply: is_ko_runb (is_dead_is_ko is_dead_dead). Qed.

  Lemma run_dead_left1 {s1 s2 A B X SOL b}:
    is_dead A -> runb u s1 (Or A s2 B) SOL X b ->
      Texists B' b,
        X = (Or A s2 B') /\ runb u s2 B SOL B' b.
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1 => + H.
    elim: H s2 A B Ho1; clear.
    - move=> s1 s2 A B C b H1 H2 s3 D E ? dD; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 => //= D' s3' E' H1 /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done H1 => -[][]H []; try congruence.
      move=> ? [b1 H2]; subst.
      rewrite dD; repeat eexists.
      apply: run_done H2 erefl.
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? s3 E F ? dE; subst.
      have:= expandedb_same_structure _ HA.
      case: B HA HB => //= D' s3' E' H1 + /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_fail H1 => -[][]; try congruence.
      move=> _ [?][b3 H2]; subst.
      rewrite dE.
      case X: next_alt => //[E''][?]; subst.
      have [B' [b4 [? H]]] := IH _ _ _ erefl dE; subst.
      repeat eexists.
      apply: run_backtrack H2 _ H erefl.
      have [] := expanded_or_complete_fail H1; rewrite dE//.
  Qed.

  Lemma run_dead_left2 {s2 X B B' SOL b1} sIgn:
    is_dead X -> runb u s2 B SOL B' b1 ->
    runb u sIgn (Or X s2 B) SOL (Or X s2 B') 0.
  Proof.
    move=> dA HB; elim: HB sIgn; clear -dA.
    - move=> s1 s2 A B C b H1 H2 sIgn; subst.
      have H := expanded_or_correct_right sIgn dA H1.
      apply: run_done H _ => /=; rewrite dA//.
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? sIgn; subst.
      have H := expanded_or_correct_right_fail dA HA sIgn.
      have {}IH := IH sIgn.
      apply: run_backtrack H _ IH erefl => /=.
      have fE := expandedb_failed _ HA.
      rewrite dA HB//.
  Qed.

  Lemma expandedb_exists s A:
    Texists r b, expandedb u s A r b.
  Proof.
    elim: A s => //=.
    - move=> s; do 2 eexists; apply: expanded_fail => //.
    - move=> s; do 2 eexists; apply: expanded_done => //.
    - move=> s; do 2 eexists; apply: expanded_step => //.
      apply: expanded_done => //.
    - move=> s; do 2 eexists; apply: expanded_fail => //.
    - move=> p c s.
      case X : (F u p c s) => [|[s' x] xs].
        do 2 eexists.
        apply: expanded_step => //=.
        apply: expanded_fail.
        rewrite/big_or X//.
      do 2 eexists.
      apply: expanded_step => //=.
      apply: expanded_fail.
      rewrite/big_or X//.
    - move=> s; do 2 eexists.
      apply: expanded_cut => //.
      apply: expanded_done => //.
    - move=> A HA s B HB s1.
      have [r[b {}HA]]:= HA s1.
      have [r1 [b1 {}HB]] := HB s.
      case: r HA => [s1' A'|A'] HA.
        have H1 := expanded_or_correct_left _ HA s B.
        do 2 eexists; eassumption.
      case dA: (is_dead A).
        case: r1 HB => [s' B'|B'] H1.
          have := expanded_or_correct_right s1 dA H1.
          do 2 eexists; eassumption.
        have := expanded_or_correct_right_fail dA H1 s1.
        do 2 eexists; eassumption.
      have  := expanded_or_correct_left_fail _ dA HA s B.
      do 2 eexists; eassumption.
    - move=> A HA B0 _ B HB s.
      have [r[bA {}HA]] := HA s.
      case: r HA => [s' A'|A'] HA.
        have [r[bB {}HB]]:= HB s'.
        case: r HB => [s'' B'|B'] HB.
          have := expanded_and_correct_done B0 HA HB.
          do 2 eexists; eassumption.
        have := run_and_fail_both B0 HA HB.
        do 2 eexists; eassumption.
      have [b]:= expanded_and_fail_left HA B0 B.
      do 2 eexists; eassumption.
  Qed.

  Lemma next_alt_runb {A B C s s2 b1}:
    next_alt A = Some B ->
      runb u s B s2 C b1 ->
        Texists G b, runb u s A s2 G b.
  Proof.
    have [r[b H]]:= expandedb_exists s A.
    elim: H B C s2 b1; clear.
    - move=> s s' A A' HA B C s2 b1 nA HB.
      have [[??]sA]:= expand_solved_same _ HA; subst.
      have:= next_alt_not_failed _ (success_failed _ sA).
      rewrite nA => -[]?; subst.
      do 2 eexists; eassumption.
    - move=> s A B HA B0 C s2 b1 nA HB.
      have [? fA]:= (expand_failed_same _ HA); subst => //.
      do 2 eexists; apply: run_backtrack nA HB erefl.
      apply: expanded_fail HA.
    - move=> s s' r A B b HA HB IH B0 C s2 b1 nA H.
      have fA:= expand_not_failed _ HA notF.
      have:= next_alt_not_failed _ fA.
      rewrite nA => -[?]; subst.
      do 2 eexists; eassumption.
    - move=> s s' r A B b HA HB IH B0 C s2 b1 nA H.
      have fA:= expand_not_failed _ HA notF.
      have:= next_alt_not_failed _ fA.
      rewrite nA => -[?]; subst.
      do 2 eexists; eassumption.
  Qed.

  Lemma run_or_complete {s1 s2 A B SOL altAB b}:
  (* TODO: be more precise on altAB *)
    runb u s1 (Or A s2 B) SOL altAB b ->
      (Texists altA b1, runb u s1 A SOL altA b1) + 
        (Texists altB b1, runb u s2 B SOL altB b1).
  Proof.
    remember (Or _ _ _) as O1 eqn:HO1.
    move=> H.
    elim: H s2 A B HO1 => //=; clear.
    + move=> s st s' alt C b H ? s2 D E ?; subst.
      have /= := expandedb_same_structure _ H.
      case: alt H => //= D' s2' E' H /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done H.
      move=> [][dD].
        move=> [b'[H1?]]; subst.
        left; eexists (clean_success D'), _.
        by apply: run_done H1 erefl.
      move=> [?[H1]] H2; subst.
      right; do 2 eexists.
      by apply: run_done H2 erefl.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? s4 E F ?; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= D' s2' E' H1 + /and3P[/eqP? _ _]; subst.
      case: ifP => dD'.
        case X: next_alt => //=[E2][?]; subst.
        have [[x [b {}IH]]|[x [b{}IH]]] := IH _ _ _ erefl.
          by have:= is_dead_runb dD' IH.
        have [[dE [b3[H4 H5]]]|[dE[?[b3 H4]]]] := expanded_or_complete_fail H1; subst.
          have /= := expanded_not_dead _ dE H4; congruence.
        right; do 2 eexists.
        apply: run_backtrack H4 X IH erefl.
      case W: next_alt => [D''|].
        move=>[?]; subst.
        have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
          have {H1} [[dE [b4 [H1 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail H1; subst.
            left; repeat eexists; apply: run_backtrack H1 W H erefl.
          by have:= next_alt_runb W H; auto.
        have [[dE [b4 [H2 H4]]]|[dE[?[b4 H2]]]] := expanded_or_complete_fail H1; subst; try congruence.
        right; case: b4 H2 H4 => /= [|n] H2 H4; subst.
        - repeat eexists; eassumption.
        - by have:= is_ko_runb _ is_ko_cutr H.
      case: ifP => //dE.
      have [[dE' [b4 [H2 H4]]]|[dE'[?[b4 H2]]]] := expanded_or_complete_fail H1; try congruence.
      case X: next_alt => //[E''][?]; subst.
      have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
        by have:= runb_dead H.
      case: b4 H2 H4 => [|n] /= H2 ?; subst => /=; try by rewrite next_alt_cutr in X.
      have [B'[b4 [? H4]]]:= run_dead_left1 is_dead_dead H3; subst.
      have {H2} [[_ ?]?]:= run_consistent _ H H4; subst.
      right; apply: next_alt_runb X H.
  Qed.

  Lemma run_or_correct_dead {s1 s2 A B}:
    dead_run u s1 A -> dead_run u s2 B -> dead_run u s1 (Or A s2 B).
  Proof.
    move=> HA HB sX C b H.
    have [] := run_or_complete H.
      move=> [x[b1]]; apply: HA.
    move=> [x[b1]]; apply: HB.
  Qed.

  Lemma expandedb_or_is_ko_left_ign_subst {A s B D b2 sIgn1} sIgn2:
    is_ko A -> expandedb u sIgn1 (Or A s B) D b2 ->
      Texists b2, expandedb u sIgn2 (Or A s B) D b2.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => + H.
    elim: H s A B sIgn2 Ho => //=; clear.
    - move=> s s' A A' + s1 B B' sIgn2 ? kB; subst.
      move=> /=; rewrite (is_ko_expand _ kB).
      case: ifP => //dB.
      case X: expand => //[s1' B''][??]; subst.
      have [[??]sB''] := expand_solved_same _ X; subst.
      eexists; apply: expanded_done => /=.
      rewrite dB X//.
    - move=> s A A' + s1 B B' sIgn2 ? kB; subst => /=.
      rewrite (is_ko_expand _ kB).
      case: ifP => dB.
        case X: expand => //[B''][?]; subst.
        have ?:= (expand_failed_same _ X); subst.
        eexists; apply: expanded_fail => /=; rewrite dB X//.
      move=>[?]; subst.
      eexists; apply: expanded_fail => /=; rewrite dB (is_ko_expand)//.
    - move=> s1 s2 r A B b + HB IH s3 C D sIgn2 ? kC; subst => /=.
      case: ifP => dC; case X: expand => //.
    - move=> s1 s2 r A B b + HB IH s3 C D sIgn2 ? kC; subst => /=.
      case: ifP => dC.
        case X: expand => //=[s3' D'|s3' D'][??]; subst;
        have [b2 {}IH] := IH _ _ _ sIgn2 erefl kC;
        eexists; apply: expanded_step IH; rewrite/=dC X//.
      rewrite is_ko_expand//.
  Qed.

  Lemma run_or_is_ko_left_ign_subst {A s B s2 D b2 sIgn1} sIgn2:
    is_ko A -> runb u sIgn1 (Or A s B) s2 D b2 ->
      Texists b2, runb u sIgn2 (Or A s B) s2 D b2.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => + H.
    elim: H s A B sIgn2 Ho; clear.
    - move=> s s' A B C b H1 ? s2 D E sIgn2 ? H; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 => //= D' s2' E' H1 /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done H1.
      move=> [[dD [b1 [H2 ?]]]| [dD[?[b1 H2]]]]; subst.
        have:= is_ko_expanded u s H.
        move=> /(expanded_consistent _ H2) []//.
      rewrite dD.
      have H3 := expanded_or_correct_right sIgn2 dD H2.
      eexists.
      apply: run_done H3 _.
      move=> /=; rewrite dD//.
    - move=> s s1 A B C D b1 b2 b3 HA HB HC IH ? s2 E F sIgn2 ? kE; subst.
      have:= expandedb_same_structure _ HA.
      case: B HA HB => //= E' s2' F' HA + /and3P[/eqP? _ _]; subst.
      case: ifP => dE'.
        case X: next_alt => //[F''][?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE  [b4 [H2 H4]]]|[dE [?[b4 H2]]]] := expanded_or_complete_fail HA; subst.
          have:= is_ko_expanded u s kE.
          move=> /(expanded_consistent _ H2) [][??]; subst.
          congruence.
        move=> /(_ sIgn2 kE) [b3 IH].
        have H3 := expanded_or_correct_right_fail dE H2 sIgn2.
        eexists; apply: run_backtrack H3 _ IH erefl.
        move=> /=; rewrite dE X//.
      case X: next_alt => //[E''|].
        move=>[?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE [H1 [b3 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail HA; subst; [|congruence].
        have:= is_ko_expanded u s kE.
        move=> /(expanded_consistent _ b3) [][??]; subst.
        rewrite (is_ko_next_alt)// in X.
      case: ifP => //dF'.
      case W: next_alt => //[F''][?]; subst.
      have [b3{}IH] := IH _ _ _ sIgn2 erefl (is_dead_is_ko is_dead_dead).
      have [[dE [H [b4 H1]]]|[dE [?[b4 H1]]]] := expanded_or_complete_fail HA; subst; [|congruence].
      have:= is_ko_expanded u s kE.
      move=> /(expanded_consistent _ b4) [][??]; subst.
      simpl in H1; subst.
      have [b5 H2] := expandedb_or_is_ko_left_ign_subst sIgn2 kE HA.
      eexists.
      apply: run_backtrack H2 _ IH erefl; rewrite/= dE X dF' W//.
  Qed.

  Fixpoint has_bt A B :=
    match A, B with
    | Or A _ B, Or A' _ B' =>
        if is_dead A' then 
          if is_dead A then has_bt B B'
          else true (*I'm creating a new dead state = call to backtrack*)
        else false
    | _, _ => false
    end.

  Lemma has_bt_id {A} : has_bt A A = false.
  Proof.
    elim: A => //=.
    move=> A HA _ B HB; case: ifP => dA//; rewrite dA//.
  Qed.

  Lemma expand_has_bt {s A r}:
    expand u s A = r -> has_bt A (get_state r) = false.
  Proof.
    move=> <-; clear r.
    elim: A s => //=.
    move=> A HA s B HB s1; case: ifP => dA.
      move: (HB s); case X: expand => /= ->; rewrite if_same//.
    move: (HA s1); case X: expand => /=; rewrite (expand_not_dead _ dA X)//.
  Qed.

  Lemma has_bt_trans {A B C}:
    same_structure A B -> same_structure B C ->
    has_bt A B = false -> has_bt B C = false -> has_bt A C = false.
  Proof.
    elim: A B C => //= A HA s B HB C D; destruct C, D => //= /and3P[_ Hx Hy] /and3P[_ H1 H2].
    case: ifP => dC1; last first.
      move=> _; case: ifP => dD1//.
    case: ifP => //dA bB.
    case: ifP => // dD1 bC.
    apply: HB Hy H2 bB bC.
  Qed.

  (* Lemma has_bt_trans1 {A B C}:
    same_structure A B -> same_structure B C ->
    has_bt A B = false -> has_bt B C = true -> has_bt A C = true.
  Proof.
    elim: A B C => //= A HA s B HB C D; destruct C, D => //= /and3P[_ Hx Hy] /and3P[_ H1 H2].
    case: ifP => dC1; last first.
      move=> _; case: ifP => dD1//.
    case: ifP => //dA bB.
    case: ifP => // dD1 bC.
    apply: HB Hy H2 bB bC.
  Qed. *)

  Lemma expandedb_has_bt {s A r b}:
    expandedb u s A r b -> has_bt A (get_state_exp r) = false.
  Proof.
    elim; clear.
    - move=> s s' A A' /expand_solved_same [[??]sA]; subst; rewrite/=has_bt_id//.
    - move=> s A B /expand_failed_same [? fB]; subst; rewrite/=has_bt_id//.
    - move=> s s' r A B b HA HB H. apply: has_bt_trans (expand_has_bt HA) H.
      apply: expand_same_structure HA. apply: expandedb_same_structure HB.
    - move=> s s' r A B b HA HB H. apply: has_bt_trans (expand_has_bt HA) H.
      apply: expand_same_structure HA. apply: expandedb_same_structure HB.
  Qed.

  Lemma run_and_correct {s0 sn A B B0 A' B0' B' b}:
    runb u s0 (And A B0 B) sn (And A' B0' B') b -> Texists A'' b1 b2 sm,
    (* TODO: be more precise on B0: it is cut if B' has a cut *)
    ( runb u s0 A sm (clean_success A'') b1 /\
      (if has_bt A A'' then runb u sm B0 sn (clean_success B' ) b2
      else runb u sm B sn (clean_success B' ) b2) /\
      A' = clean_success (if b2 == 0 then A'' else cutl A'')).
  Proof.
    remember (And _ _ _) as O1 eqn:HO1.
    remember (And A' _ _) as O2 eqn:HO2.
    move=> H.
    elim: H A B B0 A' B0' B' HO1 HO2 => //=; clear.
    + move=> s st s' alt C b H ? A B B0 A' B0' B' ? H1; subst.
      have := expandedb_same_structure _ H.
      case: alt H H1 => //= Ax B0x Bx H + _.
      have [s''[b1[b2[A''[H1[H2 [?]]]]]]]:= expanded_and_complete H; subst.
      case: eqP => H3 ?; subst.
        have sA'' := expanded_Done_success _ H1.
        rewrite sA'' => -[???]; subst.
        repeat eexists.
        - apply: run_done H1 erefl.
        - rewrite (expandedb_has_bt H1)//clean_success2//; apply: run_done H2 erefl.
        - move=> //.
      have := expanded_Done_success _ H1.
      rewrite -success_cut => sA''.
      rewrite sA'' => -[???]; subst.
      repeat eexists.
      - apply: run_done H1 erefl.
      - rewrite  (expandedb_has_bt H1)//clean_success2//; apply: run_done H2 erefl.
      - case: eqP => //.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? Ax B0x Bx A' B' C' ??; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= E' F' G' H1 + _.
      case: ifP => dD'//.
      have {H1} [[H1 [??]]|[s'[b5[b6[A'''[H1[H5 [H [Hx Hy]]]]]]]]] := expandes_and_fail H1; subst.
        (* we are in the case (E /\ G) with E failing for expandedb *)
        rewrite (expandedb_failed _ H1).
        case X: next_alt => //=[E2][?]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H5]]]]]]; subst.
        rewrite if_same.
        repeat eexists.
        apply: run_backtrack H1 X rE2 erefl.
        case: ifP => bt//.
        admit. (*should be OK: has_bt Ax A'' should be true *)
      have sA''' := expanded_Done_success _ H1.
      case: b6 H5 Hx Hy => /= [|n] H5 Hx Hy; subst.
        rewrite success_failed sA'''//.
        case W: next_alt => [G''|][?]; subst.
          have {IH} := IH _ _ _ _ _ _ erefl erefl.
          move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
          have [[? H ]?] := run_consistent _ rE2 (runb_success _ _ sA'''); subst.
          case: ifP => hbt H2.
            repeat eexists.
            apply: run_done H1 H.
            case: ifP => hbt1.
              admit.
            admit. (*should be OK: has_bt Ax A'' should be true *)
          repeat eexists.
          apply: run_done H1 H.
          case: ifP; last first => Hz.
            apply: run_backtrack H5 W _ erefl.
            admit. (*should be ok: need lemma: next_alt, the input subst for run is ignorable*)
          admit. (*should be ok: has_bt A''' A' is true*)
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
        rewrite if_same => H.
        repeat eexists.
        apply: run_done H1 _.
          admit. (*?what*)
        admit.
      rewrite -success_cut in sA'''.
      rewrite success_failed//sA'''.
      case W: next_alt => [G''|][?]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
        have [[? H ]?] := run_consistent _ rE2 (runb_success _ _ sA'''); subst.
        have:= clean_success_cutl _ sA'''.
        rewrite cutl2 -H => Hw.
        admit.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      move=>[A''[b3[b4[sm [rE2 [+ H6]]]]]]; subst.
      have /= := is_ko_runb _ _ rE2.
      rewrite success_cut in sA'''.
      move=> /(_ (clean_success_cutl _ sA'''))//.
  Admitted.

  (* Lemma run_and_correct_success_left {s0 sn A B B0 C b}:
    success A ->
    runb u s0 (And A B0 B) sn C b -> Texists A' B0' B' b1 b2, C = And A' B0' B' /\
    (   (runb u (get_substS s0 A) B sn (clean_success B' ) b2 /\ 
         A' = clean_success (if b2 == 0 then A else cutl A))%type2 +
    
        Texists sm A'', (runb u s0 (clean_success A) sm (clean_success A'') b1 /\ 
         runb u sm B0 sn (clean_success B') b2 /\
         A' = clean_success (if b2 == 0 then A'' else cutl A''))%type2
    )%type.
  Proof.
    remember (And _ _ _) as O1 eqn:HO1.
    move=> + H.
    elim: H A B B0 HO1 => //=; clear.
    + move=> s st s' alt C b H ? A B B0 ? sA; subst.
      have /= := expandedb_same_structure _ H.
      case: alt H => // A' B0' B' H _.
      move=> /=.
      have [s''[b1[b2[A''[H1[H2 [?]]]]]]]:= expanded_and_complete H; subst.
      have:= expanded_success1 u s sA.
      move=> /(expanded_consistent _ H1) [][]???; subst.
      case: eqP => H3 ?; subst.
        rewrite sA.
        repeat eexists; left; split; (try apply: run_done H2 _);rewrite?clean_success2//.
      rewrite success_cut sA.
      repeat eexists; left; repeat split.
        apply: run_done H2 _; rewrite clean_success2//.
      case: eqP => //.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? E G F ? sE; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= E' F' G' H1 + _.
      case: ifP => dD'//.
      have Hz := expanded_success1 u s sE.
      have {H1} [[H1 [??]]|[s'[b5[b6[A'''[H1[H5 [H [Hx Hy]]]]]]]]] := expandes_and_fail H1; subst.
        by have [] := expanded_consistent _ H1 Hz.
      have {H1}[[]???] := expanded_consistent _ Hz H1; subst A'''; subst.
      case: b6 H5 Hx Hy => //= [|n] H5 ??; subst.
        rewrite success_failed sE//.
        case X: next_alt => //[G''|][?]; subst.
          have {IH} [A'[B0'[B'[b1[b3[? [[H1 H2]|[sm[A'' [H4 [H6 H7]]]]]]]]]]] := IH _ _ _ erefl sE; subst.
            repeat eexists; left; split => //.
            apply: run_backtrack H5 X H1 erefl.
          by repeat eexists; right; repeat eexists; try eassumption.
        admit.
      rewrite -success_cut in sE.
      rewrite success_failed//sE.
      case X: next_alt => [G''|][?]; subst.
        have {IH} [A'[B0'[B'[b1[b3[? [[H1 H2]|[sm[A'' [H4 [H6 H7]]]]]]]]]]] := IH _ _ _ erefl sE; subst.
          repeat eexists.
          left; repeat split.
          rewrite ges_subst_cutl in H1.
          apply: run_backtrack H5 X H1 erefl.
          by rewrite cutl2 if_same.
        rewrite success_cut in sE.
        by have:= is_ko_runb _ (clean_success_cutl _ sE) H4.
      have /= := is_ko_runb _ _ H3.
      rewrite success_cut in sE.
      by move=> /(_ (clean_success_cutl _ sE)).
  Admitted. *)

  


  (*   Lemma run_or_fail {s1 s2 A B b}:
    run u s1 (Or A s2 B) Failed ->
      run u s1 A Failed /\ (run_classic u s1 A b -> run u s2 B Failed).
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
    run u s A Failed ->
      run u s (Or A s2 (cutl B)) Failed.
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
      run u s1 g1 Failed -> (run_classic u s1 g1 Failed -> run u s2 g2 Failed) ->
        run u s1 (Or g1 s2 g2) Failed.
  Proof.
    move: (classic (run_classic u s1 g1 Failed)) => [].
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
      run u s1 g1 Failed -> expand u s1 g1 = CutBrothers g3 -> (* g1 coulbe not an immediate cutl, but expand u... to a cutl *)
        run u s1 (Or g1 s2 g2) Failed.
  Proof.
    move=> H H1; apply: run_or_fail1 H _ => H2.
    inversion H2; subst; congruence.
  Qed.  *)

End RunP.
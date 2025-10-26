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

  (* Lemma expandedb_cutl_success {s1 A sm C b1}:
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
  Qed. *)

  (* TODO: here *)
  (* Lemma expandes_and_fail {s A B0 B A' B0' B' b3}:
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
  Qed. *)

  (* Lemma expandedb_or0 {s A s1 B r b}:
    expandedb u s (Or A s1 B) r b -> b = 0.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim: H A s1 B Ho; clear => //.
    - move=> s s' r A B b + H2 IH C s2 D ?; subst => /=; case: ifP => dC; case e: expand => //.
    - move=> s s' r A B b + H2 IH C s2 D ?; subst => /=; case: ifP => dC;
        by case e: expand => // [s2' D'|s2' D'][??]; subst; apply: IH.
  Qed. *)

  (* Lemma runb_or0 {s A s1 B s' r b}:
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
  Qed. *)

  (* Lemma expanded_and_fail_left {s A FA b1}:
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
  Qed. *)

  (* Lemma run_and_fail_both {s s' A B} B0 {SA FB b1 b}:
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
  Qed. *)

  (* Lemma expanded_or_correct_left {s s' A A'} b:
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
  Qed. *)

  (* Lemma expanded_or_correct_right {s s' X A A' b} sIgn:
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
  Qed. *)

  (* Lemma expanded_or_complete_done {s s' s2 A A' B B' b}:
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
  Qed. *)

  (* Lemma expanded_or_complete_fail {s s2 A A' B B' b}:
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
  Qed. *)
  
  (* Lemma expanded_or_correct_left_fail {s A A'} b:
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
  Qed. *)

  (* Lemma expanded_or_correct_right_fail {s2 X A A' b}:
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
  Qed. *)

  Lemma run_or_correct_left {s1 A s2 b r} sX X:
    runb u s1 A s2 r b ->
      Texists r', 
        runb u s1 (Or A sX X) s2 r' 0 /\
          if b == 0 then
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
    + move=> s1 s2 s3 r A B n HA HB IH X/=.
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
    + move=> s1 s2 s3 r A B n HA HB IH X/=.
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
    + move=> s1 s2 A B C r n HA HB HC + X.
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
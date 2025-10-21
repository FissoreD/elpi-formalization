From mathcomp Require Import all_ssreflect.
From det Require Import run.

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

  Lemma expanded_and_complete {s s' C A B0 B b} :
    expandedb u s (And A B0 B) (Done s' C) b ->
      Texists s'' A' B' b1 b2, expandedb u s A (Done s'' A') b1 /\
        (expandedb u s'' B (Done s' B') b2) /\ b = b1 || b2.
  Proof.
    move=>/[dup] /expandedb_same_structure.
    case: C => //= A' B0' B' _.
    remember (And _ _ _) as g0 eqn:Hg0.
    remember (Done _ _) as s1 eqn:Hs1 => H.
    elim: H A B0 B A' B0' B' Hg0 s' Hs1; clear => //.
    - move=> s1 s2 A A' + B C0 C B' C0' C' ? s3 [??]; subst.
      move=> /simpl_expand_and_solved. 
      move => [s' [Ax [Bx']]] => -[H1 [H2 [???]]]; subst.
      do 3 eexists; exists false, false; repeat split; apply: expanded_done; eassumption.
    - move=> s1 s2 r A A' b + HB IH B C0 C B2 C0' C2 ? s3 ?; subst => /=.
      case HA: expand => //=[s4 B1|s4 B1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl _ erefl.
        move=> [s'[B3[C3[b1[b2[HB2[HC ?]]]]]]]; subst.
        do 5 eexists; repeat split.
        - apply: expanded_cut HA HB2.
        - apply HC.
        - reflexivity.
      case HB1':expand => //[s5 C1][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl _ erefl.
      move=> /= [s5 [B1' [C1' [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
      have [[??]+]:= expand_solved_same _ HA; subst.
      rewrite -success_cut => scA1.
      have ?:= expand_cb_same_subst _ HB1'; subst.
      have[[??]?] := expanded_success _ scA1 EA2; subst.
      rename B1 into A1.
      rename B2 into A2.
      rename C into B.
      rename C1 into B1.
      rename C2 into B2.
      do 5 eexists; repeat split.
      - apply: expanded_done HA.
      - rewrite ges_subst_cutl in EB2.
        apply: expanded_cut HB1' EB2.
      - reflexivity.
    - move=> s1 s2 r A A' b + HB IH B C0 C B2 C0' C2 ? s3 ?; subst.
      move=> /simpl_expand_and_expanded [].
        move=> [Ax [EA ?]];subst.
        have:= IH _ _ _ _ _ _ erefl _ erefl.
        move=> /= [s4 [A2 [B2' [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
        do 5 eexists; repeat split => //=.
          apply: expanded_step EA EA2.
        apply: EB2.
      move=> [s4 [A'' [B'' [EA' [EB' ?]]]]]; subst.
      have:= IH _ _ _ _ _ _ erefl _ erefl.
      move=> /= [s5 [A2' [B2' [b1[b2[EA2 [EB2 ?]]]]]]]; subst.
      have [[??] sA']:= expand_solved_same _ EA'; subst.
      have /= [[??]?] := expanded_success _ sA' EA2; subst.
      do 5 eexists; repeat split.
        apply: expanded_done EA'.
      apply: expanded_step EB' EB2.
  Qed.

  Lemma expand_success_done {A B0 s1 B s2 B' b}: 
    success A -> expandedb u (get_substS s1 A) B (Done s2 B') b ->
      Texists b1, expandedb u s1 (And A B0 B) 
        (Done s2 (And (if b then cutl A else A) (if b then cutl B0 else B0) B')) b1.
  Proof.
    remember (get_substS _ _) as S eqn:HS.
    remember (Done _ _) as RD eqn:HRD => + H.
    elim: H A B0 s1 s2 B' HS HRD => //; clear.
    - move=> s s' A A' H A0 B0 s1 _ _ ? [<-<-] sA0; subst.
      have [[??]sA]:= expand_solved_same _ H; subst.
      exists false.
      apply: expanded_done.
      rewrite /= succes_is_solved//.
      rewrite (succes_is_solved)//=.
    - move=> s s' r A B b HA HB IH A0 B0 s1 s2 C?? sA0; subst.
      exists true.
      rewrite -success_cut in sA0.
      have:= IH (cutl A0) (cutl B0) s1 s2 C.
      rewrite ges_subst_cutl => /(_ erefl erefl sA0).
      rewrite !cutl2 !if_same.
      move=>[b1 {}IH].
      rewrite success_cut in sA0.
      apply: expanded_cut IH.
      move=>/=; rewrite // (succes_is_solved _ _ sA0) HA//.
    - move=> s s' r A B b HA HB IH A0 B0 s1 s2 C?? sA0; subst.
      have [b1 H]:= IH A0 B0 _ _ _ erefl erefl sA0.
      eexists.
      apply: expanded_step H.
      rewrite /= (succes_is_solved _ _ sA0) HA//.
  Qed.

  (* This can be factored with the previous proof... *)
  Lemma expand_success_fail {A B0 s1 B B' b}: 
    success A -> expandedb u (get_substS s1 A) B (Failed B') b ->
      expandedb u s1 (And A B0 B) 
        (Failed (And (if b then cutl A else A) (if b then cutl B0 else B0) B')) b.
  Proof.
    remember (get_substS _ _) as S eqn:HS.
    remember (Failed _) as RD eqn:HRD => + H.
    elim: H A B0 B' s1 HS HRD => //; clear.
    - move=> s A A' HA B C0 C s1 ? [?] sB; subst.
      apply: expanded_fail.
      rewrite /= (succes_is_solved _ _ sB) HA//.
    - move=> s1 s2 r A A' b HA HA' IH B C0 C s3 ?? sB; subst.
      rewrite -success_cut in sB.
      have := IH _ _ _ s3 _ erefl sB.
      rewrite ges_subst_cutl => /(_ (cutl C0) erefl).
      rewrite !cutl2 !if_same => {}IH.
      apply: expanded_cut IH.
      rewrite success_cut in sB.
      move=>/=; rewrite //= (succes_is_solved _ _ sB) HA//.
    - move=> s1 s2 r A A' b HA HA' IH B C0 C s3 ?? sB; subst.
      have := IH _ _ _ s3 _ erefl sB.
      move => /(_ (C0) erefl) {}IH.
      apply: expanded_step IH.
      move=>/=; rewrite //= (succes_is_solved _ _ sB) HA//.
  Qed.

  Lemma expanded_and_correct {s0 s1 s2 A C} B0 {B D b1 x} :
      expandedb u s0 A (Done s1 B) b1 -> expandedb u s1 C (Done s2 D) x ->
        Texists b3, expandedb u s0 (And A B0 C) 
          (Done s2 (And (if x then cutl B else B) (if x then cutl B0 else B0) D)) b3.
  Proof.
    remember (Done _ _) as RD eqn:HRD => H.
    elim: H s1 s2 C B0 B D HRD x => //=; clear.
    + move=> s1 s2 A B eA s3 s4 C D E F [??] b;subst.
      have [??]:= expand_solved_same _ eA; subst.
      have [[??]]:= expand_solved_same _ eA; subst.
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

  Lemma expandedb_cutl_success {s1 A sm C b}:
    expandedb u s1 (cutl A) (Done sm C) b -> success A.
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
  Lemma expandes_and_fail {s A B0 B A' B0' B' b}:
    expandedb u s (And A B0 B) (Failed (And A' B0' B')) b ->
      ((*TODO: decide better what is B0'*)
      ((Texists b1, expandedb u s A (Failed A') b1) +
        (Texists s' b1 b2, expandedb u s A (Done s' A') b1 /\ expandedb u s' B (Failed B') b2))) %type.
  Proof.
    remember (And A _ _) as R eqn:HR.
    remember (Failed _) as F eqn:HF => H.
    elim: H A B0 B A' B0' B' HR HF => //=; clear.
    + move=> s A B + C D0 D C' D0' D' ? [?]; subst => /=.
      case X: expand => //[C1|s' C1].
        move=> [???]; subst.
        left; eexists; apply: expanded_fail X.
      case Y: expand => //[D1][???]; subst.
      right; do 3 eexists; split.
        apply: expanded_done X.
      apply: expanded_fail Y.
    + move=> s1 s2 r A B b + HB IH C D0 D C' D0' D' ??; subst => /=.
      case X: expand => //[s1' C1|s1' C1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move => [[b1 IH]|[sm [b1 [b2 [IH1 IH2]]]]].
          left; eexists; apply: expanded_cut X IH.
        right; repeat eexists; try eassumption.
        apply: expanded_cut X IH1.
      case Y: expand => //[s1'' D''][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      have [[??] sC1] := expand_solved_same _ X; subst C1 s1'.
      have H1 := expanded_success1 u  s1 sC1.
      rewrite -success_cut in sC1.
      have H := expanded_success1 u  s1 sC1.
      move => [[b1 IH]|[sm [b1 [b2 [IH1 IH2]]]]].
        by have [] //:= expanded_consistent _ H IH.
      have [[??] ?] //:= expanded_consistent _ H IH1; subst; clear H.
      right; repeat eexists; last first.
        apply: expanded_cut Y _.
        rewrite ges_subst_cutl in IH2.
        eassumption.
      rewrite ges_subst_cutl in IH1.
      admit.
    + move=> s1 s2 r A B b + HB IH C D0 D C' D0' D' ??; subst => /=.
      case X: expand => //[s1' C1|s1' C1].
        move=>[??]; subst.
        have {IH} := IH _ _ _ _ _ _ erefl erefl.
        move => [[b1 IH]|[sm [b1 [b2 [IH1 IH2]]]]].
          left; eexists; apply: expanded_step X IH.
        right; repeat eexists; try eassumption.
        apply: expanded_step X IH1.
      case Y: expand => //[s1'' D''][??]; subst.
      have {IH} := IH _ _ _ _ _ _ erefl erefl.
      have [[??] sC1] := expand_solved_same _ X; subst.
      move => [[b1 IH]|[sm [b1 [b2 [IH1 IH2]]]]].
        left; eexists; eassumption.
      have:= expanded_success1 u s1 sC1.
      move=> /(expanded_consistent _ IH1) [][]???; subst.
      right; repeat eexists; try eassumption.
      apply: expanded_step Y IH2.
  Admitted.

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
      Texists b2, expandedb u s (And A B0 B) (Failed (And (if b then cutl SA else SA) (if b then cutl B0 else B0) FB)) b2.
  Proof.
    move=> H.
    remember (Done _ _) as D eqn:HD.
    elim: H B s' SA HD b => //=; clear.
    + move=> s1 s2 A B HA C s3 D [??] b H; subst.
      have [[??]sA]:= expand_solved_same _ HA; subst.
      eexists; apply: expand_success_fail sA H.
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
    expandedb u s A (Done s' A') b ->
      forall s2 B, Texists b2, expandedb u s (Or A s2 B) (Done s' (Or A' s2 (if b then cutr B else B))) b2.
  Proof.
    remember (Done _ _) as D eqn:HD => H.
    elim: H s' A' HD => //=; clear.
    + move=> s s' A A' HA s2 B [] ?? s3 C; subst.
      eexists; apply: expanded_done => //= ; rewrite HA.
      case: ifP => //H.
      by rewrite (is_dead_expand _ H) in HA.
    + move=> s1 s2 r A B b HA HB IH s3 C ? s4 D /[subst].
      have /= [? {IH}]:= IH _ _ erefl s4 (cutr D).
      rewrite cutr2 if_same => IH.
      eexists; apply: expanded_step => //=.
        case: ifP => // dA.
          by rewrite (is_dead_expand _ dA) in HA.
        by rewrite HA.
      apply: IH.
    + move=> s1 s2 r A B b HA HB IH s' C ? s4 D /[subst].
      have [? {}IH] := IH _ _ erefl s4 D.
      eexists; apply: expanded_step => //=.
        case: ifP=> dA.
          by rewrite (is_dead_expand _ dA) in HA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma expanded_or_correct_right {s s' X A A' b} sIgn:
    is_dead X ->
    expandedb u s A (Done s' A') b ->
      Texists b1, expandedb u sIgn (Or X s A) (Done s' (Or X s A')) b1.
  Proof.
    remember (Done _ _) as D eqn:HD => dX H.
    elim: H s' A' HD; clear -dX => //.
    + move=> s s' A A' HA s2 B [] ??; subst.
      eexists; apply: expanded_done => //= ; rewrite HA dX//.
    + move=> s1 s2 r A B b HA HB IH s3 C ?; subst.
      have {IH} [b1 H] := IH _ _ erefl.
      eexists; apply: expanded_step H => /=; rewrite dX HA//=.
    + move=> s1 s2 r A B b HA HB IH s3 C ?; subst.
      have [b1 {}IH] := IH _ _ erefl.
      eexists; apply: expanded_step IH => /=; rewrite dX HA//.
  Qed.

  Lemma expanded_or_complete_done {s s' s2 A A' B B' b}:
    expandedb u s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
      ((is_dead A = false) * 
        Texists b, expandedb u s A (Done s' A') b /\ B' = if b then cutr B else B) +
        (is_dead A /\ A = A' /\ Texists b1, expandedb u s2 B (Done s' B') b1)%type2.
  Proof.
    remember (Done _ _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s' s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 s3 A A' + s2 s4 B C D E ? [??]; subst.
      move=> /simpl_expand_or_solved [].
        move=> [A2 [HA']] [??];subst.
        have [[??]sA] := expand_solved_same _ HA'; subst.
        have dA := success_is_dead sA.
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
        rewrite (expand_not_dead _ dA eA)// => _ [b [H1 H2]]; subst.
        eexists; split => //; apply: expanded_step eA H1.
      eexists; split.
        apply: expanded_cut eA H1.
      move=>/=; rewrite cutr2 if_same//.
  Qed.


  Lemma expanded_or_complete_fail {s s2 A A' B B' b}:
    expandedb u s (Or A s2 B) (Failed (Or A' s2 B')) b ->
      (is_dead A = false /\ (if b then (B' = cutr B) :> Type else ((B' = cutr B) + (B' = B)))%type2 /\ 
        Texists b1, expandedb u s A (Failed A') b1 )%type2 +
        (is_dead A /\ A = A' /\ Texists b1, expandedb u s2 B (Failed B') b1)%type2.
  Proof.
    remember (Failed _) as RD eqn:HRD.
    remember (Or A _ _) as RO eqn:HRO => H.
    elim: H s2 A' B' A B HRO HRD => //=; clear.
    + move=> s1 A A' + s2 B C D E ? [?]; subst.
      move=> /simpl_expand_or_fail [].
        move=> [A2 [HA']] [H [??]];subst.
        rewrite HA'; left; repeat split; auto.
        eexists; apply: expanded_fail H.
      move=> [B' [dA [HB' [??]]]];subst.
      right; repeat split; auto; eexists.
      apply: expanded_fail HB'.
    + move=> s s1 r C D b2 + HB IH s' A' B' A B ??; subst.
      move=> /=; case: ifP => //dA; case: expand => //.
    + move=> s s1 r C D b2 + HB IH s' A' B' A B ??/=; subst => /=.
      case: ifP => dA.
        case eB: expand => //[s1' B1'|s1' B1'][??]; subst.
          have:= IH _ _ _ _ _ erefl erefl; rewrite dA => -[][]// _[->][b H].
          right; repeat eexists; apply: expanded_step eB H.
        have:= IH _ _ _ _ _ erefl erefl; rewrite dA => -[][]// _[->][b H].
        right; repeat split; eexists; apply: expanded_cut eB H.
      case eA: expand => //[s1' A1'|s1' A1'][??]; subst; left; repeat split;
      have {IH} := IH _ _ _ _ _ erefl erefl => -[][];
      rewrite (expand_not_dead _ dA eA) // => _ [H1 [b H2]]; subst => //.
      - eexists; apply: expanded_step eA H2.
      - case: b2 HB H1; rewrite cutr2; auto => _.
        move=> []; auto.
      - eexists; apply: expanded_cut eA H2.
  Qed.
  
  Lemma expanded_or_correct_left_fail {s A A'} b:
    is_dead A = false ->
    expandedb u s A (Failed A') b ->
      forall s2 B, Texists b1, expandedb u s (Or A s2 B) (Failed (Or A' s2 (if b then cutr B else B))) b1.
  Proof.
    remember (Failed _) as D eqn:HD => + H.
    elim: H A' HD => //=; clear.
    + move=> s A A' HA B [] ? s3 C; subst.
      eexists; apply: expanded_fail => /=.
      rewrite HA s3//.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH]:= IH _ erefl (expand_not_dead _ dA HA) s4 (cutr D).
      eexists; apply: expanded_step => //=.
        rewrite dA HA//.
      move: IH; rewrite cutr2 if_same => H; eassumption.
    + move=> s1 s2 r A B b HA HB IH C ? dA s4 D /[subst].
      have [? {}IH] := IH _ erefl (expand_not_dead _ dA HA) s4 D.
      eexists; apply: expanded_step => //=.
      rewrite dA.
        by rewrite HA.
      apply IH. 
  Qed.

  Lemma expanded_or_correct_right_fail {s2 X A A' b}:
    is_dead X = true ->
    expandedb u s2 A (Failed A') b ->
      forall s, Texists b1, expandedb u s (Or X s2 A) (Failed (Or X s2 A')) b1.
  Proof.
    remember (Failed _) as D eqn:HD => dX H.
    elim: H A' HD => //=; clear -dX.
    + move=> s A A' HA B [<-] s2; eexists.
      apply: expanded_fail; rewrite /=dX HA//.
    + move=> s1 s2 r A B b HA HB IH A' ? s; subst.
      have [b1{}IH]:= IH _ erefl s.
      eexists; apply: expanded_step IH; rewrite /=dX HA//.
    + move=> s1 s2 r A B b HA HB IH A' ? s; subst.
      have [b1{}IH]:= IH _ erefl s.
      eexists; apply: expanded_step IH.
      rewrite /=dX HA//.
  Qed.

  Lemma run_or_correct_left {s1 A s2 A' b sB B}:
    runb u s1 A s2 A' b ->
      Texists b1, runb u s1 (Or A sB B) s2 (Or A' sB (if b then cutr B else B)) b1.
  Proof.
    move => H.
    elim: H sB B => //; clear.
    + move=> s s' A B C b H -> s2 A'.
      have [? H1]:= expanded_or_correct_left _ H s2 A'.
      eexists.
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
      have [b3 H] := expanded_or_correct_left_fail _ dA HE s2 E.
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

  Lemma is_dead_runb {s1 s2 A B b}: is_dead A -> runb u s1 A s2 B b -> False.
  Proof. move=> H; apply: is_ko_runb (is_dead_is_ko H). Qed.

  Lemma next_alt_cutr {A}:
    next_alt (cutr A) = None.
  Proof. apply: is_ko_next_alt is_ko_cutr. Qed.

  Lemma runb_dead {s s1 A B b}: runb u s (dead1 A) s1 B b -> False.
  Proof. apply: is_ko_runb (is_dead_is_ko is_dead_dead). Qed.

  Lemma run_dead_left1 {s1 s2 A B X SOL b}:
    is_dead A -> runb u s1 (Or A s2 B) SOL X b ->
      Texists B' b1,
        X = (Or A s2 B') /\ runb u s2 B SOL B' b1.
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1 => + H.
    elim: H s2 A B Ho1; clear.
    - move=> s1 s2 A B C b H1 H2 s3 D E ? dD; subst.
      have:= expandedb_same_structure _ H1.
      case: B H1 => //= D' s3' E' H1 /and3P[/eqP? _ _]; subst.
      have:= expanded_or_complete_done H1 => -[][]; try congruence.
      move=> _ [?] [b1 H2]; subst; rewrite dD.
      repeat eexists.
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
    Texists b, runb u sIgn (Or X s2 B) SOL (Or X s2 B') b.
  Proof.
    move=> dA HB; elim: HB sIgn; clear -dA.
    - move=> s1 s2 A B C b H1 H2 sIgn; subst.
      have [b1 H] := expanded_or_correct_right sIgn dA H1.
      eexists; apply: run_done H _ => /=; rewrite dA//.
    - move=> s1 s2 A B C D b1 b2 b3 HA HB HC IH ? sIgn; subst.
      have [b3 H] := expanded_or_correct_right_fail dA HA sIgn.
      have [b4 {}IH] := IH sIgn.
      eexists; apply: run_backtrack H _ IH erefl => /=.
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
        have [b' H1] := expanded_or_correct_left _ HA s B.
        do 2 eexists; eassumption.
      case dA: (is_dead A).
        case: r1 HB => [s' B'|B'] H1.
          have [b2]:= expanded_or_correct_right s1 dA H1.
          do 2 eexists; eassumption.
        have [b2]:= expanded_or_correct_right_fail dA H1 s1.
        do 2 eexists; eassumption.
      have [b2] := expanded_or_correct_left_fail _ dA HA s B.
      do 2 eexists; eassumption.
    - move=> A HA B0 _ B HB s.
      have [r[bA {}HA]] := HA s.
      case: r HA => [s' A'|A'] HA.
        have [r[bB {}HB]]:= HB s'.
        case: r HB => [s'' B'|B'] HB.
          have [b3]:= expanded_and_correct B0 HA HB.
          do 2 eexists; eassumption.
        have [b]:= run_and_fail_both B0 HA HB.
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
      do 2 eexists; apply: run_backtrack nA HB erefl.
      apply: expanded_fail.
      have?:= (expand_failed_same _ HA); subst => //.
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
        have := expanded_or_complete_fail H1 => -[][]dE []H []b4 H2; subst.
          have /= := expanded_not_dead _ dE H2; congruence.
        right; do 2 eexists.
        apply: run_backtrack (H2) (X) _ erefl.
        apply: IH.
      case W: next_alt => [D''|].
        move=>[?]; subst.
        have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
          have := expanded_or_complete_fail H1 => {H1} -[][]dE []H2 []b4 H4; subst; try congruence.
          left; do 2 eexists; apply: run_backtrack H4 W H erefl.
        have := expanded_or_complete_fail H1 => {H1} -[][]dE []H2 []b4 H4; subst; try congruence.
        right; case: b1 H2 => [| []]?; subst.
        - by have:= is_ko_runb _ is_ko_cutr H.
        - by have:= is_ko_runb _ is_ko_cutr H.
        - do 2 eexists; apply: H.
      case: ifP => //dE.
      have := expanded_or_complete_fail H1 => -[][]dE' []H2 []b4 H4; subst; try congruence.
      case X: next_alt => //[E''][?]; subst.
      have {IH} [[aA [b3 H]]|[aA [b3 H]]] := IH _ _ _ erefl.
        by have:= runb_dead H.
      case: b1 H2 H1 => [|[]] ? H1; subst; try by rewrite next_alt_cutr in X.
      have [B'[b1 [? H2]]]:= run_dead_left1 is_dead_dead H3; subst.
      have {H2} [[_ ?]?]:= run_consistent _ H H2; subst.
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
      have [b2 H3] := expanded_or_correct_right sIgn2 dD H2.
      eexists.
      apply: run_done H3 _.
      move=> /=; rewrite dD//.
    - move=> s s1 A B C D b1 b2 b3 HA HB HC IH ? s2 E F sIgn2 ? kE; subst.
      have:= expandedb_same_structure _ HA.
      case: B HA HB => //= E' s2' F' HA + /and3P[/eqP? _ _]; subst.
      case: ifP => dE'.
        case X: next_alt => //[F''][?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE [H1 [b3 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail HA; subst.
          have:= is_ko_expanded u s kE.
          move=> /(expanded_consistent _ H2) [][??]; subst.
          congruence.
        move=> /(_ sIgn2 kE) [b3 IH].
        have [b5 H2]:= expanded_or_correct_right_fail dE H1 sIgn2.
        eexists; apply: run_backtrack H2 _ IH erefl.
        move=> /=; rewrite dE X//.
      case X: next_alt => //[E''|].
        move=>[?]; subst.
        have {IH} := IH _ _ _ _ erefl.
        have [[dE [H1 [b3 H2]]]|[dE[?[b4 H1]]]] := expanded_or_complete_fail HA; subst; [|congruence].
        have:= is_ko_expanded u s kE.
        move=> /(expanded_consistent _ H2) [][??]; subst.
        rewrite (is_ko_next_alt)// in X.
      case: ifP => //dF'.
      case W: next_alt => //[F''][?]; subst.
      have [b3{}IH] := IH _ _ _ sIgn2 erefl (is_dead_is_ko is_dead_dead).
      have [[dE [H [b4 H1]]]|[dE [?[b4 H1]]]] := expanded_or_complete_fail HA; subst; [|congruence].
      have:= is_ko_expanded u s kE.
      move=> /(expanded_consistent _ H1) [][??]; subst.
      case: b1 H HA => [?|[?|?]]; subst=> HA.
      - rewrite (is_ko_next_alt is_ko_cutr)// in W.
      - rewrite (is_ko_next_alt is_ko_cutr)// in W.
      have [b4 H2] := expandedb_or_is_ko_left_ign_subst sIgn2 kE HA.
      eexists.
      apply: run_backtrack H2 _ IH erefl; rewrite/= dE X dF' W//.
  Qed.

  Lemma run_and_correct_dead {s0 sn A B B0 C b}:
  (* TODO: be more precise on C *)
    runb u s0 (And A B0 B) sn C b -> Texists A' (*B0'*) B' b1 b2 sm, (*C = And A' B0' B' /\*)
    ((runb u s0 A sm A' b1 /\ runb u sm B sn B' b2)%type2 +
    (runb u s0 (clean_success A) sm A' b1 /\ runb u sm B0 sn B' b2)%type2)%type.
  Proof.
    remember (And _ _ _) as O1 eqn:HO1.
    move=> H.
    elim: H A B B0 HO1 => //=; clear.
    + move=> s st s' alt C b H ? A B B0 ?; subst.
      have /= := expandedb_same_structure _ H.
      case: alt H => //= A' B0' B' H _.
      Search expandedb And Done.
      have [s''[Ax[Bx[b1[b2[H1[H2?]]]]]]]:= expanded_and_complete H; subst.
      repeat eexists; left; split.
      - apply: run_done H1 erefl.
      - apply: run_done H2 erefl.
    + move=> s s1 A B C D b1 b2 b3 H1 H2 H3 IH ? E G F ?; subst.
      have /= := expandedb_same_structure _ H1.
      case: B H1 H2 => //= E' F' G' H1 + _.
      case: ifP => dD'//.
      case: ifP => fD.
        case X: next_alt => //=[E2][?]; subst.
        have [A'[B'[b3[b4[sm [[H4 H5]|[H4 H5]]]]]]] := IH _ _ _ erefl.



        (* move=> [?]; subst.
          Search expandedb Failed And.
          admit.
        admit.
      case: ifP => //sE.
        case W: next_alt => [G''|].
          move=>[?]; subst.
          have {IH} := IH _ _ _ erefl.
          admit.
        admit.
      admit. *)
  Admitted.

  


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
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import ctx tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap.

Require Import FunInd.
Functional Scheme expand_ind := Induction for step Sort Prop.

(* Definition sV_expand (S:sigV) Sexp:=
  forall k, 
    match lookup k Sexp with
    | None => True
    | Some Se =>
      if lookup k S is Some S then incl Se S = ty_ok true
      else forall (S':sigV), S' <> Sexp -> lookup k S' = None
    end.

Lemma sV_expand_refl {A}: sV_expand A A.
Proof.
  move=> //k.
  case lookup => //= s.
  rewrite incl_refl//.
Qed. *)

Open Scope fset_scope.

(* Definition sigP (sP:sigT) (s: sigS) (sV: sigV) :=
  [forall k : domf s,
    let (S, b1) := check_tm sP empty_ctx s.[valP k] in
    let SS := if b1 then S else weak S in
    let SV := odflt SS (sV.[?val k]) in 
    compat_type SS SV && incl SS SV]. *)

Definition sigP (sP:sigT) (s: sigS) (sV: sigV) :=
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then
      let (S, b1) := check_tm sP empty_ctx vk in
      let SS := if b1 then S else weak S in
      compat_type SS SV && incl SS SV
    else
    SV == weak SV].

(* Lemma sigP_MP {sP s N O}:
  closed_in O -> sigP sP s N -> more_precise N O -> sigP sP s O.
Proof.
Print val.
  move=> CO SP MP.
  apply /forallP => /= H/=.
  have:= forallP SP H.
  case: H => /= k ks.
  have kO := CO k.
  have kN := closed_in_mp CO MP k.
  rewrite (in_fnd kO)/= (in_fnd kN)/=.
  have [CON INO] := in2_more_compat_type_more_precise MP kO kN.
  case X: check_tm => [S []] /andP[CSN ISN]; apply/andP; split.
  - apply: compat_type_trans CSN _; by rewrite compat_type_comm.
  - apply: incl_trans ISN INO.
  - apply: compat_type_trans CSN _; by rewrite compat_type_comm.
  - apply: incl_trans ISN INO.
Qed. *)


(* Axiom step_sigP: forall u sP s sV A,
  sigP sP s sV -> sigP sP (get_substS s (get_tree (step u s A))) sV. *)

Lemma expand_det_tree {u sP sV sV' A r s ign d} : 
  check_program sP -> closed_in sV ->
    sigP sP (get_substS s A) sV ->
    (* sigma2ctx sP s = sV -> *)
      tc_tree_aux sP sV A ign = (d, sV') ->
        step u s A = r -> 
          exists S d', [/\ minD d d' = d',
            more_precise S sV'
            (* sigP sP (get_substS s (get_tree r)) S  *)
            (* true *)
            &
          (* sV_expand sV' S /\ *)
            tc_tree_aux sP sV (get_tree r) d = (d', S)].
Proof.
  move=> CkP.
  move: sV sV' r d ign.
  pattern u, s, A, (step u s A).
  apply: expand_ind; clear -CkP.
  - move=> s []//= _ sV sV' r d ign C SP [??] ?; subst=>/=; repeat eexists; rewrite ?minD_refl//; case:ifP => //.
  - move=> s []//= _ sV sV' r d ign C SP [??] ?; subst=>/=; repeat eexists; rewrite ?minD_refl//; case:ifP => //.
  - move=> s []//= _ sV sV' r d ign C SP [??] ?; subst=>/=; repeat eexists; rewrite ?minD_refl//; case:ifP => //.
  - (*here the checker comes into the game*)
    move=> /=s A pr t HA sV1 sV2 r d ign + + + <-{r}/=.
    {
      rewrite/big_or.
      case CC: check_callable => [D B] C SP [??]; subst.
      case X: F => [|[sr1 r1] rs]/=.
      - repeat eexists; rewrite ?minD_refl//.
        (* apply: more_precise_check_callable1 C CC. *)
      - admit.
      admit.
    }
  - by move=> s []//= _ sV sV' r d ign C SP [??] <-/=; subst; repeat eexists.
  - move=> s INIT A sB B HINIT dA IH sV sV' r d ign H/= SP.
    rewrite is_dead_is_ko//=.
    move=> tcA <-/=.
    rewrite get_tree_Or /= is_dead_is_ko// ?dA.
    apply: IH; eauto.
    rewrite dA in SP.
    move=> //.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/= + + <-/={r}.
    rewrite ?(step_not_dead _ dA eA) dA => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA.
      have {IH}/=[S[d'[H1 MP H2]]]:= IH _ _ _ _ _ H SP dtA eA.
      rewrite H2.
      have:= is_ko_tc_tree_aux kB.
      move=> ->; case: ifP; repeat eexists; auto.
        by rewrite minD_refl.
      apply: more_precise_trans MP.
      move: H2.
      rewrite is_ko_tc_tree_aux => //[[_<-]]//.
    have fA:= expand_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    have {IH}/=[S[d'[M MP dtA']]]:= IH _ _ _ _ _ H SP dtA eA.
    move=> [??]; subst d sV'.
    rewrite (expand_Exp_has_cut eA).
    case kA' : (is_ko A').
      rewrite failed_has_cut?is_ko_failed//=.
      case dt: tc_tree_aux => [B1 DA]; repeat eexists.
      move: dtA'.
      rewrite is_ko_tc_tree_aux//= => -[??]; subst d' S.
      have MDAS := more_precise_tc_tree_aux1 H dt.
      have [? _] := tc_tree_aux_func2 dtB dt; subst.
      have MM := more_precise_tc_tree_aux1 H dtA.
      by apply: more_precise_mergeR => //.
    case dtA2: (tc_tree_aux _ _ A') => /=[DA2 sVA2]//=.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB2 sVB2].
    repeat eexists.
      case: ifP => // cA.
      rewrite !cA/= in dtA2 dtB1.
      destruct DA', DB, d', DA2; simpl in * => //;[|congruence].
      have [? ] := tc_tree_aux_func2 dtB dtB1.
      by destruct DB2, ign => //=; congruence.
    have [? _] := tc_tree_aux_func2 dtA' dtA2; subst.
    have [? _] := tc_tree_aux_func2 dtB dtB1; subst.
    by apply: more_precise_merge2 (H) _ _ MP (more_precise_refl _);
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/= ++ <-{r}.
    rewrite dA/= ?(step_not_dead _ dA eA) => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA /=.
      rewrite (expand_CB_is_ko eA) is_ko_cutr.
      have //= := IH _ _ _ _ _ H SP dtA eA.
    have fA:= expand_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> [??]; subst => /=.
    rewrite (expand_CB_is_ko eA) is_ko_cutr.
    have {IH}/=[S[d' [H1 MP /=H2]]] := IH _ _ _ _ _ H SP dtA eA.
    move=> /=.
    case Hz : tc_tree_aux => //=[Dx sX].
    have [? Hk] := tc_tree_aux_func2 Hz H2; subst.
    suffices: more_precise S (merge_sig sVA sVB).
      move: Hz; case: ifP => cA Hz/=; repeat eexists; auto.
      destruct DA', DB, d', Dx; simpl in *; congruence.
    apply: more_precise_trans MP _.
    rewrite merge_comm.
    apply: more_precise_mergeR (H) _ _ (more_precise_refl _);
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/= ++ <-{r}.
    rewrite dA/= ?(step_not_dead _ dA eA) => SP.
    have [? fA] := expand_failed_same _ eA; subst A'.
    case: ifP => kA.
      move=> dtB /=.
      case dtB': tc_tree_aux => //=[D1 S1]/=.
      have [? Hk] := tc_tree_aux_func2 dtB dtB'; subst.
      by repeat eexists; first by destruct d, D1, ign => //; congruence.
    case: ifP => kB.
      move=> dtA1.
      by apply: IH eA; eauto.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA1 dtA2; subst.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
    have [? HB] := tc_tree_aux_func2 dtB1 dtB2; subst.
    rewrite failed_has_cut//= => -[??]; subst.
    by repeat eexists.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/= ++ <-{r}.
    rewrite dA/= ?(step_not_dead _ dA eA) => SP.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite success_has_cut//=.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA1 dtA2; subst.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
    have [? HB] := tc_tree_aux_func2 dtB1 dtB2; subst.
    have [S[d'[/= M H1 H2]]]:= IH _ _ _ _ _ H SP dtA1 eA.
    case: ifP => kB [??]; subst; repeat eexists => //.
    move: dtB1 dtB2; rewrite !is_ko_tc_tree_aux// => -[??][??]; subst.
    destruct DB2, DA2, DB1, d' => //=; congruence.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign/= C + + <-.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=sA => SP.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB01: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??]; subst.
    have {IH}/=[S[d'[H1 MP H2]]] := IH _ _ _ _ _ C SP dtA1 eA.
    case dtA1': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    have [? Hk] := tc_tree_aux_func2 H2 dtA1'; subst.
    case: (ifP (is_ko A')) => kA.
      repeat eexists; [apply: minD_refl|].
      move: H2 dtA1'; rewrite !is_ko_tc_tree_aux// => -[??][??]; subst.
      apply: more_precise_trans (MP) _.
      admit. (*should be OK if I add the hyp that the state will never fail, i.e. is_ko A' is rejected *)
    have H7 := more_precise_tc_tree_aux1 C dtA1.
    have H8:= more_precise_tc_tree_aux1 C dtA1'.
    case dtB : tc_tree_aux => [ddB sB].
    case dtB0 : tc_tree_aux => [ddB0 sB0].
    have CVA1 := closed_in_mp C H7.
    have [MP1 H] := more_precise_tc_tree_aux CVA1 dtB01 dtB0 MP.
    have [MP2 M3] := more_precise_tc_tree_aux CVA1 dtB1 dtB MP.
    repeat eexists.
      destruct DB01, DB1 => //=.
      simpl in dtA1'.
      have M1 : minD DA1 DA1' = DA1' by destruct DA1, DA1', d' => //=; congruence.
      move: (H M1) (M3 M1) => /=?; subst => //.
    by apply: more_precise_merge2 => //; 
    apply: more_precise_trans (more_precise_tc_tree_aux1 CVA1 _) H7; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign/= C + + <-.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=sA => SP.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB01: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??]; subst.
    have {IH}/=[S[d'[H1 MP H2]]] := IH _ _ _ _ _ C SP dtA1 eA.
    case dtA1': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    have [? Hk] := tc_tree_aux_func2 H2 dtA1'; subst.
    case: (ifP (is_ko A')) => kA.
      have:= expand_CB_is_ko eA.
      by rewrite kA.
    have H7 := more_precise_tc_tree_aux1 C dtA1.
    have H8:= more_precise_tc_tree_aux1 C dtA1'.
    case dtB : tc_tree_aux => [ddB sB].
    case dtB0 : tc_tree_aux => [ddB0 sB0].
    have CVA1 := closed_in_mp C H7.
    have [MP1 H] := more_precise_tc_tree_aux CVA1 dtB01 dtB0 MP.
    have [MP2 M3] := more_precise_tc_tree_aux CVA1 dtB1 dtB MP.
    repeat eexists.
      destruct DB01, DB1 => //=.
      simpl in dtA1'.
      have M1 : minD DA1 DA1' = DA1' by destruct DA1, DA1', d' => //=; congruence.
      move: (H M1) (M3 M1) => /=?; subst => //.
    by apply: more_precise_merge2 => //; 
    apply: more_precise_trans (more_precise_tc_tree_aux1 CVA1 _) H7; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign/= H + +<-/=.
    have [? fA]:= expand_failed_same _ eA; subst A'.
    rewrite failed_success//= => SP.
    case:ifP => kA.
      by move=> [??]; subst; repeat eexists; rewrite ?minD_refl.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=[??]; subst.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1].
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1].
    case dtB01: (tc_tree_aux _ _ B0) => /=[DB01 sVB01].
    have [? Hj] := tc_tree_aux_func2 dtA dtA1; subst.
    have [? Hk] := tc_tree_aux_func2 dtB dtB1; subst.
    have [? Hl] := tc_tree_aux_func2 dtB0 dtB01; subst.
    repeat eexists; last by [].
    destruct DB0,DB => //=; simpl in *.
    destruct DA', DA1, DB1, DB01, ign => //=; congruence.
  - move=> s INIT A B0 B HINIT HL A' eA HR sV sV' r d ign H/= ++<-/=.
    have [? sA] := expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite sA.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> SP [??]; subst.
    have ? := success_det_tree_same_ctx H sA dtA; subst.
    (* have:= HL _ _ _ _ _ H _ dtA eA. *)
    case eB: step => //=[B'|B'|B'|B']; rewrite success_is_ko//?success_cut//;
    case dtA': tc_tree_aux => [DA2 sVA'];
    case dtB': tc_tree_aux => [DB2 sVB'];
    case dtB0': tc_tree_aux => [DB02 sVB0']; cycle 1;
    [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); subst..];
    have MP1 := (more_precise_tc_tree_aux1 H dtA);
    have CSVA := closed_in_mp H MP1;
    have /= {HR}[S[d'[H1 H2 dtB'']]] := HR _ _ _ _ _ CSVA SP dtB eB.
    - move: dtA' dtB0'; rewrite cutl_tc_tree_aux//=cutr_tc_tree_aux.
      move=> [??][??]; subst sVB0' DB02 sVA' DA2.
      have [? m]:= tc_tree_aux_func2 dtB' dtB''; subst.
      repeat eexists.
        by destruct DB0, DB, DB2 => //=; simpl in *; subst.
      have MP := more_precise_tc_tree_aux1 H dtB'.
      rewrite merge_comm more_precise_merge//.
      admit.
    - have [? fB] := expand_failed_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
      repeat eexists; last by [].
      destruct DB0, DB => //=.
      destruct DB02, DB2, DA', DA2, ign => //=; simpl in *; try congruence.
    - have [? sB] := expand_solved_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
      repeat eexists; last by [].
      destruct DB0, DB => //=.
      destruct DB02, DB2, DA', DA2, ign => //=; simpl in *; try congruence.
    - have [? m1]:= tc_tree_aux_func2 dtB' dtB''; subst.
      have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst.
      repeat eexists.
        destruct DB0, DB; simpl in * => //; subst.
        rewrite !(@minD_comm _ Func)/= in m1, m.
        destruct DB02, DA2, DB2, DA', ign => //=; try congruence; simpl in *.
          exfalso. (*should be proved with dtB' + dtB *)
          admit.
        exfalso. (*should be proved with dtB' + dtB *)
        admit.
      by apply: more_precise_merge2 => //; apply: more_precise_tc_tree_aux1; eauto.
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A s' B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> 
  closed_in sV ->
    sigP sP (get_substS s A) sV ->
    (* sigma2ctx sP s = sV -> *)
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None /\ 
        sigP sP s' sV'.
Proof.
  rewrite/is_det.
  move=> ckP +++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV'; clear -ckP => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' H1 SP H2.
    have /=-> := success_det_tree_next_alt sA H2.
    split => //=.
    admit.
  - move=> s1 s2 r A B n eA _ IH s' ? sV sV' H1 SP dtA; subst.
    apply: IH erefl _ _ H1 _ _ .
    admit.
    admit.
  - move=> s1 s2 r A B n eA _ IH s' ? sV sV' H1 SP dtA; subst.
    (* apply: IH erefl _ _ _ _ _. *)
    admit.
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C SP TC; subst.
    have := failed_det_tree_next_alt C TC nA.
    move => [[]// [N [? [X _]]]]//.
    have:= IH _ erefl _ _ C _ X.
    admit.
Admitted.

Definition det_tree sP sV A := typ_func (tc_tree_aux sP sV A Func).

Lemma main {sP p t sV}:
  check_program sP -> 
    closed_in sV ->
      det_tree sP sV (CallS p t) -> 
        is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det.
  move=> /= CP CV.
  case C: check_callable => [[] S]//= _.
  move=> u s' B n H.
  apply: run_is_det H; eauto.
  by rewrite/=C.
Qed.

Print Assumptions  main.

Module elpi.
  From det Require Import elpi elpi_equiv.
  From det Require Import tree t2l_prop tree_valid_state tree_prop.

  Definition is_det g := forall u s' a',
    nur u empty g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c ign sV}: 
    check_program sP -> 
    closed_in sV ->
      check_callable sP sV c Func = (Func, ign) -> 
      is_det ((call p c):::nilC).
  Proof.
    move=> CkP CV C u s' a'.
    move=> /elpi_to_tree /(_ _ (CallS p c))/=.
    move=> /(_ _ isT erefl) [t1'[n [H3]]].
    have /= := run_is_det CkP CV.
    move => /(_ _ _ (CallS p c))/=.
    rewrite C => /(_ _ _ erefl).
    rewrite /check.is_det/=.
    move=> /(_ _ _ _ _ _ H3).
    have:= valid_tree_run _ _ H3 => /(_ isT).
    move=> [].
      move=> ->.
      rewrite t2l_dead//is_dead_dead//.
    move=> vt1' H.
    have ft1':= next_alt_None_failed H.
    have:= failed_next_alt_none_t2l vt1' ft1' H.
    by move=> ->.
  Qed.

End elpi.

(* Print Assumptions tail_cut_is_det. *)

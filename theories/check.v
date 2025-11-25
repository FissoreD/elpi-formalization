From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import ctx tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Require Import FunInd.
Functional Scheme expand_ind := Induction for step Sort Prop.

Definition sV_expand (S:sigV) Sexp:=
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
Qed.

Lemma expand_det_tree {u sP sV sV' A r s ign d} : 
  check_program sP ->
    sigma2ctx sP s = Some sV ->
      tc_tree_aux sP sV A ign = ty_ok (d, sV') ->
        step u s A = r ->
          exists S d', minD d d' = d' /\ 
          (* sV_expand sV' S /\ *)
            tc_tree_aux sP sV (get_tree r) d = ty_ok (d', S).
Proof.
  simpl in *.
  move=> C.
  move: sV sV' r d ign.
  pattern u, s, A, (step u s A).
  apply: expand_ind; clear.
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - (*here the checker comes into the game*)
    move=> /=s A pr t HA sV1 sV2 r d ign + + <-/=; clear.
    {
      rewrite/big_or.
      case X: F => /=[|[sr1 r1] rs]/=.
      - repeat eexists; rewrite minD_refl//.
      -  
    }
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
    (* apply: sV_expand_refl. *)
  - move=> s INIT A sB B HINIT dA IH sV sV' r d ign H/=.
    have ?: sB = s by admit.
    subst.
    rewrite dA.
    move=> tcA <-/=.
    rewrite get_tree_Or /= is_dead_has_cut/= dA//.
    apply: IH; eauto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    case: ifP => DA.
      by rewrite is_dead_step in eA.
    have fA:= expand_not_failed _ eA notF.
    move=> + <-{r}/=.
    (* case nB: next_alt => [B'|]//=. *)
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S']; subst.
    have {IH}/=[S[d'[H1 H2]]]:= IH _ _ _ _ _ H dtA eA.
    move=> [??]; subst.
    rewrite (expand_Exp_has_cut eA) (step_not_dead _ dA eA).
    have:= same_ty_tc_tree_aux sP sV A' DA' (if has_cut A' then maxD DA' DB else Pred).
    rewrite H2/=.
    case dtA2: (tc_tree_aux _ _ A') => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
    have:= same_ty_tc_tree_aux sP sV B ign (if has_cut A' then maxD DA' DB else Pred).
    rewrite dtB.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
    have: exists T, merge_sig S sVB = ty_ok T by admit.
    move=> [SS HH]; rewrite HH/=.
    move: dtA2 dtB1.
    case: ifP; repeat eexists => //=.
    destruct DA', DB => //=; simpl in *; subst.
    destruct DA2; [|congruence].
    have [d2[Hx]] := tc_tree_aux_func2 dtB.
    rewrite dtB1 => -[?]; subst.
    by destruct d2.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    rewrite dA.
    have fA:= expand_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S']; subst.
    move=> [??]; subst.
    have {IH}/=[S[d' [H1 H2]]] := IH _ _ _ _ _ H dtA eA.
    have := same_ty_tc_tree_aux sP sV A' DA' (if has_cut A then maxD DA' DB else Pred).
    rewrite H2/= => /eqP.
    case Hz : tc_tree_aux => //=[[Dx sX]][?]; subst sX.
    move=> <-{r}/=.
    rewrite Hz/=.
    rewrite (step_not_dead _ dA eA).
    have V := sigma2ctx_valid H.
    have:= @cutr_tc_tree_aux sP sV B (if has_cut A then maxD DA' DB else Pred) V.
    move=> [SB dtB']; rewrite dtB'/=.
    have: exists T, merge_sig S sV = ty_ok T by admit.
    move=> [SS HH]; rewrite HH/=.
    move: Hz dtB'.
    case: ifP => cA Hz dtB'; repeat eexists.
    case cA': (has_cut A').
      destruct DA', DB => //=; simpl in *; subst.
      destruct Dx; [|congruence] => /=.
      (* TODO: this is not provable in the current setting, should change the definition of tc_tree_aux if cutr is rhs of OR? *)
      admit.
    destruct DA'; simpl in *; subst => //.
    destruct DB => //=.
    admit.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have [? fA] := expand_failed_same _ eA; subst A'.
    rewrite dA.
    move=> +<-{r}/=.
    have:= same_ty_tc_tree_aux sP sV A ign d.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
    have:= same_ty_tc_tree_aux sP sV B ign d.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
    case M: merge_sig => //=[S'][??]; subst.
    rewrite dA.
    repeat eexists; case:ifP => //=.
    rewrite failed_has_cut//=.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    move=> +<-{r}/=.
    rewrite dA.
    rewrite success_has_cut//=.
    have:= same_ty_tc_tree_aux sP sV A ign d.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
    have:= same_ty_tc_tree_aux sP sV B ign d.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
    case M: merge_sig => //=[S'][??]; subst.
    repeat eexists.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/= + <-/=.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    have {IH}/=[S[d'[H1 H2]]] := IH _ _ _ _ _ H dtA1 eA.
    have:= same_ty_tc_tree_aux sP sV A' DA1 (maxD DB01 DB1).
    rewrite H2.
    case dtA1': (tc_tree_aux _ _ A') => /=[[DA1' sVA1']|]//=/eqP[?]; subst sVA1'.
    admit. (*TODO: pb with tc_tree_aux ran with a more precise subst then the hyp, should be solved using more_precise_tc_tree_aux *)
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/=.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    move=> <-{r}/=.
    admit. (*same as above...*)
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/=.
    have [? fA]:= expand_failed_same _ eA; subst A' => +<-{r}/=.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    have:= same_ty_tc_tree_aux sP sV A ign (maxD DB0 DB).
    rewrite dtA.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=/eqP[?]; subst sVA1.
    have:= same_ty_tc_tree_aux sP sVA B DA' DA1.
    rewrite dtB/=.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=/eqP[?]; subst sVB1.
    have:= same_ty_tc_tree_aux sP sVA B0 DA' DA1.
    rewrite dtB0/=.
    case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=/eqP[?]; subst sVB01.
    rewrite M/=; repeat eexists.
    destruct DB0,DB => //=; simpl in *.
    destruct DA'; simpl in *; last first.
      have [[][// _ H1]] := tc_tree_aux_func2 dtB0.
      move: dtB01; destruct DA1; rewrite ?dtB0?H1 => -[<-]/=; [|congruence].
      have [[][// _ H2]] := tc_tree_aux_func2 dtB; congruence.
    destruct ign.
      move: dtA1; rewrite dtA => -[?]; subst.
      move: dtB01; rewrite dtB0 => -[<-]/=; congruence.
    have [[][//= _]] := tc_tree_aux_func2 dtA.
    rewrite dtA1 => -[?]; subst.
    destruct DB01;[|congruence] => /=; congruence.
  - move=> s INIT A B0 B HINIT HL A' eA HR sV sV' r d ign H/= + <-{r}/=.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    have [? sA] := expand_solved_same _ eA; subst A'.
    case eB: step => //=[B'|B'|B'|B'].
    - have:= same_ty_tc_tree_aux sP sV A ign (maxD DB0 DB).
      rewrite dtA.
      case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=/eqP[?]; subst sVA1.
      have:= same_ty_tc_tree_aux sP sVA B0 DA' DA1.
      rewrite dtB0/=.
      case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=/eqP[?]; subst sVB01.
      have:= HR _ _ _ _ _ _ dtB eB.
      admit. (*PB with ctx*)
    - (*TODO: pb with cutl: no lemma for it...*)
       admit.
    - have [? fB] := expand_failed_same _ eB; subst B'.
      have:= same_ty_tc_tree_aux sP sV A ign (maxD DB0 DB).
      rewrite dtA.
      case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=/eqP[?]; subst sVA1.
      have:= same_ty_tc_tree_aux sP sVA B0 DA' DA1.
      rewrite dtB0/=.
      case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=/eqP[?]; subst sVB01.
      have:= same_ty_tc_tree_aux sP sVA B DA' DA1.
      rewrite dtB/=.
      case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=/eqP[?]; subst sVB1.
      rewrite M/=; repeat eexists.
      destruct DB0, DB => //=; simpl in *.
      destruct DA'; simpl in *; last first.
        have [[][// _ H1]] := tc_tree_aux_func2 dtB0.
        move: dtB01; destruct DA1; rewrite ?dtB0?H1 => -[<-]/=; [|congruence].
        have [[][// _ H2]] := tc_tree_aux_func2 dtB; congruence.
      destruct ign.
        move: dtA1; rewrite dtA => -[?]; subst.
        move: dtB01; rewrite dtB0 => -[<-]/=; congruence.
      have [[][//= _]] := tc_tree_aux_func2 dtA.
      rewrite dtA1 => -[?]; subst.
      destruct DB01;[|congruence] => /=; congruence.
    - have [? sB]:= expand_solved_same _ eB; subst B'.
      have:= same_ty_tc_tree_aux sP sV A ign (maxD DB0 DB).
      rewrite dtA.
      case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=/eqP[?]; subst sVA1.
      have:= same_ty_tc_tree_aux sP sVA B0 DA' DA1.
      rewrite dtB0/=.
      case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=/eqP[?]; subst sVB01.
      have:= same_ty_tc_tree_aux sP sVA B DA' DA1.
      rewrite dtB/=.
      case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=/eqP[?]; subst sVB1.
      rewrite M/=; repeat eexists.
      destruct DB0, DB => //=; simpl in *.
      destruct DA'; simpl in *; last first.
        have [[][// _ H1]] := tc_tree_aux_func2 dtB0.
        move: dtB01; destruct DA1; rewrite ?dtB0?H1 => -[<-]/=; [|congruence].
        have [[][// _ H2]] := tc_tree_aux_func2 dtB; congruence.
      destruct ign.
        move: dtA1; rewrite dtA => -[?]; subst.
        move: dtB01; rewrite dtB0 => -[<-]/=; congruence.
      have [[][//= _]] := tc_tree_aux_func2 dtA.
      rewrite dtA1 => -[?]; subst.
      destruct DB01;[|congruence] => /=; congruence.
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A s' B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> 
    sigma2ctx sP s = Some sV ->
    tc_tree_aux sP sV A Func = ty_ok (Func, sV') -> is_det s A.
Proof.
  rewrite/is_det.
  move=> ckP ++ u s' B n H.
  elim: H sV sV'; clear -ckP => //=.
  - move=> s1 s2 A B sA _ <- sV sV' H1 H2.
    by have /=-> := success_det_tree_next_alt sA H2.
  - move=> s1 s2 r A B n eA _ IH sV sV' H1 dtA.
    have /= [S' [d [<- H]]]:= expand_det_tree ckP H1 dtA eA; subst.
    apply: IH (H1) H.
  - move=> s1 s2 r A B n eA _ IH sV sV' H1 dtA.
    have /= [S' [d [<- H]]]:= expand_det_tree ckP H1 dtA eA; subst.
    apply: IH (H1) H.
  - move=> s1 s2 A B r n fA nA _ IH sV sV' H1 H2.
    have V := sigma2ctx_valid H1.
    have := failed_det_tree_next_alt false V H2 nA.
    move => -[[]// [s [? [X _]]]]//.
    apply: IH (H1) X.
  - move=> *.
    rewrite is_dead_next_alt//is_dead_dead//.
Qed.

Definition det_tree sP A := typ_func (tc_tree_aux sP empty_ctx A Func).

Lemma main {sP p t}:
  check_program sP -> det_tree sP (CallS p t) -> 
    is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det.
  case D: tc_tree_aux => //=[[[] S]]//=.
  move=> H1 H2 u s' B n H.
  apply: run_is_det H; eauto.
  rewrite/sigma2ctx//.
Qed.

Print Assumptions  main.

Module elpi.
  From det Require Import elpi elpi_equiv.
  From det Require Import tree t2l_prop tree_valid_state tree_prop.

  Definition is_det g := forall u s' a',
    nur u [::] g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c ign}: 
    check_program sP -> 
      check_callable sP [::] c Func = ty_ok (Func, ign) -> 
      is_det ((call p c):::nilC).
  Proof.
    simpl in *.
    move=> H1 H2 u s' a'.
    move=> /elpi_to_tree /(_ _ (CallS p c))/=.
    move=> /(_ _ isT erefl) [t1'[n [H3 H4]]].
    have /= := run_is_det H1 .
    move=> /(_ [::] ign [::] (CallS p c) erefl)/=.
    rewrite H2/= => /(_ erefl).
    (* rewrite H2/= => /(_ isT). *)
    rewrite /check.is_det -H4.
    move=> /(_ _ _ _ _ H3).
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

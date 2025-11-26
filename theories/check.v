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

Definition typ_func (A: typecheck (_ * sigV)%type) := match A with ty_ok (Func, _) => true | _ => false end.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  valid_sig sV ->
  (check_atoms sP sV l r) = tc_tree_aux sP sV (big_and p l) r.
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r V.
  case: A => //=.
    rewrite -IH//; case C: check_atoms => //=[[??]]; rewrite maxD_refl//merge_refl//.
    rewrite IH// in C.
    apply: tc_tree_aux_valid_sig V C.
  move=> C.
  case X: check_callable => //=[[D S]].
  have [H V'] := check_callable_valid_sig V X.
  rewrite maxD_comm H.
  rewrite -IH//=; case C1: check_atoms => //=[[D1 S1]].
  rewrite maxD_refl merge_refl//.
  rewrite IH// in C1.
  by apply: (tc_tree_aux_valid_sig _ C1).
Qed.

(* given a ty_ok term, then back_chaining return a type_checkable tree *)
Lemma ty_ok_backchain {sP sV2 b u pr t s r}:
  sigma2ctx sP s = Some sV2 ->
  check_program sP ->
  check_tm sP sV2 (Callable2Tm t) = ty_ok b ->
    F u pr t s = r ->
      all (fun (r:(Sigma * R)) => 
        is_ty_ok (check_atoms sP sV2 (premises r.2) Func) ||
        is_ty_ok (check_atoms sP sV2 (premises r.2) Pred)
        ) r.
Proof.
  move=> + CKPR +<-{r}.
  rewrite/F/=.
  elim: t s sV2 b => //.
  - move=> /= k s A b H1 _ {b}.
    case L: lookup => [m|]//=.
    have:= CKPR pr.
    case: pr L => //= rules modes _ L {}CKPR.
    clear -CKPR H1.
    elim: rules CKPR k m s A H1 => //=r rs IH /andP[+ H].
    case: r => [hd bo]/=.
    case C: check_rule => //=[[]]//= _ k m s A H1.
    case HH: lang.H => //=[s1|]; [|by auto].
    move: C; rewrite/check_rule.
    rewrite /RCallable_sig.
    case HDS: get_tm_hd_sig => //=[hds].
    case AssHd: assume_hd => //=[Shd].
    case CAT: check_atoms => //=[[DAT SAT]]/=.
    case: ifP => //= H2.
    rewrite (IH H k m _ _ H1) andbT.
    move=> H3 {IH}.
    admit.
  - move=> k s A b H1 _ {b}.
    case T: tm2RC => //=[R].
    case L: lookup => [m|]//=.
    have:= CKPR pr.
    case: pr L => //= rules modes _ L {}CKPR.
    clear -CKPR H1.
    elim: rules CKPR R m s A H1 => //=r rs IH /andP[+ H].
    case: r => [hd bo]/=.
    case C: check_rule => //=[[]]//= _ k m s A H1.
    case HH: lang.H => //=[s1|]; [|by auto].
    move: C; rewrite/check_rule.
    rewrite /RCallable_sig.
    case HDS: get_tm_hd_sig => //=[hds].
    case AssHd: assume_hd => //=[Shd].
    case CAT: check_atoms => //=[[DAT SAT]]/=.
    case: ifP => //= H2.
    rewrite (IH H k m _ _ H1) andbT.
    move=> H3 {IH}.
    admit.
  - move=> c IH t s A b H/=.
    case C: (check_tm _ _ (Callable2Tm _)) => //=[[[[|m tl tr] D]|]]//; last first.
      move=> [?]; subst.
      case T1: tm2RC => //=[V].
      (* V has a rigid head *)
      case L: lookup => //=[M].
      (*  *)

Abort.

Lemma expand_det_tree {u sP sV sVx sV' A r s ign d} : 
  check_program sP ->
    sigma2ctx sP s = Some sVx ->
      more_precise sVx sV ->
      tc_tree_aux sP sV A ign = ty_ok (d, sV') ->
        step u s A = r ->
          exists S d', minD d d' = d' /\ 
          (* sV_expand sV' S /\ *)
            tc_tree_aux sP sV (get_tree r) d = ty_ok (d', S).
Proof.
  simpl in *.
  move=> CKPR.
  move: sV sV' sVx r d ign.
  pattern u, s, A, (step u s A).
  apply: expand_ind; clear -CKPR.
  - move=> s []//= _ ?????? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - move=> s []//= _ ?????? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - move=> s []//= _ ?????? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - (*here the checker comes into the game*)
    move=> /=s A pr t HA sV1 sV2 sVx r d ign + + + <-/=; clear -CKPR.
    {
      move=> H1 H2.
      rewrite/big_or.
      case X: F => /=[|[sr1 r1] rs]/=.
      - repeat eexists; rewrite minD_refl//.
      - case C: check_callable => //=[[D SIG]][??]; subst.
        move: C; rewrite /check_callable.
        case C: check_tm => //=[[[S B]|]]//=; last first.
          rewrite/get_callable_hd_sig/get_tm_hd_sig.
          case HD: get_tm_hd => //=[E|[P|V]]; [by destruct t|..].
            case LP: lookup => //=[VP|]; last first.
              move=> [??]; subst; rewrite maxD_comm/=.
              (* a big_or always produces a tc valid tree  *)
              admit.
            case A: assume_call => //=[V] [??]; subst; rewrite maxD_comm//=.
              (* a big_or always produces a tc valid tree  *)
            admit.
          case LP: lookup => //=[VP|]; last first.
            move=> [??]; subst; rewrite maxD_comm/=.
              (* a big_or always produces a tc valid tree  *)
            admit.
          case A: assume_call => //=[V'] [??]; subst; rewrite maxD_comm//=.
          (* a big_or always produces a tc valid tree  *)
          admit.
        case: S C => //=-[]//= d1.
        case: B; last first.
          (* miscall *)
          move=> + [??]; subst.
          rewrite maxD_comm/=.
          (* a big_or always produces a tc valid tree  *)
          admit.
        (* THIS A GOOD CALL!! *)
        move=> H.
        have : exists T d0, get_callable_hd_sig sP sV1 t = Some T /\ 
          get_sig_hd T = d d0 /\ minD d0 d1 = d0.
          admit. (*TODO: THIS IS INTERESTING TO PROVE*)
        move=> [S[d0 [H3 [H4 H5]]]].
        rewrite H3/=.
        case ASS: assume_call => //=[SEND] [??]; subst.
        rewrite maxD_comm -maxD_assoc maxD_refl.
        destruct d1 => //=; last first.
          (* a big_or always produces a tc valid tree  *)
          admit.
        destruct ign => //=; last first.
          (* a big_or always produces a tc valid tree  *)
          admit.
        (* !!! THIS IS THE TRULY INTERESTING CASE !!! *)
        destruct d0; subst => //=.
        admit.
    }
  - move=> s []//= _ ?????? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
  - move=> s INIT A sB B HINIT dA IH sV sV' sVx r d ign H/= MP.
    rewrite is_dead_is_ko//=.
    have ?: sB = s by admit.
    subst.
    move=> tcA <-/=.
    rewrite get_tree_Or /= is_dead_is_ko//.
    apply: IH; eauto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' sVx r d ign H/= MP.
    case: ifP => kA.
      by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA <-{r}/=.
      rewrite kB.
      have {IH}/=[S[d'[H1 H2]]]:= IH _ _ _ _ _ _ H MP dtA eA.
      rewrite H2.
      rewrite is_ko_tc_tree_aux//=?(sigma2ctx_valid H)//.
      case: ifP; repeat eexists; auto.
      rewrite minD_refl//.
      admit.
    have fA:= expand_not_failed _ eA notF.
    move=> + <-{r}/=.
    (* case nB: next_alt => [B'|]//=. *)
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S']; subst.
    have {IH}/=[S[d'[H1 H2]]]:= IH _ _ _ _ _ _ H MP dtA eA.
    move=> [??]; subst.
    case kA' : (is_ko A'); last first.
      rewrite (expand_Exp_has_cut eA).
      have:= same_ty_tc_tree_aux sP sV A' DA' (if has_cut A' then maxD DA' DB else Pred).
      rewrite H2/=.
      case dtA2: (tc_tree_aux _ _ A') => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
      have:= same_ty_tc_tree_aux sP sV B ign (if has_cut A' then maxD DA' DB else Pred).
      rewrite dtB.
      case dtB1: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
      have: exists T, merge_sig S sVB = ty_ok T by admit.
      move=> [SS HH]; rewrite HH/=.
      move: dtA2 dtB1.
      rewrite kB.
      case: ifP; repeat eexists => //=.
      destruct DA', DB => //=; simpl in *; subst.
      destruct DA2; [|congruence].
      have [d2[Hx]] := tc_tree_aux_func2 dtB.
      rewrite dtB1 => -[?]; subst.
      by destruct d2.
    rewrite (expand_Exp_has_cut eA) failed_has_cut?is_ko_failed//.
    move=> /=.
    have:= same_ty_tc_tree_aux sP sV B ign Pred.
    rewrite dtB; case dtB': tc_tree_aux => //=[[D1 S1]]; repeat eexists.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' sVx r d ign H/= MP.
    case: ifP => kA.
      by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA <-/=.
      rewrite (expand_CB_is_ko eA) is_ko_cutr.
      have /=[S[d'[H1 H2]]] := IH _ _ _ _ _ _ H MP dtA eA.
      by rewrite H2; repeat eexists.
    have fA:= expand_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S']; subst.
    move=> [??]; subst.
    have {IH}/=[S[d' [H1 H2]]] := IH _ _ _ _ _ _ H MP dtA eA.
    have := same_ty_tc_tree_aux sP sV A' DA' (if has_cut A then maxD DA' DB else Pred).
    rewrite H2/= => /eqP.
    case Hz : tc_tree_aux => //=[[Dx sX]][?]; subst sX.
    move=> <-{r}/=.
    rewrite Hz/=.
    rewrite (expand_CB_is_ko eA).
    have V := sigma2ctx_valid H.
    rewrite cutr_tc_tree_aux//=.
    have: exists T, merge_sig S sV = ty_ok T by admit.
    move=> [SS HH]; rewrite HH/=.
    move: Hz.
    rewrite is_ko_cutr.
    case: ifP => cA; repeat eexists.
    destruct DA'; simpl in *; subst => //.
    destruct DB => //=.
    congruence.
    admit.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' sVx r d ign H/= MP.
    have [? fA] := expand_failed_same _ eA; subst A'.
    case: ifP => kA.
      move=> dtB <-/=; rewrite kA.
      have:= same_ty_tc_tree_aux sP sV B ign d.
      rewrite dtB.
      case dtB': tc_tree_aux => //=[[D1 S1]]/=/eqP[?]; subst.
      repeat eexists; destruct d => //=.
      have:= tc_tree_aux_func2 dtB; rewrite dtB'.
      move=> [][]//=[]// _ []//.
    case: ifP => kB.
      move=> dtA <-{r}/=; rewrite kB kA.
      have:= same_ty_tc_tree_aux sP sV A ign d.
      rewrite dtA.
      case dtB': tc_tree_aux => //=[[D1 S1]]/=/eqP[?]; subst.
      repeat eexists; destruct d => //=.
      have:= tc_tree_aux_func2 dtA; rewrite dtB'.
      move=> [][]//=[]// _ []//.
    move=> +<-{r}/=.
    have:= same_ty_tc_tree_aux sP sV A ign d.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
    have:= same_ty_tc_tree_aux sP sV B ign d.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
    case M: merge_sig => //=[S'][??]; subst.
    rewrite kA kB.
    repeat eexists; case:ifP => //=.
    rewrite failed_has_cut//=.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' sVx r d ign H/= MP.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    case: ifP => kB.
      move=> dtA <-{r}/=; rewrite success_is_ko// kB.
      have:= same_ty_tc_tree_aux sP sV A ign d.
      rewrite dtA.
      case dtB': tc_tree_aux => //=[[D1 S1]]/=/eqP[?]; subst.
      repeat eexists; destruct d => //=.
      have:= tc_tree_aux_func2 dtA; rewrite dtB'.
      by move=> [][]//=[]// _ []//.
    move=> +<-{r}/=.
    rewrite success_has_cut//=.
    have:= same_ty_tc_tree_aux sP sV A ign d.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[[DA2 sVA2]|]//=/eqP[?]; subst sVA2.
    have:= same_ty_tc_tree_aux sP sV B ign d.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[[DB2 sVB2]|]//=/eqP[?]; subst sVB2.
    case M: merge_sig => //=[S'][??]; subst.
    rewrite success_is_ko// kB.
    repeat eexists.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' sVx r d ign H/= MP + <-/=.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=.
    case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=.
    case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=.
    case dtB1: (tc_tree_aux _ _ B) => /=[[DB1 sVB1]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    have {IH}/=[S[d'[H1 H2]]] := IH _ _ _ _ _ _ H MP dtA1 eA.
    have:= same_ty_tc_tree_aux sP sV A' DA1 (maxD DB01 DB1).
    rewrite H2.
    case dtA1': (tc_tree_aux _ _ A') => /=[[DA1' sVA1']|]//=/eqP[?]; subst sVA1'.
    admit. (*TODO: pb with tc_tree_aux ran with a more precise subst then the hyp, should be solved using more_precise_tc_tree_aux *)
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' sVx r d ign H/= MP.
    have fA:= expand_not_failed _ eA notF.
    rewrite failed_is_ko//=.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    move=> <-{r}/=.
    admit. (*same as above...*)
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' sVx r d ign H/= MP.
    have [? fA]:= expand_failed_same _ eA; subst A' => +<-{r}/=.
    case:ifP => kA.
      move=> [??]; subst; repeat eexists; rewrite minD_refl//.
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
    destruct DB01 => /=;congruence.
  - move=> s INIT A B0 B HINIT HL A' eA HR sV sV' sVx r d ign H MP /= + <-{r}/=.
    have [? sA] := expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    case eB: step => //=[B'|B'|B'|B']; rewrite success_is_ko//?success_cut//.
    - have:= same_ty_tc_tree_aux sP sV A ign (maxD DB0 DB).
      rewrite dtA.
      case dtA1: (tc_tree_aux _ _ A) => /=[[DA1 sVA1]|]//=/eqP[?]; subst sVA1.
      have:= same_ty_tc_tree_aux sP sVA B0 DA' DA1.
      rewrite dtB0/=.
      case dtB01: (tc_tree_aux _ _ B0) => /=[[DB01 sVB01]|]//=/eqP[?]; subst sVB01.
      (* have: exists XX, sigma2ctx sP (get_substS s A) = Some XX /\ more_precise XX sVA.
        admit.
      move=> [XX [HH ZZ]].
      have:= HR _ _ _ _ _ _ HH ZZ dtB eB.
      move=> /=[S1[D1[Hx Hy]]].
      have:= same_ty_tc_tree_aux sP sVA B' DB DA1.
      rewrite Hy.
      case dtB': tc_tree_aux => //=[[D S]]/eqP[?]; subst S.
      have: exists T, merge_sig S1 sVB0 = ty_ok T by admit.
      move=> [T H1]; rewrite H1; repeat eexists.
      destruct DB0, DB; simpl in *; subst => //=.
      have:= tc_tree_aux_func2 dtA.
      rewrite dtA1/= => -[d2[H2 [?]]]; subst.
      have:= tc_tree_aux_func2 dtB'.
      rewrite Hy/= => -[d3[H3 [?]]]/=; subst.
      simpl in *; subst.
      have [d3[H4 H5]] := tc_tree_aux_func2 dtB01.
      destruct d2; simpl in *; subst.
        destruct D; try congruence.
        destruct DB01, d3; try congruence.

      destruct d3; simpl in *; subst => //=.
      rewrite dtB0/= => -[d4[H4 [?]]]/=; subst.
      simpl in *; subst.
      destruct DB01 => //=.

      rewrite Hy. *)
      admit. (*PB with ctx*)
    - have V := sigma2ctx_valid H.
      rewrite cutl_tc_tree_aux//;[|admit]; rewrite cutr_tc_tree_aux//=; [|admit].
      have /= := HR _ _ _ _ _ _ _ _ dtB eB.
      admit. (*PB with ctx*)
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
    have V := sigma2ctx_valid H1.
    have /= [S' [d [<- H]]]:= expand_det_tree ckP H1 (more_precise_refl V) dtA eA; subst.
    apply: IH (H1) H.
  - move=> s1 s2 r A B n eA _ IH sV sV' H1 dtA.
    have V := sigma2ctx_valid H1.
    have /= [S' [d [<- H]]]:= expand_det_tree ckP H1 (more_precise_refl V) dtA eA; subst.
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

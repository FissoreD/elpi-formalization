From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

(* TODO:
A valid state for substitutions is mandatory?
Given the following program execution
(main X) => (p X, q X) => p X succeeds setting X to func, then
OK, (r X \/ s X) => backchain for q X gives two solutions
Is it important that the substitution in the Or note, X is a function?
*)


Require Import FunInd.
Functional Scheme expand_ind := Induction for expand Sort Prop.

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
      det_tree_aux sP sV A ign = ty_ok (d, sV') ->
        expand u s A = r ->
          exists S d', minD d d' = d' /\ 
          (* sV_expand sV' S /\ *)
            det_tree_aux sP sV (get_tree r) d = ty_ok (d', S).
Proof.
  simpl in *.
  move=> C.
  move: sV sV' r d ign.
  pattern u, s, A, (expand u s A).
  apply: expand_ind; clear.
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
    (* apply: sV_expand_refl. *)
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
    (* apply: sV_expand_refl. *)
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
    (* apply: sV_expand_refl. *)
  - admit.
  - move=> s []//= _ ???? _ _ [_ ->] <-/=; repeat eexists; rewrite ?minD_refl//.
    (* apply: sV_expand_refl. *)
  - move=> s INIT A sB B HINIT dA IH sV sV' r d ign H/=.
    rewrite is_dead_next_alt//= => dtB<-{r}.
    have ?: sB = s by admit.
    subst.
    have:= IH _ _ _ _ _ _ _ erefl.
    move=> /(_ _ _ _ _ H dtB).
    move=> [S[d' [H1 H2]]].
    rewrite get_tree_Or/= is_dead_next_alt//= H2.
    by repeat eexists; eauto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have fA:= expand_not_failed _ eA notF.
    rewrite next_alt_not_failed//=.
    move=> + <-{r}/=.
    case nB: next_alt => [B'|]//=.
      case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S']; subst.
      have {IH}/=[S[d'[H1 H2]]]:= IH _ _ _ _ _ H dtA eA.
      move=> [??]; subst.
      case nA: next_alt => [A''|]//=; last first.
        have:= same_ty_det_tree_aux sP sV B ign (if has_cut A then maxD DA' DB else Pred).
        rewrite dtB/=; case dtB': det_tree_aux => //=[[D' sVx]] /eqP[?]; subst sVx.
        repeat eexists.
        move: dtB'.
        case: ifP => //=cA.
        case N: maxD => //=.
        destruct DA', DB => //=.
        have [[] [//= _ {}H]] := det_tree_aux_func2 dtB.
        rewrite H; congruence.
      have:= same_ty_det_tree_aux sP sV A' DA'(if has_cut A then maxD DA' DB else Pred).
      rewrite H2; case dtA' : det_tree_aux => //=[[Dx Sx]] /eqP[?]; subst Sx.
      have:= same_ty_det_tree_aux sP sV B ign (if has_cut A then maxD DA' DB else Pred).
      rewrite dtB/=; case dtB': det_tree_aux => //=[[Dy Sy]] /eqP[?]; subst Sy.
      case M1: merge_sig => /=[S'|].
        repeat eexists.
        move: dtB' dtA'.
        case: ifP => cA//.
        destruct DA' => //=.
        destruct DB => //=.
        rewrite H2 => +[?]; subst.
        have [[][//_ Hz]] := det_tree_aux_func2 dtB.
        rewrite Hz => -[?]; subst; rewrite maxD_comm/=.
        simpl in H1; subst.
        rewrite (expand_Exp_has_cut _ eA)//=.
      (* BELOW: SHOULD NOT BE REACHABLE: merge_sig S sVB is a ty_ok *)
      (* sV1 <= sVA
          sV1 <= sVB
          sVA + sVB = sV2
          sV1 <= S 
          ==========> 
          goal: merge_sig S sVB = ty_ok
          IDEA: all vars in S have "compatible" with sVA
          and all variables not appearing in sVA are also not in sVB, i.e. they are fresh

          FORMALLY:
          forall x \in S, if x \in sVA, then they are compatible,
                          else x is not in sVB
      *)
      idtac.
      admit.
    move=> H2.
    have /=[S[d' [H3 H4]]]  := IH _ _ _ _ _ H H2 eA.
    rewrite H4/=.
    have /= [d1[MM ->]]:= next_alt_None_dt sP sV d nB.
    case: eqP => Hz; repeat eexists; auto.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have fA:= expand_not_failed _ eA notF.
    rewrite next_alt_not_failed//=.
    move=> + <-{r}/=.
    rewrite (is_ko_det_tree_aux is_ko_cutr)/=(is_ko_next_alt _ is_ko_cutr)/=.
    case nB: next_alt => [B'|]//=.
      case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S']; subst.
      move=> [??]; subst.
      have /=[S[d' [H1 H2]]] := IH _ _ _ _ _ H dtA eA.
      have := same_ty_det_tree_aux sP sV A' DA' (if has_cut A then maxD DA' DB else Pred).
      rewrite H2/= => /eqP.
      case Hz : det_tree_aux => //=[[Dx sX]][?]; subst sX.
      case: eqP; repeat eexists; rewrite //=?minD_refl//=.
      move: Hz.
      case:ifP => //= cA.
      destruct DA'; simpl in *; subst => //.
      destruct DB => //=; congruence.
    move=> H2.
    have /=[S[d' [H0 H1]]]  := IH _ _ _ _ _ H H2 eA.
    rewrite H1/=.
    by case:ifP => //=; repeat eexists; auto; rewrite minD_refl.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have [? fA] := expand_failed_same _ eA; subst A'.
    move=> +<-{r}/=.
    case nA: next_alt => [A'|]//=; last first.
      move=> H2.
      have := same_ty_det_tree_aux sP sV B ign d.
      rewrite H2/=; case H3: det_tree_aux => /=[[D1 Sx]|] => //=/eqP[?]; subst Sx.
      repeat eexists.
      destruct d => //=.
      have [d2[H4 H5]]:= det_tree_aux_func2 H2.
      destruct d2 => //=.
      congruence.
    case nB: next_alt => [B'|]//=; last first.
      move=> H2.
      have [d2[H3 H4]]:= det_tree_aux_func2 H2.
      rewrite minD_comm in H3.
      destruct d; simpl in H3; subst.
        by rewrite H4; repeat eexists.
      move=>/=.
      have := same_ty_det_tree_aux sP sV A ign Pred.
      by rewrite H2/=; case: det_tree_aux => //= -[]//=; repeat eexists.
    case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    pose X := if has_cut A then maxD DA' DB else Pred.
    rewrite -/X.
    have := same_ty_det_tree_aux sP sV A ign X.
    rewrite dtA; case dtA': det_tree_aux => //=[[d' blah]]/eqP[?]; subst blah.
    have := same_ty_det_tree_aux sP sV B ign X.
    rewrite dtB; case dtB': det_tree_aux => //=[[d1 blah]]/eqP[?]; subst blah.
    rewrite M/=; repeat eexists.
    move: dtA' dtB'; rewrite/X.
    case:ifP => // c.
    destruct DA' => //=.
    destruct DB => //=.
    have [[][//_ ->]] := det_tree_aux_func2 dtA.
    move=> [?]; subst => /=.
    have [[][//_ ->]] := det_tree_aux_func2 dtB; congruence.
  - move=> s INIT A sB B HINIT dA IH A' eA sV sV' r d ign H/=.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    move=> +<-{r}/=.
    rewrite next_alt_not_failed?success_failed//=.
    case nB: next_alt => [B'|]//=; last first.
      move=> H2; have [d2[H3 H4]] := det_tree_aux_func2 H2.
      have := same_ty_det_tree_aux sP sV A ign d.
      rewrite H2; case dtA': det_tree_aux => //=[[d' blah]]/eqP[?]; subst blah.
      repeat eexists; destruct d2; simpl in H3; subst => //.
      destruct d => //=; congruence.
    case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    have [d2[H2 H3]] := det_tree_aux_func2 dtB.
    have [d3[H4 H5]]:= det_tree_aux_func2 dtA.
    pose X := if has_cut A then maxD DA' DB else Pred.
    rewrite -/X.
    have := same_ty_det_tree_aux sP sV A ign X.
    rewrite dtA; case dtA': det_tree_aux => //=[[d' blah]]/eqP[?]; subst blah.
    have := same_ty_det_tree_aux sP sV B ign X.
    rewrite dtB; case dtB': det_tree_aux => //=[[d1 blah]]/eqP[?]; subst blah.
    rewrite M/=; repeat eexists.
    move: dtA' dtB'; rewrite/X.
    case:ifP => // c.
    destruct DA' => //=.
    destruct DB => //=.
    have [[][//_ ->]] := det_tree_aux_func2 dtA.
    move=> [?]; subst => /=.
    have [[][//_ ->]] := det_tree_aux_func2 dtB; congruence.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/=.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite fA (next_alt_not_failed fA)//= sA/=.
    move=> + <-{r}/=.
    case nB0: next_alt => [B0'|]//=.
      case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S'][??]; subst.
      rewrite orbF andbF/=.
      have {IH}/=[S[d'[H4 H5]]] := IH _ _ _ _ _ H dtA eA.
      case nA: next_alt => [A''|]//=; last first.
        repeat eexists; rewrite minD_refl//.
      have [d0[//H2 H3]] := det_tree_aux_func2 dtB.
      case: ifP => fA'.
        have := same_ty_det_tree_aux sP sV A' DA' (maxD DB0 DB).
        rewrite H5; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
        (* in S there are more assignemnts than in sV *)
        (* all of this new assigments will never appear in B0
            all output are the same more precise
        *)
        admit. (*PB WITH SIG*)
      rewrite orbF.
      case: ifP.
        move=> /andP[sA' /eqP nA'].
        have [dd[//H6 H7]] := next_alt_None_dt sP sV (maxD DB0 DB) nA'.
        rewrite H7/=.
        case nB: next_alt => [B'|]//=; last first.
          by repeat eexists; rewrite minD_refl.
        (* (DEAD \/ (OK /\ ... ! /\ ... OK) \/ Any) /\ B  -> OK /\ B *)
        admit. (*PB WITH SIG*)
      have := same_ty_det_tree_aux sP sV A' DA' (maxD DB0 DB).
      rewrite H5; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
      case sA' : success => //=.
        move=> {nA A''}.
        case nA: next_alt => [A''|]//= _.
        admit. (*PB WITH SIG*)
      move=> _.
      admit. (*PB WITH SIG*)
    case nB: next_alt => [B'|]//=.
      case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S'][??]; subst.
      rewrite orbF andbT.
      case nA: next_alt => [A''|]//=; last first; rewrite?orbF?orbT/=.
        repeat eexists; rewrite minD_refl//.
      rewrite andbT.
      case: ifP => fA'.
        repeat eexists; rewrite minD_refl//.
      rewrite fA'.
      have [dd[//H2 H3]] := det_tree_aux_func2 dtB.
      have [d2[H4 H5]] := det_tree_aux_func2 dtA.
      have {IH}/=[S[d'[H6 H7]]] := IH _ _ _ _ _ H dtA eA.
      have := same_ty_det_tree_aux sP sV A' DA' (maxD DB0 DB).
      rewrite H7; case dtA': det_tree_aux => //=[[d3 blah]]/eqP[?]; subst blah.
      case: ifP => sA'.
        admit. (*PB WITH SIG*)
      admit. (*PB WITH SIG*)
    move=> [??]; subst.
    rewrite andbT orbT; repeat eexists; rewrite minD_refl//.
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/=.
    have fA:= expand_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite fA (next_alt_not_failed fA)//= sA/= => +<-{r}/=.
    case nB0: next_alt => [B0'|]//=.
      case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S'][??]; subst.
      rewrite orbF andbF/=.
      case nA: next_alt => [A''|]//=; last first.
        by repeat eexists; rewrite minD_refl.
      have [xx[//H2 H3]] := det_tree_aux_func2 dtB.
      have /=[S[d'[H4 H5]]] := IH _ _ _ _ _ H dtA eA.
      have := same_ty_det_tree_aux sP sV A' DA' (maxD DB0 DB).
      rewrite H5; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
      case: ifP => fA'.
        admit. (*PB WITH SIG*)
      rewrite orbF/=.
      case:ifP => H1/=.
        case:ifP.
          repeat eexists; rewrite minD_refl//.
        move=> /eqP nB.
        admit. (*PB WITH SIG*)
      admit. (*PB WITH SIG*)
    rewrite !orbT/=!andbT/=.
    case nB: next_alt => [B'|]//=; rewrite?orbF ?orbT/=; last first.
      by move=> [??]; subst; repeat eexists; rewrite minD_refl.
    case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
    case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case M: merge_sig => //=[S'][??]; subst.
    case fA': failed => /=.
      repeat eexists.
      by rewrite minD_refl.
    rewrite next_alt_not_failed//=.
    case:ifP => sA'.
      admit. (*PB WITH SIG*)
    have /=[S[d'[H4 H5]]] := IH _ _ _ _ _ H dtA eA.
    have := same_ty_det_tree_aux sP sV A' DA' (maxD DB0 DB).
    rewrite H5; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
    admit. (*PB WITH SIG*)
  - move=> s INIT A B0 B HINIT IH A' eA sV sV' r d ign H/=.
    have [? fA]:= expand_failed_same _ eA; subst A' => +<-{r}/=.
    rewrite fA/=.
    case:ifP => H1.
      move=> [??]; subst.
      by repeat eexists; rewrite minD_refl.
    case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//= dtB0.
    have:= same_ty_det_tree_aux sP sV A ign d.
    rewrite dtA; case dtA' : det_tree_aux => /=[[DA'' blah]|]//=/eqP[?]; subst blah.
    have:= same_ty_det_tree_aux sP sVA B0 DA' DA''.
    rewrite dtB0; case dtB0' : det_tree_aux => /=[[DB0'' blah]|]//=/eqP[?]; subst blah.
    repeat eexists.
    destruct d => //=.
    move: H1.
    case nB0: next_alt => [B0'|]//=; rewrite orbF.
    case nA: next_alt => [A'|]//= _.
    have /=[S[d'[H4 H5]]] := IH _ _ _ _ _ H dtA eA.
    destruct DA'; destruct DA''; simpl in H4; try congruence.
    have [[][//_]] := det_tree_aux_func2 dtB0; congruence.
  - move=> s INIT A B0 B HINIT HL A' eA HR sV sV' r d ign H/=.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    have fA:= success_failed _ sA.
    rewrite sA fA (next_alt_not_failed fA)/=.
    case e1: expand => //=[B'|B'|B'|B'].
    - have fB:= expand_not_failed _ e1 notF.
      have sB:= expand_not_solved_not_success _ e1 notF.
      rewrite (next_alt_not_failed fB)//= andbF/=.
      move=> + <-{r}/=; rewrite fA sA/= (next_alt_not_failed fA)/=.
      case nA: next_alt => [A'|]//=.
        case nB0: next_alt => [B0'|]//=.
          case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
          case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
          case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
          case M: merge_sig => //=[S'][??]; subst.
          have := same_ty_det_tree_aux sP sV A ign (maxD DB0 DB).
          rewrite dtA; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
          
          have := same_ty_det_tree_aux sP sVA B0 DA' d2.
          rewrite dtB0; case dtB0': det_tree_aux => //=[[d3 blah]]/eqP[?]; subst blah.

          have /= := HR _ _ _ _ _ _ dtB e1.
          (*PB WITH IH*)
          admit.
        move=> dtB.
        case nB: next_alt => [B''|]//=.
          apply: HR _ _ _ _ _ _ dtB e1.
          admit. (*PB WITH IH*)
        repeat eexists; rewrite minD_refl//.
      case nB0: next_alt => [B0'|]//=.
        case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=dtB.
        have := same_ty_det_tree_aux sP sV A ign d.
        rewrite dtA; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
        case:eqP => nB'.
          by repeat eexists; rewrite minD_refl.
        admit.
      move=> dtB.
      case nB: next_alt => [B''|]//=.
        apply: HR dtB e1.
        admit.
      repeat eexists; rewrite minD_refl//.
    - have fB:= expand_not_failed _ e1 notF.
      have sB:= expand_not_solved_not_success _ e1 notF.
      rewrite (next_alt_not_failed fB)//= andbF/=.
      move=> + <-{r}/=.
      rewrite (is_ko_next_alt _ is_ko_cutr)/=.
      rewrite failed_success_cut success_cut sA/=next_alt_cutl/=.
      rewrite (@next_alt_not_failed (cutl A))/=; last first.
        rewrite failed_success_cut success_cut sA//.
      case nA: next_alt => [A'|]//=.
        case nB0: next_alt => [B0'|]//=.
          case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
          case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
          case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
          case M: merge_sig => //=[S'][??]; subst.
          case: eqP => nB'.
            by repeat eexists; rewrite minD_refl//.
          admit.
        move=> H1.
        case nB: next_alt => [B''|]/=; last first.
          by repeat eexists; rewrite minD_refl.
        apply: HR _ _ _ _ _ _ H1 e1.
        admit.
      case nB0: next_alt => [B0'|]//=.
        case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
        case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=[??]; subst.
        case nB: next_alt => [B''|]/=; last first.
          by repeat eexists; rewrite minD_refl.
        have [d1[H1]] := next_alt_None_dt sP sV ign nA.
        rewrite dtA => -[??]; subst.
        apply: HR dtB e1.
        admit.
      move=> dtB.
      case nB: next_alt => [B''|]/=; last first.
        by repeat eexists; rewrite minD_refl.
      apply: HR dtB e1.
      admit.
    - have [? fB]:= expand_failed_same _ e1; subst B' => +<-{r}/=.
      rewrite fA/=sA (next_alt_not_failed fA)/=.
      case nB0: (next_alt _ B0) => [B0'|]//=.
        rewrite orbF/=.
        case nA: next_alt => [A'|]//=.
          case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
          case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
          case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
          case M: merge_sig => //=[S'][??]; subst.
          have := same_ty_det_tree_aux sP sV A ign (maxD DB0 DB).
          rewrite dtA; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
          have := same_ty_det_tree_aux sP sVA B DA' d2.
          rewrite dtB; case dtB': det_tree_aux => //=[[d3 blah]]/eqP[?]; subst blah.
          have := same_ty_det_tree_aux sP sVA B0 DA' d2.
          rewrite dtB0; case dtB0': det_tree_aux => //=[[d4 blah]]/eqP[?]; subst blah.
          rewrite M/=.
          repeat eexists.
          destruct DB0, DB => //=; simpl in *.
          have /=[Sx [d'[H1 H2]]] := HL _ _ _ _ _ H dtA eA.
          admit.
        case nB: next_alt => [B''|]//=.
          case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
          move=>dtB.
          have := same_ty_det_tree_aux sP sV A ign d.
          rewrite dtA; case dtA': det_tree_aux => //=[[d2 blah]]/eqP[?]; subst blah.
          have := same_ty_det_tree_aux sP sVA B DA' d2.
          rewrite dtB; case dtB': det_tree_aux => //=[[d3 blah]]/eqP[?]; subst blah.
          repeat eexists.
          have /=[Sx [d'[H1 H2]]] := HL _ _ _ _ _ H dtA eA.
          destruct d => //=.
          admit.
        move=> [??]; subst.
        by repeat eexists; rewrite minD_refl.
      case nB: next_alt => [B'|]//=; last first.
        move=> [??]; subst.
        by repeat eexists; rewrite minD_refl.
      rewrite orbT/= => dtB.
      have:= same_ty_det_tree_aux sP sV B ign d.
      rewrite dtB; case dtB' : det_tree_aux => /=[[DB' blah]|]//=/eqP[?]; subst blah.
      repeat eexists.
      destruct d => //=.
      have [[][//_ ]] := det_tree_aux_func2 dtB.
      congruence.
    - have [? sB]:= expand_solved_same _ e1; subst B'.
      have fB:= success_failed _ sB.
      move=> +<-{r}/=; rewrite fA sA /=.
      rewrite (next_alt_not_failed fB) andbF/=.
      rewrite (next_alt_not_failed fA)/=.
      case nA: next_alt => [A'|]//=.
        case nB0: (next_alt _ B0) => [B0'|]//=.
          case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
          case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
          case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
          case M: merge_sig => //=[S'][??]; subst.
          have /=[Sx [d'[H1 H2]]] := HL _ _ _ _ _ H dtA eA.
          (* have /= := HR _ _ _ _ _ _ _ dtB e1. *)
          have:= same_ty_det_tree_aux sP sV A ign (maxD DB0 DB).
          rewrite dtA; case dtA' : det_tree_aux => /=[[DA'' blah]|]//=/eqP[?]; subst blah.
          have:= same_ty_det_tree_aux sP sVA B0 DA' DA''.
          rewrite dtB0; case dtB0' : det_tree_aux => /=[[DB0'' blah]|]//=/eqP[?]; subst blah.
          have:= same_ty_det_tree_aux sP sVA B DA' DA''.
          rewrite dtB; case dtB' : det_tree_aux => /=[[DB'' blah]|]//=/eqP[?]; subst blah.
          rewrite M/=.
          repeat eexists.
          destruct DB0 => //=.
          destruct DB => //=.
          simpl in *.
          have [[][//_ H3]] := det_tree_aux_func2 dtB0.
          have [[][//_ H4]] := det_tree_aux_func2 dtB.
          destruct DA''.
            have->/=: DB0'' = Func by congruence.
            by have->/=: DB'' = Func by congruence.
          destruct DA'; simpl in H1; subst => //=; try congruence.
          admit. (*PB with max DB0 DB*)
        move=> dtB.
        have:= same_ty_det_tree_aux sP sV B ign d.
        rewrite dtB; case dtB' : det_tree_aux => /=[[DB' blah]|]//=/eqP[?]; subst blah.
        repeat eexists.
        destruct d => //=.
        have [[][//_ ]] := det_tree_aux_func2 dtB.
        congruence.
      case nB0: (next_alt _ B0) => [B0'|]//=.
        case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=dtB.
        have:= same_ty_det_tree_aux sP sV A ign d.
        rewrite dtA; case dtA' : det_tree_aux => /=[[DA'' blah]|]//=/eqP[?]; subst blah.
        have:= same_ty_det_tree_aux sP sVA B DA' DA''.
        rewrite dtB; case dtB' : det_tree_aux => /=[[DB' blah]|]//=/eqP[?]; subst blah.
        repeat eexists.
        destruct d => //=.
        have [[][//_ ]] := det_tree_aux_func2 dtB.
        destruct DA''; [congruence|].
        destruct DA'; [|congruence].
        have [[][//_ ]] := det_tree_aux_func2 dtA.
        destruct DB'; try congruence.
      move=> H1.
      have:= same_ty_det_tree_aux sP sV B d ign.
      rewrite H1; case dtB' : det_tree_aux => /=[[DB' blah]|]//=/eqP[?]; subst blah.
      repeat eexists.
      destruct d => //=.
      have [[][//]]:= det_tree_aux_func2 H1.
      congruence.
Admitted.

(* 
  Given a checked program, and a deterministic tree,
  then calling expand produces a tree which is still deterministic.
*)
Lemma expand_det_tree1 {u sP sV sV' A r s ign d} : 
  check_program sP ->
    sigma2ctx sP s = Some sV ->
      det_tree_aux sP sV A ign = ty_ok (d, sV') ->
        expand u s A = r ->
          exists S d', minD d d' = d' /\ sV_expand sV' S /\
            det_tree_aux sP sV (get_tree r) d = ty_ok (d', S).
Proof.
  simpl in *.
  rewrite/check_program.
  move=> ckP; elim: A sV sV' r s ign d.
  - move=> sV1 sV2 r s ign d H [??] <-; subst => /=; repeat eexists; rewrite ?minD_refl//.
    apply: sV_expand_refl.
  - move=> sV1 sV2 r s ign d H [??] <-; subst => /=; repeat eexists; rewrite ?minD_refl//.
    apply: sV_expand_refl.
  - move=> sV1 sV2 r s ign d H [??] <-; subst => /=; repeat eexists; rewrite ?minD_refl//.
    apply: sV_expand_refl.
  - admit.
  - move=> sV1 sV2 r s ign d H [??] <-; subst => /=; repeat eexists.
    apply: sV_expand_refl.
  - move=> A HA s B HB sV1 sV2 r s'/= ign d H.
    case: (ifP (is_dead A)) => DA.
      {
        move=> +<-{r}; rewrite get_tree_Or/=.
        rewrite !(is_dead_det_tree_aux DA)//=.
        rewrite (is_dead_next_alt _ DA)/=.
        have? : s = s' by admit. (*should say something on the tree: I have s in the or node*)
        subst.
        move=> H2.
        by have:= HB _ _ _ _ _ _ H H2 erefl.
      }
    case e: expand => [A'|A'|A'|A']//=.
    - have fA:= expand_not_failed _ e notF.
      rewrite next_alt_not_failed//=.
      move=> + <-{r}/=.
      case nB: next_alt => [B'|]//=.
        case dtA: (det_tree_aux _ _ A) => /=[[DA' sVA]|]//=.
        case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
        case M: merge_sig => //=[S']; subst.
        move=> [??]; subst.
        case nA: next_alt => [A''|]//=; last first.
          have:= same_ty_det_tree_aux sP sV1 B ign (if has_cut A then maxD DA' DB else Pred).
          rewrite dtB/=; case dtB': det_tree_aux => //=[[D' sV']] /eqP[?]; subst.
          repeat eexists.
          move: dtB'.
          case: ifP => //=cA.
          case N: maxD => //=.
          destruct DA', DB => //=.
          have [[] [//= _ {}H]] := det_tree_aux_func2 dtB.
          rewrite H; congruence.
          rewrite/sV_expand => k.
          case X: lookup => //=[Se].
          case Y: lookup => //=[Sf|].
          admit.
        have {HA}/=[S[d'[H1 [Hx H2]]]]:= HA _ _ _ _ _ _ H dtA e.
        have:= same_ty_det_tree_aux sP sV1 A' DA'(if has_cut A then maxD DA' DB else Pred).
        rewrite H2; case dtA' : det_tree_aux => //=[[Dx Sx]] /eqP[?]; subst Sx.
        have:= same_ty_det_tree_aux sP sV1 B ign (if has_cut A then maxD DA' DB else Pred).
Abort.

Definition is_det s A := forall u s' B n,
  runb u s A s' B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> 
    sigma2ctx sP s = Some sV ->
    det_tree_aux sP sV A Func = ty_ok (Func, sV') -> is_det s A.
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
    apply: IH (H1) _.
    have V := sigma2ctx_valid H1.
    have := failed_det_tree_next_alt false V H2.
    rewrite nA/= => -[d']; rewrite minD_comm/=.
    move=> [<-{d'}]->//.
  - move=> *.
    rewrite is_dead_next_alt//is_dead_dead//.
Qed.

Definition det_tree sP A := typ_func (det_tree_aux sP empty_ctx A Func).

Lemma main {sP p t}:
  check_program sP -> det_tree sP (CallS p t) -> 
    is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det.
  case D: det_tree_aux => //=[[[] S]]//=.
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

From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop.
From det Require Import tree_vars elpi_clean_ca.

Section NurEqiv.
  Variable (u : Unif).
  Variable (p : program).

  Lemma tree_to_elpi fv A s1 B s2 b s0:
    vars_tree A `<=` fv -> vars_sigma s1 `<=` fv ->
    valid_tree A ->
      run u p fv s1 A (Some s2) B b -> 
        exists x xs,
          t2l A s1 nilC = x ::: xs /\
          nur u p fv x.1 x.2 xs s2 (t2l B s0 nilC).
  Proof.
    move=> +++H.
    remember (Some _) as r eqn:Hr.
    elim: H s2 Hr s0; clear => //.
    + move=> s1 _ A _ sA fv <-<- _ [<-] sIgn fvP fvP' vA; subst.
      rewrite (success_t2l sIgn)//.
      repeat eexists.
      apply: StopE.
    + move=> s1 s2 r A B n fv fv' eA rB IH s4 ? sIgn fvP1 fvP2 vA; subst.
      have ?:= tree_fv_step_cut eA; subst.
      have {IH} //= [|[sy y]/=[ys [+ H4]]]:= IH _ erefl sIgn _ fvP2 (valid_tree_step vA eA).
        by apply/fsubset_trans/fvP1/vars_tree_step_cut/eA.
      have H5 := step_cb_same_subst1 vA eA; subst.
      have [x[tl[H1 H2]]] := [elaborate s2l_CutBrothers s1 nilC vA eA].
      rewrite H1 H2 H5 => -[???]; subst.
      repeat eexists; by apply CutE.
    + move=> s1 s2 r A B n fv fv' eA rB IH s4 ? sIgn fvP1 fvP2 vA; subst. 
      have /=vB:= (valid_tree_step vA eA). 
      have fA := step_not_failed eA notF.
      have [s[x[xs +]]] := failed_t2l vA fA s1 nilC.
      move=> H; rewrite H; repeat eexists.
      have [fvB fvs] := vars_tree_step_sub_flow fvP1 fvP2 eA.
      have [[sy y][ys /=[+ {}IH]]]:= IH _ erefl sIgn fvB fvs vB.
      case: x H => [|g gs].
        fNilG => H.
        have [] := s2l_empty_hd_success vA (step_not_failed eA notF) H.
        rewrite (step_not_solved eA notF)//.
      fConsG g gs.
      case: g => [[|c] ca] H; last first.
        have:= s2l_Expanded_call vA eA H.
        move=> []?; subst.
        case X: bc => [fv2 rules][?]; subst.
        case: rules X => [|r0 rs] X [fB Hx]; rewrite Hx; subst.
          by move=> ->; apply: FailE X _.
        move=> [???]; subst.
        rewrite cats0 in IH.
        by apply: CallE X _.
      have [[[? SS] H1]] := s2l_Expanded_cut vA eA H; subst.
      rewrite cats0 => ->[???]; subst.
      by apply: CutE.
    + move=> s1 s2 A B r n fv fA nA H IH s3 ? sIgn fvP1 fvP2 vA; subst.
      have vB := valid_tree_next_alt vA nA.
      have H1 := failed_next_alt_some_t2l _ vA fA nA.
      have {}fvP := vars_tree_next_alt_sub_flow fvP1 nA.
      have {IH} /= [[sx x][xs [H2 H3]]] := IH _ erefl sIgn fvP fvP2 vB.
      by rewrite H1; eauto.
  Qed.
  Print Assumptions tree_to_elpi.

Lemma elpi_to_tree fv s1 s2 a na g  : 
  nur u p fv s1 g a s2 na -> 
  forall s0 t, valid_tree t -> (t2l t s0 nilC) = ((s1,g) ::: a) -> 
  exists t1 n, run u p fv s0 t (Some s2) t1 n /\ t2l t1 s0 nilC = na.
Proof.
  elim; clear.
  - move=> s a fv s1 A vA /= H.
    case fA: (failed A).
      case nA: (next_alt false A) => [A'|]; last first.
        by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
      have /= fA' := next_alt_failed nA.
      have /= vA' := (valid_tree_next_alt vA nA).
      rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
      have [skA ?]:= s2l_empty_hd_success vA' fA' H; subst.
      repeat eexists.
        apply: run_fail fA nA _.
        apply: run_done => //.
      have:=@s2l_next_alt_tl _ s1 no_alt vA' skA.
      by rewrite H => ->//; rewrite behead_cons.
    have [skA ?]:= s2l_empty_hd_success vA fA H; subst.
    repeat eexists.
      by apply: run_done.
    have:=@s2l_next_alt_tl _ s1 no_alt vA skA.
    by rewrite H => ->//; rewrite behead_cons.
  - move=> s1 s2 a ca r gl fv ELPI IH s A vA H.
    {
      (* CUT CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        case X: (step u p fv s A') => [[fv' r'] A''].
        have:= next_cut_s2l fA' vA' H X => /=.
        rewrite clean_ca_nil/= => -[H1 H2].
        have /= [t1[n [{}IH H3]]] := IH _ _ (valid_tree_step vA' X) H1; subst.
        move: H2; case: ifP => Hx [??]; subst.
          repeat eexists.
          apply: run_fail fA nA _.
          apply: run_cut X IH.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step X IH.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      case X: (step u p fv s A) => [[fv' r'] A'].
      have:= next_cut_s2l fA vA H X => /=.
      rewrite clean_ca_nil/= => -[H1 H2].
      have /= [t1[n [{}IH H3]]] := IH _ _ (valid_tree_step vA X) H1; subst.
      move: H2; case: ifP => Hx [??]; subst.
        repeat eexists.
        by apply: run_cut IH.
      repeat eexists.
      by apply: run_step IH.
    }
  - move=> s1 s2 a [s0 r0]/= rs gl r t ca fv fv' B ELPI IH s3 A vA H.
    {
      (* CALL SUCCESS CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        have [] := next_callS_s2l p u fv fA' vA' H.
        rewrite B/=clean_ca_nil => H1 H2.
        have /= [t1[n [{}IH ?]]] := IH _ _ (valid_tree_step vA' erefl) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step H2 IH.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [] := next_callS_s2l p u fv fA vA H.
      rewrite B/= clean_ca_nil/= => H1 H2.
      have /= [t1[n [{}IH ?]]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
      repeat eexists.
      apply: run_step H2 IH.
    }
  - move=> s1 s2 s3 t gl a al r ca fv fv' B ELPI IH s4 A vA H.
    {
      (* CALL FAIL CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        have [] := next_callS_s2l p u fv fA' vA' H.
        rewrite B/= clean_ca_nil/= cat0s => H1 H2.
        have /= [t1[n [{}IH ?]]] := IH _ _ (valid_tree_step vA' erefl) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step H2 IH.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [] := next_callS_s2l p u fv fA vA H.
      rewrite B/= clean_ca_nil/=cat0s => H1 H2.
      have /= [t1[n [{}IH ?]]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
      repeat eexists.
      apply: run_step H2 IH.
    }
Qed.

Print Assumptions elpi_to_tree.
End NurEqiv.
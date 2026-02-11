From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree.

Section s.
  Variable u : Unif.
  (* Variable p : program. *)
  Notation runT := (runT u).

  Lemma run_success p fv A s1 r n fv1: 
    success A -> runT p fv s1 A r n fv1 -> [/\ r = Some (get_subst s1 A, next_alt true A), fv1 = fv & n = false].
  Proof.
    move=> sA H; have:= success_step u p fv s1 sA.
    have pA := success_path_atom sA.
    have fA := success_failed sA.
    inversion H; clear H; subst; rewrite success_step//; try congruence.
    by rewrite next_altFN_fail in fA.
  Qed.

  Lemma runT_det1: forall p v0 s0 t0 r1 r2 b1 b2 v1 v2,
    runT p v0 s0 t0 r1 b1 v1 -> runT p v0 s0 t0 r2 b2 v2 -> [/\ r2 = r1, v2 = v1 & b2 = b1].
  Proof.
    move=> p v0 s A r1 r2 b1 bx v1 vx H.
    elim_run H bx vx => H1.
    + by apply: run_success sA H1.
    + inversion H1; clear H1; try congruence; subst.
      - by rewrite success_path_atom in pA.
      - move: H0; rewrite eA => -[???]; subst.
        by case: (IH _ _ H3) => ???; subst.
      - by rewrite path_atom_failed in H.
      - by rewrite path_atom_next_alt_id in H.
    + inversion H1; clear H1; try congruence; subst.
        by rewrite success_failed in fA.
        by rewrite path_atom_failed in fA.      
      move: H0; rewrite nA => -[?]; subst.
      by apply: IH.
    + have fA:= next_altFN_fail nA.
      have sA := failed_success fA.
      inversion H1; subst => //; try congruence.
      by rewrite path_atom_failed in fA.
  Qed.

  (*SNIP: runT_det*)
  Lemma runT_det: forall p v0 s0 t0 r1 r2 b1 b2 v1 v2,
    runT p v0 s0 t0 r1 b1 v1 -> runT p v0 s0 t0 r2 b2 v2 -> r2 = r1 /\ v2 = v1 /\ b2 = b1.
  (*ENDSNIP: runT_det*)
  Proof.
    move=> p v0 s A r1 r2 b1 bx v1 vx H1 H2.
    by have [] := runT_det1 H1 H2 => *; subst.
  Qed.


  Lemma run_or0 p s1 sv X s Y r b fv' :
    runT p sv s1 (Or X s Y) r b fv' -> b = false.
  Proof.
    remember (Or _ _ _) as o eqn:Ho => H.
    elim_run H X s Y Ho.
    - move:  eA => /=; rewrite !push; destruct X => //=.
        rewrite !push => -[???]; subst.
        by rewrite (IH _ _ _ erefl); case_step_tag eA A => //.
      move=> [???]; subst.
      by rewrite (IH _ _ _ erefl); case_step_tag eA A => //.
    - move: fA nA => /=.
      case: X => [X|]; (case: next_alt => [?|]//) => fX.
        by move=> []/esym; apply: IH.
        by case: next_alt => //= ? [?]; subst; apply/IH.
      by move=> []/esym; apply: IH.
  Qed.

  Lemma run_ko_left2 p fv fv' s2 B B' sIgn:
    (exists b1, runT p fv s2 B B' b1 fv') <->
    runT p fv sIgn (Or None s2 B) (omap (fun '(s, x) => (s, omap (Or None s2) x)) B') false fv'.
  Proof.
    split.
      move=> [b1 HB]; elim_run HB sIgn.
      + by apply: StopT; rewrite//success_or_None.
      + by apply: StepT (IH _); rewrite/= ?(rew_pa,eA)//; destruct st.
      + by apply: BackT; rewrite//=(failed_or_None,nA).
      + by apply: FailT; rewrite//= nA.
    remember (Or _ _ _) as OR eqn:HO.
    remember (omap _ _) as M eqn:HM.
    remember false as F eqn:HF => HB.
    rename s2 into s3.
    rename B into C.
    elim_run HB s3 C B' HO HM HF.
    + move: sA HM; rewrite rew_pa/= => sC. 
      by case nB: next_alt => [C'|]//=; case: B' => //=-[s [C2 |]]//=[]*; subst;
      exists false; apply: StopT.
    + move: pA eA HF; rewrite rew_pa/= !push => pC [???]; subst.
      case eB: step => [[fvx rx] B2].
      have ? := run_or0 rB; subst.
      have [b1 {}IH] := IH _ _ _ erefl erefl erefl.
      rewrite eB/= in IH => /=.
      case: ifP; first destruct rx; move => // _ ?; subst; eexists;
      apply: StepT eB erefl IH => //.
    + move: fA nA; rewrite rew_pa/= => fC.
      case nB: next_alt => //[B2][?]; subst.
      have [? {}IH] := IH _ _ _ erefl erefl erefl.
      by eexists; apply: BackT IH.
    + destruct B' => //.
      eexists; apply: FailT => //.
      by move: nA => /=; case: next_alt.
  Qed.

  Lemma run_or_correct_left p fv fv' s1 A r b:
    runT p fv s1 A r b fv' ->
      if r is Some (s2, A') then
        forall sX X, 
        runT p fv s1 (Or (Some A) sX X) 
          (Some (s2, if A' is Some A' then
            Some (Or (Some A') sX (if b then KO else X))
          else 
            if b then None
            else omap (fun x => Or None sX x) (next_alt false X))) false fv'
      else
        if b then
          forall sX X, runT p fv s1 (Or (Some A) sX X) None false fv'
        else
          forall sX X X' n1 fv2, runT p fv' sX X X' n1 fv2 ->
          runT p fv s1 (Or (Some A) sX X) (omap (fun '(s, x) => (s, omap (Or None sX) x)) X') false fv2.
  Proof.
    move=> H; elim_run H.
    - by move=> sX X; subst => /=; apply: StopT.
    + case: r rB IH => [[s B']|].
        move=> rB IH sX X.
        case: (path_atom_exp_cut pA eA) => /=?; subst => //=; apply: StepT;
        rewrite /= ?(rew_pa,eA)//=.
        by have:= IH sX KO; rewrite !if_same//=.
      move=> HB.
      destruct b1 => //= IH.
        rewrite orbT => sX X.
        apply: StepT; rewrite/= ?(eA,rew_pa)//=.
        by destruct st.
      rewrite orbF.
      case: (path_atom_exp_cut pA eA) => /=?; subst => //=.
        move=> sX X.
        apply: StepT; rewrite/= ?(eA,rew_pa)//=.
        apply: (IH _ KO None); by apply: FailT.
      move=> sX X X' n1 fv3 H.
      apply: StepT;rewrite/= ?(eA,rew_pa)//=.
      by apply:IH H.
    + case: r rB IH => [[s B']|] rB.
        move=> IH sX X.
        apply: BackT; rewrite /=?(next_alt_dead nA)//.
        rewrite nA//.
      destruct n => //=.
        move=> IH sX X.
        by apply: BackT; rewrite //=nA.
      move=> IH sX X X' n1 fv2 H.
      apply: BackT; only 1,2: rewrite //=nA//.
      by apply: IH H.
    + move=> sX X X' n1 fv' H.
      have fB := next_altFN_fail nA.
      inversion H; subst; clear H.
      + apply: BackT => //=; first rewrite nA failedF_next_alt//.
          by rewrite success_failed.
        by apply: StopT; rewrite//=success_or_None.
      + apply: BackT => //=; first rewrite nA failedF_next_alt//.
          by rewrite path_atom_failed.
        apply: StepT; rewrite/= ?(rew_pa,H1)//; first destruct tg => //.
        by apply/run_ko_left2; exists b1.
      + apply: BackT => //=; first by rewrite H1 nA.
        by apply/run_ko_left2; exists n1.
      + by apply: FailT; rewrite /= nA H0.
  Qed.

  Definition is_or A := match A with Or _ _ _ => true | _ => false end.

  Definition is_cb_exp rx:
    (if is_cb rx then Expanded else rx) = Expanded ->
      rx = CutBrothers \/ rx = Expanded.
  Proof. by destruct rx => //=; auto. Qed.

  Definition or_succ_build_res s b B A' X :=
    if X is Some (Or Ax sx Bx) then sx = s /\ A' = Ax /\ 
      if b then Bx = KO
      else if Ax is Some Ax then Bx = B
      else Some Bx = next_alt false B
    else A' = None.

  Lemma or_succ_build_resP1 s1 b D A' r:
    or_succ_build_res s1 b KO A' r -> or_succ_build_res s1 true D A' r.
  Proof. by case: r => [[]|]//[t|]//= s t1 [->]; case: ifP => // _ []//. Qed.

  Lemma run_or_fail_L1 p b fv1 s1 Cx fv3 fn sx:
    runT p fv1 s1 Cx None b fv3 ->
    runT p fv1 s1 (Or (Some Cx) sx KO) None false fn ->
    fv3 = fn.
  Proof.
    remember None as n1 eqn:H1.
    remember (@None tree) as n2 eqn:H2 => H.
    elim_run H H1 H2.
    - inversion 1 => //; subst.
        move: H1; rewrite/=eA/=if_same => -[???]; subst.
        apply: IH => //.
        destruct b0 => //; by rewrite orbT in H2.
      - by rewrite rew_pa path_atom_failed in H0.
      by move: H0 => /=; rewrite path_atom_next_alt_id.
    - inversion 1 => //=; subst.
        by rewrite rew_pa in H0; rewrite path_atom_failed in fA.
      - apply: IH => //.
        move: H1 => /=; case nA': next_alt => //= -[?]; subst.
        by move: nA; rewrite nA' => -[?]; subst.
      by move: H0 => /=; rewrite nA.
    - have fA := next_altFN_fail nA.
      inversion 1 => //; subst.
        by rewrite rew_pa in H0; rewrite path_atom_failed in fA.
      by move: H2 => /=; rewrite nA.
  Qed.

  Lemma run_or_complete p v0 v2 s0 sm t0 t1 X:
    runT p v0 s0 (Or (Some t0) sm t1) X false v2 ->
      if X is Some (s3, X) then
        (exists t0' b, runT p v0 s0 t0 (Some (s3, t0')) b v2 /\ 
          or_succ_build_res sm b t1 t0' X /\ 
          (~~b -> X = None -> next_alt false t1 = None))
        \/
        (exists v1, runT p v0 s0 t0 None false v1 /\ 
          (if X is Some (Or (Some _ ) _ _) then false else true) /\
          exists b, runT p v1 sm t1 (Some (s3, (if X is Some (Or _ _ t1') then Some t1' else None))) b v2)
      else
        X = None /\
        exists b v1, runT p v0 s0 t0 None b v1 /\ 
          if b then  v1 = v2
          else exists b1, runT p v1 sm t1 None b1 v2.
  Proof.
    remember (Or (Some t0) _ _) as o1 eqn:Ho1.
    remember false as z eqn:Hz.
    move=> H.
    elim_run H sm t0 t1 Ho1 Hz => //.
    + rewrite rew_pa in sA; rewrite/=.
      left; case nA: next_alt => [A3|]/=.
        by repeat eexists; first apply: StopT => //=.
      repeat eexists; first apply: StopT => //=.
      move=> /=; case nB: next_alt => [B1'|]//=.
      case: next_alt => //=.
    + move: eA pA; rewrite rew_pa/=.
      rewrite !push; case eC: step => [[fvx rx] Cx]/=[???] PL; subst.
      have/= rxP:= path_atom_exp_cut PL eC.
      have ? : b1 = false by case: rxP => ?; subst.
      subst.
      have {IH} := IH _ _ _ erefl erefl.
      rewrite orbF in Hz *.
      case: r rB => [[s2 X]|] rB.
        move=> [[A'[b [rC [HS NR]]]]|[fv3[H1[H2[b HS]]]]].
          left; case: rxP => /=?; subst; repeat eexists.
            by apply: StepT eC erefl rC.
            by apply: or_succ_build_resP1 HS.
            by [].
            by apply: StepT eC erefl rC.
            by apply: HS.
          move=> /= H1 H2/=.
          by apply: NR.
        right; case: rxP => ?; subst; simpl  in HS.
          by inversion HS.
        repeat eexists.
          by apply: StepT eC erefl H1.
          by destruct X => //=.
        by apply: HS.
      move=> [?[b[fv3[H1]]]] H2; subst; split => //.
      destruct b; subst.
        exists true, v2; split => //=.
        by case: rxP => ?; subst; apply: StepT eC erefl H1.
      case: H2 => [b1 H2].
      case: rxP => ?; subst.
        repeat eexists.
          by apply: StepT eC _ H1.
        move=> //=.
        simpl in *.
        by rewrite (run_or_fail_L1 H1 rB).
      exists false.
      repeat eexists.
        by apply: StepT eC _ H1.
      apply: H2.
    + move: fA nA; rewrite rew_pa/= => fA.
      case nC: next_alt => [C'|]//=.
        move=> [?]; subst.
        have {IH} := IH _ _ _ erefl erefl.
        case: r rB => [[s2 X]|] rB/=; last first.
          move=> [?[b[fv2[H1 H2]]]]; subst; split => //; exists b, fv2; split => //.
          by apply: BackT H1.
        move=> [[A' [b [rA' [H HR]]]]|[fv2[rC' [H1 [b H]]]]].
          by left; repeat eexists; first by apply: BackT rA'.
        right; repeat eexists; last by apply H.
          by apply: BackT rC'.
        by destruct X => //.
      case nD: next_alt => //[D'][?]; subst.
      case: r rB IH => [[s2 r]|] rB IH.
        have /= := run_same_structure rB.
        case: r rB IH => [r|] rB IH/=.
          case: r rB IH => // l s3' D2 rB IH /andP[/eqP?/eqP?]; subst.
          have [b1 H] := proj2 (run_ko_left2 p v0 v1 s3' D' (Some (s2, Some D2)) s1) rB.
          destruct s2.
          right; repeat eexists.
            by apply: FailT.
          by apply: next_alt_run nD H.
        move=> _.
        have [b H] := proj2 (run_ko_left2 p v0 v1 sm D' (Some (s2, None)) s1) rB.
        destruct s2.
          right; repeat eexists; first by apply: FailT.
          apply: next_alt_run nD H.
      repeat eexists.
        by apply: FailT.
      have [b H] := proj2 (run_ko_left2 p v0 v1 sm D' None s1) rB.
      by eexists; apply: next_alt_run nD H.
    move: nA => /=.
    case nA: next_alt => //=; case nB: next_alt => //= _.
    repeat eexists; first by apply: FailT.
    move=> /=; repeat eexists.
    by apply: FailT nB.
  Qed.

  (*SNIP: runSST_or *)
  Lemma runSST_or: forall p v0 v1 s0 s1 t0 t0' sm t1,
    runT p v0 s0 t0 (Some (s1, Some t0')) true v1 ->
      runT p v0 s0 (Or (Some t0) sm t1) (Some (s1, Some (Or (Some t0') sm KO))) false v1.
  (*ENDSNIP: run_orSST *)
  Proof. move=> > /run_or_correct_left H; auto. Qed.

  (*SNIP: runSSF_or *)
  Lemma runSSF_or: forall p v0 v1 s0 s1 t0 t0' sm t1,
    runT p v0 s0 t0 (Some (s1, (Some t0'))) false v1 ->
      let sR := Some (Or (Some t0') sm t1) in
      runT p v0 s0 (Or (Some t0) sm t1) (Some (s1, sR)) false v1.
  (*ENDSNIP: run_orSSF *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runSNF_or *)
  Lemma runSNF_or: forall p v0 v1 s0 t0 s1 sm t1,
    runT p v0 s0 t0 (Some (s1, None)) false v1 ->
      let nB := (next_alt false t1) in
      let sR := (omap (Or None sm) nB) in
      runT p v0 s0 (Or (Some t0) sm t1) (Some (s1, sR)) false v1.
  (*ENDSNIP: run_orSNF *)
  Proof . move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runSNT_or *)
  Lemma runSNT_or: forall p v0 v1 s0 t0 s1 sm t1,
    runT p v0 s0 t0 (Some (s1, None)) true v1 ->
      runT p v0 s0 (Or (Some t0) sm t1) (Some (s1, None)) false v1.
  (*ENDSNIP: run_orSNT *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runNT_or *)
  Lemma runNT_or: forall p v0 v1 s0 t0 sm t1,
    runT p v0 s0 t0 None true v1 ->
      runT p v0 s0 (Or (Some t0) sm t1) None false v1.
  (*ENDSNIP: run_orNT *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runNF_or *)
  Lemma runNF_or: forall p v0 v1 v2 s0 t0 sm t1 t1' b,
    runT p v0 s0 t0 None false v1 ->
      runT p v1 sm t1 t1' b v2 ->
        let sR := (omap (fun '(x, b) => (x, omap (Or None sm) b)) t1') in
        runT p v0 s0 (Or (Some t0) sm t1) sR false v2.
  (*ENDSNIP: run_orNF *)
  Proof. by move=>> /run_or_correct_left; eauto. Qed.

  (*SNIP: run_orSST *)
  Lemma run_orSST p v0 v2 s0 s1 sm t0 t0' t1 t1':
    runT p v0 s0 (Or (Some t0) sm t1) (Some (s1, (Some (Or (Some t0') sm t1')))) false v2 ->
    exists b, runT p v0 s0 t0 (Some (s1, Some t0')) b v2 /\ t1' = if b then KO else t1.
  (*ENDSNIP: run_orSST *)
  Proof.
    move=> /run_or_complete.
    move=> [[t0''[b[H[[?[? Ht1]] H3]]]]|[t0''[H[b H1]]]]//; subst.
    exists b; split => //.
    by destruct b.
  Qed.


  Fixpoint not_bt A B :=
    match A, B with
    | Or None _ A, Or None _ B => not_bt A B
    | Or (Some A) _ _, Or (Some B) _ _ => not_bt A B
    | And Ax _ Ay, And Bx _ By => not_bt Ax Bx && not_bt Ay By
    | TA _, _ => B != KO
    | OK, OK => true
    | KO, KO => true
    | (KO|OK|Or _ _ _|And _ _ _), _ => false
    end.
End s.
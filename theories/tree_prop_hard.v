From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree.

Section s.
  Variable u : Unif.
  Variable p : program.

  Lemma run_success fv A s1 s2 r n fv1: 
    success A -> run u p fv s1 A s2 r n fv1 -> [/\ s2 = Some (get_subst s1 A), r = (next_alt true A), fv1 = fv & n = false].
  Proof.
    move=> sA H; have:= success_step u p fv s1 sA.
    have pA := success_path_atom sA.
    have fA := success_failed sA.
    inversion H; clear H; subst; rewrite success_step//; try congruence.
    by rewrite next_alt_None_failed in fA.
  Qed.

  Lemma run_consistent fv s A s1 B sn C n1 n2 fv1 fv3:
    run u p fv s A s1 B n1 fv1 -> run u p fv s A sn C n2 fv3 -> [/\ (sn = s1), (C = B), fv3 = fv1 & (n2 = n1)].
  Proof.
    move=> H.
    elim_run H sn C n2 => H1.
    + by apply: run_success SA H1.
    + inversion H1; clear H1; try congruence; subst.
      - by rewrite success_path_atom in pA.
      - move: H0; rewrite eA => -[???]; subst.
        by case: (IH _ _ _ H3) => ????; subst.
      - by rewrite path_atom_failed in H.
      - by rewrite path_atom_next_alt_id in H.
    + inversion H1; clear H1; try congruence; subst.
        by rewrite success_failed in fA.
        by rewrite path_atom_failed in fA.      
      move: H0; rewrite nA => -[?]; subst.
      by apply: IH.
    + have fA:= next_alt_None_failed nA.
      have sA := failed_success fA.
      inversion H1; subst => //; try congruence.
      by rewrite path_atom_failed in fA.
  Qed.

  Lemma run_or0 s1 sv X s Y s2 r b fv' :
    run u p sv s1 (Or X s Y) s2 r b fv' -> b = false.
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

  Lemma next_alt_run fv fv' A B C s s2 b1:
    next_alt false A = B ->
      run u p fv s (odflt A B) s2 C b1 fv' ->
        run u p fv s A s2 C b1 fv'.
  Proof.
    move=> <-{B}.
    case fA: (failed A).
      case X: next_alt => [A'|]//= H.
      by apply: run_fail fA X H.
    rewrite failedF_next_alt//.
  Qed.

  (* Lemma run_ko_left_Some_None fv fv' s2 X B r r1 b1 sIgn:
    is_ko X ->
    run u p fv sIgn (Or (Some X) s2 B) r r1 b1 fv' <->
    run u p fv sIgn (Or None s2 B) r r1 b1 fv'.
  Proof.
    move=> kX; split => H.
      inversion H; subst; clear H.
      - by move: H0 => /=; rewrite is_ko_success.
      - by move: H0; rewrite/= is_ko_step//.
      - by move: H0; rewrite/= is_ko_step//.
      - move: H0 H1 => /= fX; rewrite is_ko_next_alt//=.
        case nB: next_alt => [B2|]//=[?]; subst.
        by apply: next_alt_run; first by rewrite/=nB.
      - move: H0; rewrite /=is_ko_next_alt//=.
        case nB: next_alt => //= _.
        by apply: run_dead; rewrite/= (next_alt_None_failed nB, nB).
    inversion H; subst; clear H.
    - move: H0 => /= sB.
      case nB: next_alt => [B2|]/=.
        apply: run_fail => /=.
          by rewrite is_ko_failed.
          by rewrite is_ko_next_alt//failedF_next_alt//success_failed.
        by apply: run_done; rewrite //= nB.
      apply: run_fail => /=.
        by rewrite is_ko_failed.
        by rewrite is_ko_next_alt//failedF_next_alt//success_failed.
      by apply: run_done; rewrite //= nB.
    - move: H0; rewrite/=!push; case eB: step => //=[[fvx []] B2]//=.
    - move: H0; rewrite/=!push; case eB: step => [[fvx r'] B2]/=.
      case: ifP.
        destruct r' => // _ [??]; subst.
        apply: run_fail => /=.
          by rewrite is_ko_failed//=.
          by rewrite is_ko_next_alt//=failedF_next_alt// (step_not_failed eB)//.
        by apply: run_step H1; rewrite /=eB//=.
      move=> _ [???]; subst.
      apply: run_fail => /=.
        by rewrite is_ko_failed//=.
        by rewrite is_ko_next_alt//=failedF_next_alt// (step_not_failed eB)//.
      by apply: run_step H1; rewrite /=eB//=.
    - move: H0 H1 => /=fB.
      case nB: next_alt => //[B2][?]; subst.
      by apply: run_fail H2; rewrite//=(is_ko_failed, is_ko_next_alt)//nB.
    - move: H0 => /=; case nB: next_alt => //= _.
      by apply: run_dead; rewrite//=(is_ko_failed, is_ko_next_alt)//nB.
  Qed. *)

  Lemma run_ko_left2 fv fv' s2 B B' r sIgn:
    (exists b1, run u p fv s2 B r B' b1 fv') <->
    run u p fv sIgn (Or None s2 B) r (omap (fun x => Or None s2 x) B') false fv'.
  Proof.
    split.
      move=> [b1 HB]; elim_run HB sIgn.
      + by apply: run_done; rewrite//success_or_None.
      + by apply: run_step (IH _); rewrite/= ?(rew_pa,eA)//; destruct st.
      + by apply: run_fail; rewrite//=(failed_or_None,nA).
      + by apply: run_dead; rewrite//= nA.
    remember (Or _ _ _) as OR eqn:HO.
    remember (omap _ _) as M eqn:HM.
    remember false as F eqn:HF => HB.
    rename s2 into s3.
    rename B into C.
    elim_run HB s3 C B' HO HM HF.
    + move: SA HM; rewrite rew_pa/= => sC. 
      case nB: next_alt => [B2|]//=; destruct B' => //=.
        by move=> [?]; subst; exists false; apply: run_done.
      by move=> _; exists false; apply: run_done.
    + move: pA eA HF; rewrite rew_pa/= !push => pC [???]; subst.
      case eB: step => [[fvx rx] B2].
      have ? := run_or0 rB; subst.
      have [b1 {}IH] := IH _ _ _ erefl erefl erefl.
      rewrite eB/= in IH => /=.
      case: ifP; first destruct rx; move => // _ ?; subst; eexists;
      apply: run_step eB erefl IH => //.
    + move: fA nA; rewrite rew_pa/= => fC.
      case nB: next_alt => //[B2][?]; subst.
      have [? {}IH] := IH _ _ _ erefl erefl erefl.
      by eexists; apply: run_fail IH.
    + destruct B' => //.
      eexists; apply: run_dead => //.
      by move: nA => /=; case: next_alt.
  Qed.

  Lemma run_none_dead_res fv fv' s A B cn :
    run u p fv s A None B cn fv' -> B = None.
  Proof.
    move=> H.
    remember None as n eqn:Hn.
    by elim: H Hn.
  Qed.

  Lemma run_or_correct_left fv fv' s1 A A' s2 b:
    run u p fv s1 A s2 A' b fv' ->
      if s2 is None then
        if b then
          forall sX X, run u p fv s1 (Or (Some A) sX X) None None false fv'
        else
          forall sX X s3 X' n1 fv2, run u p fv' sX X s3 X' n1 fv2 ->
          run u p fv s1 (Or (Some A) sX X) s3 (omap (fun x => Or None sX x) X') false fv2
      else forall sX X, 
      run u p fv s1 (Or (Some A) sX X) s2 
        (if A' is Some A' then
          Some (Or (Some A') sX (if b then KO else X))
        else 
          if b then None
          else omap (fun x => Or None sX x) (next_alt false X)) false fv'.
  Proof.
    move=> H; elim_run H.
    - by move=> sX X; subst => /=; apply: run_done.
    + case: s2 rB IH => //= [s2|] HB/=.
        move=> IH sX X.
        case: (path_atom_exp_cut pA eA) => /=?; subst => //=; apply: run_step;
        rewrite /= ?(rew_pa,eA)//=.
        by have:= IH sX KO; rewrite !if_same//=.
      have ? := run_none_dead_res HB; subst.
      destruct b1 => //= IH.
        rewrite orbT => sX X.
        apply: run_step; rewrite/= ?(eA,rew_pa)//=.
        by destruct st.
      rewrite orbF.
      case: (path_atom_exp_cut pA eA) => /=?; subst => //=.
        move=> sX X.
        apply: run_step; rewrite/= ?(eA,rew_pa)//=.
        apply: (IH _ KO _ None); by apply: run_dead.
      move=> sX X s3 X' n1 fv3 H.
      apply: run_step;rewrite/= ?(eA,rew_pa)//=.
      by apply:IH H.
    + case: s2 rB IH => //[s2|] HB; auto.
        move=> IH sX X.
        apply: run_fail; rewrite /=?(next_alt_dead nA)//.
        rewrite nA//.
      destruct n => //=.
        move=> IH sX X.
        by apply: run_fail; rewrite //=nA.
      move=> IH sX X s3 X' n1 fv2 H.
      apply: run_fail; only 1,2: rewrite //=nA//.
      by apply: IH H.
    + move=> sX X s3 X' n1 fv' H.
      have fB := next_alt_None_failed nA.
      inversion H; subst; clear H.
      + apply: run_fail => //=; first rewrite nA failedF_next_alt//.
          by rewrite success_failed.
        by apply: run_done; rewrite//=success_or_None.
      + apply: run_fail => //=; first rewrite nA failedF_next_alt//.
          by rewrite path_atom_failed.
        apply: run_step; rewrite/= ?(rew_pa,H1)//; first destruct st => //.
        by apply/run_ko_left2; exists b1.
      + apply: run_fail => //=; first by rewrite H1 nA.
        by apply/run_ko_left2; exists n1.
      + by apply: run_dead; rewrite /= nA H0.
  Qed.

  Definition is_or A := match A with Or _ _ _ => true | _ => false end.

  Definition is_cb_exp rx:
    (if is_cb rx then Expanded else rx) = Expanded ->
      rx = CutBrothers \/ rx = Expanded.
  Proof. by destruct rx => //=; auto. Qed.

  Definition or_succ_build_res b B A' X :=
    if X is Some (Or Ax _ Bx) then A' = Ax /\ 
      if b then Bx = KO
      else if Ax is Some Ax then Bx = B
      else Some Bx = next_alt false B
    else A' = None.

  Lemma or_succ_build_resP1 b D A' r:
    or_succ_build_res b KO A' r -> or_succ_build_res true D A' r.
  Proof. by case: r => [[]|]//[t|]//= _ t1 [->]; case: ifP => //. Qed.

  Lemma run_or_fail_L b fv1 s1 Cx fv3 fn sx rs:
    run u p fv1 s1 Cx None None b fv3 ->
    run u p fv1 s1 (Or (Some Cx) sx KO) None rs false fn ->
    rs = None.
  Proof.
    remember None as n1 eqn:H1.
    remember (@None tree) as n2 eqn:H2 => H.
    elim_run H H1 H2.
    - inversion 1 => //; subst; last by rewrite rew_pa path_atom_failed in H0.
      apply: IH => //.
      move: H1 => /=; rewrite eA/= => -[???]; subst.
      rewrite if_same in H3.
      destruct b0 => //; by rewrite orbT in H2.
    - inversion 1 => //=; subst.
        by rewrite rew_pa in H0; rewrite path_atom_failed in fA.
      apply: IH => //.
      move: H1 => /=; case nA': next_alt => //= -[?]; subst.
      by move: nA; rewrite nA' => -[?]; subst.
    - have fA := next_alt_None_failed nA.
      inversion 1 => //; subst.
        by rewrite rew_pa in H0; rewrite path_atom_failed in fA.
      by move: H3 => /=; rewrite nA.
  Qed.

  Lemma run_or_fail_L1 b fv1 s1 Cx fv3 fn sx rs:
    run u p fv1 s1 Cx None None b fv3 ->
    run u p fv1 s1 (Or (Some Cx) sx KO) None rs false fn ->
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
    - have fA := next_alt_None_failed nA.
      inversion 1 => //; subst.
        by rewrite rew_pa in H0; rewrite path_atom_failed in fA.
      by move: H3 => /=; rewrite nA.
  Qed.

  Lemma run_or_complete fv0 fv2 s1 sx L R X s3:
    run u p fv0 s1 (Or (Some L) sx R) s3 X false fv2 ->
      if s3 is Some s3 then
        (exists L' b, run u p fv0 s1 L (Some s3) L' b fv2 /\ 
          or_succ_build_res b R L' X)
        \/
        (exists fv1, run u p fv0 s1 L None None false fv1 /\ 
          exists b, run u p fv1 sx R (Some s3) (if X is Some (Or _ _ R') then Some R' else None) b fv2)
      else
        exists b fv1, run u p fv0 s1 L None None b fv1 /\ 
          if b then X = None /\ fv1 = fv2
          else exists b1, run u p fv1 sx R None None b1 fv2.
  Proof.
    remember (Or (Some L) _ _) as o1 eqn:Ho1.
    remember false as z eqn:Hz.
    move=> H.
    elim_run H sx L R Ho1 Hz => //.
    + rewrite rew_pa in SA; rewrite/=.
      left; case nA: next_alt => [A3|]/=.
        by repeat eexists; first apply: run_done => //=.
      repeat eexists; first apply: run_done => //=.
      move=> /=; case nB: next_alt => [B1'|]//=.
    + move: eA pA; rewrite rew_pa/=.
      rewrite !push; case eC: step => [[fvx rx] Cx]/=[???] PL; subst.
      have/= rxP:= path_atom_exp_cut PL eC.
      have ? : b1 = false by case: rxP => ?; subst.
      subst.
      have {IH} := IH _ _ _ erefl erefl.
      rewrite orbF in Hz *.
      destruct s2 => //=.
        move=> [[A'[b [rC HS]]]|[fv3[H1[b HS]]]].
          left; case: rxP => /=?; subst; repeat eexists.
            by apply: run_step eC erefl rC.
            by apply: or_succ_build_resP1 HS.
            by apply: run_step eC erefl rC.
          by apply: HS.
        right; case: rxP => ?; subst; simpl  in HS.
          by inversion HS.
        repeat eexists.
          by apply: run_step eC erefl H1.
        by apply: HS.
      move=> [b[fv3[H1]]] H2.
      destruct b; subst.
        exists true, fv3; split => //=.
        by case: rxP => ?; subst; apply: run_step eC erefl H1.
      case: H2 => [b1 H2].
      case: rxP => ?; subst.
        repeat eexists.
          by apply: run_step eC _ H1.
        move=> //=.
        simpl in *.
        by rewrite (run_or_fail_L H1 rB) (run_or_fail_L1 H1 rB).
      exists false.
      repeat eexists.
        by apply: run_step eC _ H1.
      apply: H2.
    + move: fA nA; rewrite rew_pa/= => fA.
      case nC: next_alt => [C'|]//=.
        move=> [?]; subst.
        have {IH} := IH _ _ _ erefl erefl.
        destruct s2 => //=; last first.
          move=> [b[fv2[H1 H2]]]; exists b, fv2; split => //.
          by apply: run_fail H1.
        move=> [[A' [b [rA' H]]]|[fv2[rC' [b H]]]].
          by left; repeat eexists; first by apply: run_fail rA'.
        right; repeat eexists; last by apply: H.
        by apply: run_fail rC'.
      case nD: next_alt => //[D'][?]; subst.
      have /= := run_same_structure rB.
      case: r rB IH => [r|] rB IH/=.
        case: r rB IH => // l s3' D2 rB IH /andP[/eqP?/eqP?]; subst.
        have [b1 H] := proj2 (run_ko_left2 fv0 fv1 s3' D' (Some D2) s2 s1) rB.
        destruct s2.
          right; repeat eexists.
            by apply: run_dead.
          by apply: next_alt_run nD H.
        by have:= run_none_dead_res H.
      move=> _.
      have [b H] := proj2 (run_ko_left2 fv0 fv1 sx D' None s2 s1) rB.
      destruct s2.
        right; repeat eexists; first by apply: run_dead.
        apply: next_alt_run nD H.
      repeat eexists.
        by apply: run_dead.
      repeat eexists.
      by apply: next_alt_run nD H.
    move: nA => /=.
    case nA: next_alt => //=; case nB: next_alt => //= _.
    repeat eexists; first by apply: run_dead.
    move=> /=; repeat eexists.
    by apply: run_dead nB.
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

  

  (* Lemma run_or_ko_right1 fv fv' s2 X B B' SOL b1 sIgn:
    is_ko X -> run u p fv s2 B SOL B' b1 fv' ->
    run u p fv s2 (Or B sIgn X) SOL (
      if B' is Some B' then Some (Or B' sIgn (if is_dead B' then Dead else if b1 == false then X else cutr X)) else None) false fv'.
  Proof.
    move=> + HB; elim: HB sIgn X; clear.
    + move=> s _ A _ fv sA <-<- sIgn X kX; subst => /=.
      apply: run_done => /=; rewrite?sA ?(success_is_dead sA)//.
      rewrite (is_ko_next_alt _ kX).
      case W: next_alt => [A'|]//.
      rewrite (next_alt_dead W)//.
    + move=> s1 s2 r A B n fv fv' ? HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_step in HA.
      have:= IH sIgn (cutr X) is_ko_cutr.
      by rewrite cutr2 if_same//.
    + move=> s1 s2 r A B n fv fv' ? HA HB IH sIgn X kX.
      apply: run_step.
        by rewrite/= HA; case: ifP => //dA; rewrite is_dead_step in HA.
      apply: IH => //.
    + move=> s1 s2 A B r n fv ? fA nA rB IH sIgn X kX.
      apply/run_fail/IH/kX => /=.
        by rewrite fA is_ko_failed//if_same.
      rewrite (is_ko_next_alt _ kX)/=nA; case: ifP => dA//.
      by rewrite is_dead_next_alt in nA.
    + move=> s1 A fv fA nA sIgn X kX.
      apply: run_dead => /=.
        by rewrite fA is_ko_failed// if_same.
      by rewrite is_ko_next_alt//=nA if_same.
  Qed. *)

  (* Lemma run_or_ko_right2 fv fv' s2 X X' A A' SOL sIgn:
    is_ko X -> run u p fv s2 (Or A sIgn X) SOL (Some (Or A' sIgn X')) false fv' ->
      exists b1, run u p fv s2 A SOL (Some A') b1 fv' /\ X' = if b1 == false then X else cutr X.
  Proof.
    remember (Or A _ _) as o1 eqn:Ho1.
    remember (Or A' _ _) as o2 eqn:Ho2 => + H.
    elim: H A X A' X' Ho1 Ho2; clear.
    + move=> s  _ A _ fv + <-<- A1 B1 A2 B2 ? + kB'; subst => /=.
      rewrite (is_ko_success kB') (is_ko_next_alt _ kB').
      case: ifP =>// dA1 sB1.
      rewrite (is_ko_next_alt _ kB')/=.
      case X: next_alt => //=[B1'|][??]; subst.
        repeat eexists.
          apply: run_done sB1 erefl _.
          by rewrite X.
        by rewrite (next_alt_dead X)//.
      repeat eexists.
      apply: run_done sB1 erefl _.
        rewrite X//.
      rewrite is_dead_dead//.
    - move=> s1 s2 r A B n fv fv' + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      by case: ifP => dC; case X: step => [[?[]]]//.
    - move=> s1 s2 r A B n fv fv' + HB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_step _ _ _ _ kA1)//=.
      case: ifP => dC//.
      case X: step => [[?[]]D']//[??]; subst;
      have := IH _ _ _ _ erefl erefl.
        move=> /(_ kA1) [b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_step X IH.
      move=> /(_ is_ko_cutr)[b [{}IH ?]]; subst.
        repeat eexists.
        apply: run_cut X IH.
      rewrite cutr2 if_same dead_cutr.
      by rewrite (run_or0 HB)//.
    - move=> s1 s2 A B r n fv ++ rB IH A1 A2 B1 B2 ?? kA1; subst => /=.
      rewrite (is_ko_next_alt _ kA1). 
      case: ifP => //=dA H1.
      case X: next_alt => [A2'|]//=[?]; subst.
      have [b[{}IH ?]] := IH _ _ _ _ erefl erefl kA1; subst.
      repeat eexists; apply: run_fail H1 X IH.
    - move=> s1 ? fv ++ A X A' X' ? + kX; subst => /= ++[??]; subst.
      rewrite is_ko_failed//.
      case: ifP => dA H; rewrite (is_ko_next_alt _ kX).
        rewrite //is_dead_dead; repeat eexists.
        apply: run_dead (is_dead_failed dA) (is_dead_next_alt _ dA).
      case W: next_alt => //= _.
      repeat eexists.
      apply: run_dead H W.
      rewrite is_dead_dead//.
  Qed. *)

  (* Definition build_or_state cn A' X :=
    if cn == false then 
      if is_dead A' then 
        if next_alt false X is Some X' then X'
        else Dead
      else X
    else if is_dead A' then Dead else cutr X. *)

  (*Lemma failed_cutl_run A:
    failed (cutl A) -> forall s, run u p s (cutl A) None (dead A) false.
  Proof.
    Search failed cutl.
    elim: A => //=; try by move=> *; apply: run_dead => //.
    - move=> A HA s B HB + s1; case: ifP => dA/=; rewrite ?is_dead_cutl dA => F.
        have {}HB := HB F s.
        have := run_ko_left2 s1 (is_dead_is_ko dA) HB; eauto.
        rewrite/get_dead is_dead_dead andbF//.
      have {}HA := HA F s1.
      have /= := run_or_ko_right1 s (@is_ko_cutr B) HA.
      by rewrite is_dead_dead dead_cutr.
    - move=> A HA B0 B HB.
      case:ifP => //= sA.
        rewrite failed_success_cut success_cut sA/=.
        move=> fB s.
        have {}HB := HB fB (get_subst s A).
        inversion HB; clear HB; subst => //.
        - by rewrite failed_step// in H.
        - by rewrite next_alt_cutl_failed// in H0.
        - admit.
         (* rewrite dead_cutl -/(dead (And A B0 B)) -/(cutl (And A B0 B)) -dead_cutl. *)
          (* replace (And _ _ _) with (cutl (And A B0 B)); last by rewrite /=sA.
          rewrite -/(dead (And A B0 B)).
          suffices : dead (And A B0 B) = dead (cutl (And A B0 B)).
            move=> ->.
            apply: run_dead; rewrite/= sA/= success_cut sA ?fB?orbT// H3 next_alt_cutl/=.
            by destruct B0.
          move=> /=; rewrite sA/= .
          move: sA fB H; clear => /=.
          elim: 
          rewrite !next_alt_cutl/= failed_success_cut success_cut sA/= H3//. *)
      move=> _ s.
      have:= (HA _ s).
      rewrite failed_success_cut success_cut sA/=.
      move=> /(_ isT) {}HA; inversion HA; clear HA; subst.
      - rewrite failed_step//failed_success_cut success_cut sA// in H.
      - rewrite next_alt_cutl_failed// in H0.
      (* - rewrite dead_cutl -/(dead (And A B0 B)) -/(cutl (And A B0 B)) -dead_cutl.
        replace (And _ _ _) with (cutl (And A B0 B)); last first.
          rewrite/= sA//=.
        apply: run_dead; rewrite/= sA/= failed_cutr//.
        by rewrite next_alt_cutr. *)
      admit.
  Abort. *)

  (*
  Lemma run_and_correct_successL {s0 sn A B0 B A' B0' B' b}:
    success A -> next_alt true A = None ->
    run u p s0 (And A B0 B) sn (And A' B0' B') b ->
    (run u p (get_subst s0 A) B sn B' b /\ 
      (B0' = B0) /\
      (A' = if is_dead B' then dead A else if b == false then A else cutl A)
    )%type2.
  Proof.
    (* remember (And A _ _) as a eqn:Ha.
    remember (And A' _ _) as a' eqn:Ha' => ++H.
    elim: H A B0 B Ha A' B0' B' Ha'; clear => //=.
    - move=> s1 _ A _ + <-<- A1 B01 B1 ? A2 B02 B2; subst => /=/andP[sA1 sB1].
      rewrite success_failed//sA1.
      case nB1: next_alt => [B1'|]//=.
        destruct B01.
        move=> [???] _ nA2; subst.
        rewrite (next_alt_dead nB1); repeat split.
        apply: run_done sB1 erefl _.
        by rewrite nB1//.
      destruct B01.
      case nA1: next_alt => //=-[???] _ _; subst.
      rewrite success_is_dead//=.
      repeat split.
      (* rewrite is_dead_dead; repeat split. *)
      apply: run_done => //.
      rewrite nB1//=.
    - move=> s1 s3 r A B n + _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= + sA1 nA1.
      rewrite success_step//=.
      case eA1: step => //[B1'][?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl.
      rewrite next_alt_cutl success_cut => /(_ sA1 erefl).
      rewrite ges_subst_cutl// cutl2 if_same dead_cutl.
      move=> [rB1'[??]]; subst.
      rewrite cutr2 dead_cutr !if_same.
      repeat split.
      apply: run_cut eA1 rB1'.
    - move=> s1 s3 r A B n + _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= + sA1 nA1.
      rewrite success_step//=.
      case eA1: step => //[B1'][?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl.
      move => /(_ sA1 nA1).
      move=> [rB1' [??]]; subst.
      by repeat eexists; eauto; apply: run_step eA1 rB1'.
    - move=> s1 s2 A A' r n ++ _ IH A1 B01 B1 ? A2 B02 B2 ?; subst => /= ++ sA1 nA1.
      rewrite success_failed//= sA1/= nA1.
      case X: next_alt => //[B1'] fB1 [?]; subst.
      have {IH} := IH _ _ _ erefl _ _ _ erefl sA1 nA1.
      move=> [rB1' [??]]; subst.
      repeat split.
      by apply: run_fail; eauto.
    - move=> s1 B + + A1 B01 B1 ? A2 B02 B2 + sA1 nA1; subst => /=.
      rewrite success_failed// sA1/= nA1 => ++[???]; subst.
      case X: next_alt => // fB1 _.
      rewrite is_dead_dead; repeat split.
      apply: run_dead fB1 X. *)
  Abort. *)

  (* Lemma run_big_and_total {r s}:
      Texists r0 B n, run u p s ((big_and r)) r0 B n.
  Proof.
    elim: r s => //=.
    - move=> s; repeat eexists; apply: run_done => //.
    - move=> x xs IH s.
      admit.
  Admitted. *)

  (* Lemma run_big_or_total {sr r rs c s}:
    F u p c s = (sr, r) :: rs -> 
      Texists r0 B n, run u p s (TA (call c)) r0 B n.
  Proof.
    elim: rs sr r c s => //=.
    - move=> sr r c s H.
      have [r0[B [n H1]]] := @run_big_and_total (premises r) sr.
      repeat eexists.
      apply: run_step; rewrite /=/backchain?H//.
      apply: run_fail => //=.
        rewrite next_alt_big_and//.
      by apply: run_ko_left2; eauto.
    - move=> [sx r] rs IH sr r' c s H.
  Abort. *)

  (* Lemma run_is_total {s A}:
    Texists r B n, run u p s A r B n.
  Proof.
    elim: A s.
    - repeat eexists; apply: run_dead => //.
    - repeat eexists; apply: run_done => //.
    - repeat eexists; apply: run_dead => //.
    - move=> c s.
      (* case F: (F u p c s) => [|[sr r] rs].
        repeat eexists.
        apply: run_step => //.
        rewrite/backchain F; apply: run_dead => //.
      repeat eexists.
      apply: run_step => //=.
      rewrite/backchain; rewrite F.
      apply: run_fail => //=.
      admit. *)
    (* - repeat eexists; apply: run_cut => //; apply: run_done => //. *)
    (* - admit. *)
    (* - admit. *)
  Abort. *)

  (* Lemma run_and_correct {s0 sn A B0 B A' B0' B' b}:
    run u s0 (And A B0 B) sn (And A' B0' B') b ->
    if sn is Some sn then true :> Type
    else (
      run u s0 A None A' b + 
      (Texists s0', run u s0 A (Some s0') )
    
    ).
(*     true
    (Texists sm r1 b1, run u s0 A sm r1 b1 /\
      Texists b2 r2, ((run u sm B sn r2 b2) + 
        (* TODO: it should not be Texsists sm, but I should provide the right substitution *)
        (* The problem is given by a state like (A \/ B) /\ C
           A succeeds, C fails, the substitution on which we should run C0
           is the one obtained by running B (i.e. next_alt A).
        *)
        (Texists sm, run u sm B0 sn r2 b2))). *)
  Proof.
    remember (And _ _ _) as a eqn:Ha => H.
    elim: H A B0 B Ha; clear.
    - move=> s1 s2 r A B /step_success [[??]+] ? C D E ?; subst => /=.
      move=> /andP[sC sE].
      repeat eexists.
        apply: run_done (success_step _ _ sC) erefl.
      rewrite sC; left; apply: run_done erefl.
      apply: success_step sE.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: step => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_cut X IH.
      case Y: step => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= step_success _ X; subst.
      have sC' := sC.
        rewrite -success_cut in sC'.
      have {IH} [?[??]] := run_consistent _ _ IH (run_success1 _ _ sC'); subst.
      rewrite ges_subst_cutl in H2.
      case: H2 => H2.
        by repeat eexists; left; apply: run_cut Y H2.
      move: H2 => [sm H2].
      case sD: (success (cutl D)).
        have [?[??]] := run_consistent _ _ H2 (run_success1 _ _ sD); subst.
        repeat eexists; right.
        rewrite success_cut in sD.
        rewrite ges_subst_cutl.
        eexists; apply: run_success1 sD.
      have:= @failed_success_cut D.
      rewrite sD/= => H1.
      by have:= failed_cutl_run _ H1 _ _ _ _ H2.
    - move=> s1 s2 s3 r A B n + rB IH C D E ?; subst => /=.
      case X: step => //[s1' C'|s1' C'].
        move=> [??]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        repeat eexists; eauto.
        apply: run_step X IH.
      case Y: step => //=[s1'' E'][??]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done X erefl.
      have [[??]sC]:= step_success _ X; subst.
      have {IH} [?[??]] := run_consistent _ _ IH (run_success1 _ _ sC); subst.
      case: H2 => H2.
        repeat eexists; left; apply: run_step Y H2.
      by repeat eexists; eauto.
    - move=> s1 s2 A B C r n /step_failed [? +] + rC IH D E F ?; subst.
      move=> /= /orPT[fD|/andP[sD fF]].
        rewrite fD; case: ifP => //dD.
        case W: next_alt => //=[D'].
        case X: next_alt => //=[E'][?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split.
          apply: run_fail (failed_step _ fD) W IH.
        case: H2 => H2; repeat eexists; eauto.
        right; eexists; apply: next_alt_run X H2.
      rewrite success_failed// success_is_dead//sD.
      case W: next_alt => //=[F'|].
        move=>[?]; subst.
        have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
        do 3 eexists; split; eauto.
        case: H2 => H2; repeat eexists; eauto.
        left; apply: next_alt_run W H2.
      case X: next_alt => //=[D'].
      case Y: next_alt => //=[E'][?]; subst.
      have [sm[r1[b1 [{}IH [b2[r2 H2]]]]]]:= IH _ _ _ erefl.
      do 3 eexists; split.
        apply: run_done erefl.
        apply: success_step sD.
      case: H2 => H2; repeat eexists.
        right; eexists; apply: next_alt_run Y _.
        eauto.
      repeat eexists; right; eauto.
  Qed. *)
End s.
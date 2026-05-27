From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree.

Section s.
  Variable u : Unif.
  Notation runT := (runT u).

  Lemma run_success p fv A s1 r n fv1: 
    success A -> runT p fv s1 A r n fv1 -> 
      [/\ match prune true A with None => r = One (next_subst s1 A) | Some t => r = Many (next_subst s1 A) t end, fv1 = fv & n = false].
  Proof.
    move=> sA H; have:= success_step u p fv s1 sA.
    have pA := success_incomplete sA.
    have fA := success_failed sA.
    inversion H; clear H; subst; rewrite success_step//; try congruence.
      rewrite H2 => //.
      rewrite H2 => //.
    by rewrite prune_None in fA.
  Qed.

  Lemma run_successS p fv A s1 r n fv1 t: 
    success A -> runT p fv s1 A r n fv1 -> prune true A = Some t ->
      [/\ r = Many (next_subst s1 A) t, fv1 = fv & n = false].
  Proof. by move=> S R P; have := run_success S R; rewrite P. Qed.

  Lemma run_successN p fv A s1 r n fv1: 
    success A -> runT p fv s1 A r n fv1 -> prune true A = None ->
      [/\ r = One (next_subst s1 A), fv1 = fv & n = false].
  Proof. by move=> S R P; have := run_success S R; rewrite P. Qed.

  Lemma runT_det1: forall p v0 s0 t0 r1 r2 b1 b2 v1 v2,
    runT p v0 s0 t0 r1 b1 v1 -> runT p v0 s0 t0 r2 b2 v2 -> [/\ r2 = r1, v2 = v1 & b2 = b1].
  Proof.
    move=> p v0 s A r1 r2 b1 bx v1 vx H.
    elim_run H bx vx => H1.
    + by apply: run_successN H1 NN.
    + by apply: run_successS H1 NS.
    + inversion H1; clear H1; try congruence; subst.
      - by rewrite success_incomplete in pA.
      - by rewrite success_incomplete in pA.
      - move: H0; rewrite eA => -[???]; subst.
        by case: (IH _ _ H2) => ???; subst.
      - by rewrite incomplete_failed in H.
      - by rewrite incpl_prune in H.
    + inversion H1; clear H1; try congruence; subst.
        by rewrite success_failed in fA.
        by rewrite success_failed in fA.
        by rewrite incomplete_failed in fA.      
      move: H0; rewrite nA => -[?]; subst.
      by apply: IH.
    + have fA:= prune_None nA.
      have sA := failed_success fA.
      inversion H1; subst => //; try congruence.
      by rewrite incomplete_failed in fA.
  Qed.

  (*SNIPT: runT_det*)
  Lemma runT_det: 
    forall p v0 s t r r' b b' v v', runT p v0 s t r b v -> 
      runT p v0 s t r' b' v' -> r' = r /\ v' = v /\ b' = b.
  (*ENDSNIPT: runT_det*)
  Proof.
    move=> p v s A r1 r2 b1 bx v1 vx H1 H2.
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
      case: X => [X|]; (case: prune => [?|]//) => fX.
        by move=> []/esym; apply: IH.
        by case: prune => //= ? [?]; subst; apply/IH.
      by move=> []/esym; apply: IH.
  Qed.

  Definition map_many f m :=
    match m with
    | Many s l => Many s (f l)
    | _ => m end.

  Lemma runT_Nor_elim p fv fv' s2 R B b sIgn:
    runT p fv sIgn (Or None s2 B) R b fv' ->
      exists b1,
      match R with
      | Many sk l => exists2 B', l = Or None s2 B' & runT p fv s2 B (Many sk B') b1 fv'
      | Zero => runT p fv s2 B Zero b1 fv'
      | One s => runT p fv s2 B (One s) b1 fv'
      end.
  Proof.
    remember (Or _ _ _) as OR eqn:HO.
    move => HB.
    rename s2 into s3.
    rename B into C.
    elim_run HB s3 C HO.
    + move: sA; rewrite rew_pa/= => sC.
      eexists; apply: StopOT => //.
      by move: NN => /=; case: prune.
    + move: sA; rewrite rew_pa/= => sC.
      move: NS => /=; case P: prune => //[C']/=[<-{B}].
      by repeat eexists; apply: StopMT => //.
    + move: pA eA; rewrite rew_pa/= => pC.
      case eB: step => [[fvx rx] B2][???]; subst.
      have {IH}[b] := IH _ _ erefl.
      case: r {rB} => [|s|??[z ?]] IH; subst;
      by repeat eexists; apply: StepT eB IH.
    + move: fA nA; rewrite rew_pa/= => fC.
      case nB: prune => //[B2][?]; subst.
      have [b {IH}] := IH _ _ erefl.
      case: r {rB} => [|s|??[z ?]] IH; subst;
      by repeat eexists; apply: BackT IH.
    + eexists; apply: FailT => //.
      by move: nA => /=; case: prune.
  Qed.

  Lemma runT_Nor_intro p fv fv' s2 B B' sIgn b1:
    runT p fv s2 B B' b1 fv' -> runT p fv sIgn (Or None s2 B) 
      (map_many (fun x => (Or None s2 x)) B') false fv' .
  Proof.
    move=> HB; elim_run HB sIgn.
    + by apply: StopOT; rewrite //=(rew_pa,NN).
    + by apply: StopMT; rewrite//=(rew_pa,NS).
    + by apply: StepT' (IH _); rewrite/= ?(rew_pa,eA)//; destruct st.
    + by apply: BackT; rewrite//=(failed_or_None,nA).
    + by apply: FailT; rewrite//= nA.
  Qed.

  Lemma run_or_correct_left p fv fv' s1 A r b:
    runT p fv s1 A r b fv' ->
      match r with
      | Zero => 
        if b then
          forall sX X, runT p fv s1 (Or (Some A) sX X) Zero false fv'
        else
          forall sX X X' n1 fv2, runT p fv' sX X X' n1 fv2 ->
          runT p fv s1 (Or (Some A) sX X) (map_many (Or None sX) X') false fv2
      | One s2 => forall sX X, 
        runT p fv s1 (Or (Some A) sX X) 
          (if b then One s2 else 
            if prune false X is Some x then (Many s2 (Or None sX x))
            else One s2) false fv'
      | Many s2 A' =>
        forall sX X, 
        runT p fv s1 (Or (Some A) sX X) 
          (Many s2 (Or (Some A') sX (if b then KO else X))) false fv'
      end.
  Proof.
    move=> H; elim_run H.
    + by move=> sX X; case P: prune => [X'|]/=; [apply: StopMT|apply: StopOT]; rewrite//= NN P.
    + by move=> sX X; apply: StopMT;rewrite //=NS.
    + case: r rB IH => [|s2|s2 A'] rB.
      - case: b1 rB => rB IH.
          rewrite orbT => sX X.
          case: (incomplete_exp_cut pA eA) => /= ?; subst =>/=;
          by apply: StepT' (IH _ _); rewrite//=?(rew_pa,eA)//=.
        rewrite orbF.
        case: (incomplete_exp_cut pA eA) => /= ?; subst => /=sX X.
          apply: StepT' => /=; rewrite?eA//=; cycle 1.
          by apply: (IH _ _ Zero); apply: FailT.
          by [].
        move=> X' n1 fv2 H; apply: StepT'; rewrite/=?eA//=.
          by [].
        apply: IH H.
      - move=> IH sX X; apply: StepT'; rewrite/=?eA//; first by destruct st.
        rewrite/is_cb eq_sym; case: eqP => cb; subst => //=.
        by have:= IH _ KO => //=; rewrite if_same//.
      move=> IH sX X; apply: StepT'; rewrite/=?eA//; first by destruct st.
      rewrite/is_cb eq_sym; case: eqP => cb; subst => //=.
      by have:= IH _ KO => //=; rewrite if_same//.      
    + case: r rB IH => [|s2|s2 A'] rB.
      - case: n rB => /=rB IH sX X => [|X' n1 fv2 H]; apply: BackT; rewrite/=?nA//.
        by apply: IH H.
      - by move=> H sX X; apply: BackT; rewrite/=?nA//.
      - by move=> H sX X; apply: BackT; rewrite/=?nA//.
    + move=> sX X X' n1 fv' H.
      have fB := prune_None nA.
      inversion H; subst; clear H.
      + apply: BackT => //=; first rewrite nA failedF_prune//.
          by rewrite success_failed.
        by apply: StopOT; rewrite//=(rew_pa,H2).
      + apply: BackT => //=; first rewrite nA failedF_prune//.
          by rewrite success_failed.
        by apply: StopMT; rewrite//=(rew_pa,H2).
      + apply: BackT => //=; first rewrite nA failedF_prune//.
          by rewrite incomplete_failed.
        apply: StepT'; rewrite/= ?(rew_pa,H1)//; first destruct tg => //.
        by apply: runT_Nor_intro H2.
      + apply: BackT => //=; first by rewrite H1 nA.
        by apply: runT_Nor_intro H2.
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
      else Some Bx = prune false B
    else A' = None.

  Lemma or_succ_build_resP1 s1 b D A' r:
    or_succ_build_res s1 b KO A' r -> or_succ_build_res s1 true D A' r.
  Proof. by case: r => [[]|]//[t|]//= s t1 [->]; case: ifP => // _ []//. Qed.

  Lemma run_or_fail_L1 p b b1 fv1 s1 Cx fv3 fn sx:
    runT p fv1 s1 Cx Zero b fv3 ->
    runT p fv1 s1 (Or (Some Cx) sx KO) Zero b1 fn ->
    fv3 = fn.
  Proof.
    move=> H1 H2.
    have:= run_or_correct_left H1.
    destruct b.
      by move=>/(_ sx KO) H; have [_[]] := runT_det H H2.
    move=> H; have:= H sx KO Zero false fv3 => {}H.
    have [|_[]//] := runT_det H2 (H _).
    by apply: FailT.
  Qed.

  Lemma run_or_complete b p v0 v2 s0 sm t0 t1 X:
    runT p v0 s0 (Or (Some t0) sm t1) X b v2 ->
      match X with
      | Zero =>
          exists b, exists2 v1, runT p v0 s0 t0 Zero b v1 &
            if b then  v1 = v2
            else exists b1, runT p v1 sm t1 Zero b1 v2
      | One s3 =>
        (* TODO: legare t1 con la soluzione *)
        (exists2 b, runT p v0 s0 t0 (One s3) b v2 & (~~b -> prune false t1 = None))
        \/
        (exists2 v1, runT p v0 s0 t0 Zero false v1 & exists b, runT p v1 sm t1 (One s3) b v2)
      | Many s3 X =>
        (exists Ax, exists2 b, 
          runT p v0 s0 t0 (if Ax is Some Ax then Many s3 Ax else One s3) b v2 &
          exists2 Bx, 
            X = Or Ax sm Bx &
            (if b then Bx = KO
            else if Ax is Some Ax then Bx = t1
            else Some Bx = prune false t1)) \/
        (exists2 v1, runT p v0 s0 t0 Zero false v1 &
          match X with
          | Or None _ t1' => exists b, runT p v1 sm t1 (Many s3 t1') b v2
          | _ => false
          end)
      end.
  Proof.
    remember (Or (Some t0) _ _) as o1 eqn:Ho1.
    move=> H.
    elim_run H sm t0 t1 Ho1 => //.
    + move: NN; rewrite/=; case Pt0 : prune => //=.
      case Pt1: prune => //= _.
      left; eexists => //.
      by apply: StopOT.
    + move: NS; rewrite/=; case Pt0 : prune => [t0'|]//=.
        move=> [<-{B}]; rewrite rew_pa in sA; left.
        exists (Some t0'), false.
          by apply: StopMT.
        by repeat eexists.
      case Pt1: prune => [t1'|]//=[<-{B}].
      left; exists None, false; repeat eexists.
      by apply: StopOT.
    + move: eA pA; rewrite rew_pa/=.
      case eA: step => [[? tg] t0'][???] I; subst.
      have {IH} := IH _ _ _ erefl.
      case: r rB => [|s|s t] rB.
      - move=> [[][fv' H]].
          by case: (incomplete_exp_cut I eA) => /=??; 
          subst; (repeat eexists; first apply: StepT eA H).
        move=> [b Hx]; case: (incomplete_exp_cut I eA) => /=?; 
        subst; (repeat eexists; first apply: StepT eA H) => //=.
          by inversion Hx.
        by eauto.
      - move=> [[b R H]|[v H1 [b H2]]].
          by case: (incomplete_exp_cut I eA) => /=?; subst;left; 
          (repeat eexists; first apply: StepT eA R).
        case: (incomplete_exp_cut I eA) => /=?; subst;right.
          by inversion H2 => //.
        repeat eexists; first apply: StepT eA H1 => //.
        apply: H2.
      move=> [].
        move=> [t'[b H [Bx ? Hx]]]; subst.
        case: (incomplete_exp_cut I eA) => /=?; subst; left; 
        (repeat eexists; first apply: StepT eA H) => //=.
        by destruct b, t' => //.
      move=> [f2 H1].
      destruct t => //; destruct o => //-[b].
      case: ifP => CB H3; first by inversion H3; subst; destruct t.
      right; eexists.
        by destruct tg => //; apply: StepT eA H1.
      by eauto.
    + move: fA nA; rewrite rew_pa/= => fA.
      case nC: prune => [C'|]//=.
        move=> [?]; subst.
        have {IH} := IH _ _ _ erefl.
        case: r rB => [|s|s r] rB.
        - by move=> [b[fv H1 H2]]; repeat eexists; first by apply: BackT H1.
        - by move=> [[b H1 H2]|[f H1 [x H2]]]; [left|right]; (repeat eexists; first apply: BackT H1); eauto.
        move=> [].
          move=> [t[b H[Bx Hx]]]; subst; left.
          by repeat eexists; first apply: BackT H => //.
        move=> [fv H1 H2].
        by right; repeat eexists; first (by apply: BackT H1); eauto.
      case Pt1: prune => [t1'|]//=[?]; subst.
      have [b] := runT_Nor_elim rB.
      case: r {IH rB} => [|s|s t].
      - move=> H; repeat eexists; first apply: FailT => //.
        case: (boolP (failed t1)) => ft.
          by repeat eexists; apply: BackT H => //.
        by have:= failedF_prune (negbTE ft); rewrite Pt1 => -[<-]; eauto.
      - move=> H; right; eexists; first by apply: FailT.
        case: (boolP (failed t1)) => ft; first by eexists; apply: BackT H.
        have:= failedF_prune (negbTE ft); rewrite Pt1 => -[<-]; eauto.
      move=> [B' ? H]; subst; right.
      eexists; first by apply: FailT.
      case: (boolP (failed t1)) => ft; first by eexists; apply: BackT H.
      have:= failedF_prune (negbTE ft); rewrite Pt1 => -[<-]; eauto.
    + move: nA => /=.
      case nA: prune => //=; case nB: prune => //= _.
      repeat eexists; first by apply: FailT.
      move=> /=; repeat eexists.
      by apply: FailT nB.
  Qed.

  Notation  "A ∨ B" := (A \/ B) (at level 20).
  Notation "A \/ B -sub( s )" := (Or A s B)
   (at level 50, s at level 0).

  (*SNIPT: runSST_or *)
  Lemma runSST_or: 
    forall p v v' s s' A A' s1 B, runT p v s A (Many s' A') true v' ->
      runT p v s ((Some A) \/ B -sub(s1)) (Many s' ((Some A') \/ KO -sub(s1))) false v'.
  (*ENDSNIPT: run_orSST *)
  Proof. move=> > /run_or_correct_left H; auto. Qed.

  (*SNIP: runSSF_or *)
  Lemma runSSF_or: forall p v0 v1 s0 s1 t0 t0' sm t1,
    runT p v0 s0 t0 (Many s1 t0') false v1 ->
      runT p v0 s0 (Or (Some t0) sm t1) (Many s1 ((Some t0') \/ t1 -sub(sm))) false v1.
  (*ENDSNIP: run_orSSF *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runSNF_or *)
  Lemma runSNF_or: forall p v0 v1 s0 t0 s1 sm t1,
    runT p v0 s0 t0 (One s1) false v1 ->
      runT p v0 s0 ((Some t0) \/ t1 -sub(sm))
        match (prune false t1) with
        | None =>  (One s1)
        | Some t => (Many s1 (None \/ t -sub(sm)))
        end
      false v1.
  (*ENDSNIP: run_orSNF *)
  Proof . move=>> /run_or_correct_left; auto. Qed.

  (*SNIP: runSNT_or *)
  Lemma runSNT_or: forall p v0 v1 s0 t0 s1 sm t1,
    runT p v0 s0 t0 (One s1) true v1 ->
      runT p v0 s0 ((Some t0) \/ t1 -sub(sm)) (One s1) false v1.
  (*ENDSNIP: run_orSNT *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIPT: runNT_or *)
  Lemma runNT_or: 
    forall p v v' s A s1 B, runT p v s A Zero true v' -> 
      runT p v s ((Some A) \/ B -sub(s1)) Zero false v'.
  (*ENDSNIPT: run_orNT *)
  Proof. move=>> /run_or_correct_left; auto. Qed.

  (*SNIPT: runNF_orx *)
  Lemma runNF_or': 
    forall p v0 v1 v2 s l s1 r r' b,
    runT p v0 s l Zero false v1 -> runT p v1 s1 r r' b v2 ->
      runT p v0 s ((Some l) \/ r -sub(s1)) 
      (map_many (fun x => None \/ x -sub(s1)) r') false v2.
  (*ENDSNIPT: runNF_orx *)
  Proof. by move=>> /run_or_correct_left; eauto. Qed.


  (*SNIPT: runNF_or *)
  Lemma runNF_or: 
    forall p v0 v1 v2 s A s1 s2 B b,
    runT p v0 s A Zero false v1 -> runT p v1 s1 B (One s2) b v2 ->
      runT p v0 s ((Some A) \/ B -sub(s1)) (One s2) false v2.
  (*ENDSNIPT: run_orNF *)
  Proof. move=> ???????? []> H1 H2/=; have:= run_or_correct_left H1 _ _ _ _ _ H2 => //=. Qed.
  
  (*SNIPT: runNF_or1 *)
  Lemma runNF_or1: 
    forall p v0 v1 v2 s A s1 s2 B B' b,
    runT p v0 s A Zero false v1 -> runT p v1 s1 B (Many s2 B') b v2 ->
      runT p v0 s ((Some A) \/ B -sub(s1)) (Many s2 (None \/ B' -sub(s1))) false v2.
  (*ENDSNIPT: run_orNF *)
  Proof. move=> ???????? []> H1 H2/=; have:= run_or_correct_left H1 _ _ _ _ _ H2 => //=. Qed.

  (*SNIPT: run_orSST *)
  Lemma run_orSST:
    forall p v v' s s' s1 A A' B B', 
    runT p v s ((Some A) \/ B -sub(s1)) (Many s' ((Some A') \/ B' -sub(s1))) false v' ->
      exists b, runT p v s A (Many s' A') b v' /\ B' = if b then KO else B.
  (*ENDSNIPT: run_orSST *)
  Proof.
    move=> > /run_or_complete[[Ax[b H1 [Bx [??] H]]]|[??]]//; subst.
    eexists; split; destruct b; eauto.
  Qed.

  (*SNIPT: run_orSNT1 *)
  Lemma run_orSNT1:
    forall p v v' s s' s1 A B B', 
    runT p v s ((Some A) \/ B -sub(s1)) (Many s' (None \/ B' -sub(s1))) false v' ->
      (exists b, runT p v s A (One s') b v' /\ if b then B' = KO else prune false B = Some B') ∨
      (exists v2 b, runT p v s A Zero false v2 /\ runT p v2 s1 B (Many s' B') b v').
  (*ENDSNIPT: run_orSNT1 *)
  Proof.
    move=> >/run_or_complete[[Ax[b H1 [T [??] H2]]]|[vf H1 [b H2]]]; subst.
      left; exists b => //; destruct b => //.
    by right; exists vf, b.
  Qed.

  (*SNIPT: run_orSNT *)
  Lemma run_orSNT:
    forall p v v' s s' s1 A B B', 
    runT p v s ((Some A) \/ B -sub(s1)) (Many s' (None \/ B' -sub(s1))) false v' ->
      (exists b, runT p v s A (One s') b v' /\ (b = true -> B' = KO)) ∨
      (exists v2 b, runT p v s A Zero false v2 /\ runT p v2 s1 B (Many s' B') b v').
  (*ENDSNIPT: run_orSNT *)
  Proof.
    move=> >/run_or_complete[[Ax[b H1 [T [??] H2]]]|[vf H1 [b H2]]]; subst.
      left; exists b => //; destruct b => //.
    by right; exists vf, b.
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
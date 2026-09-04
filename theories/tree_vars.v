From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop fresh.
  
Module Private.
Section vars_tree.
  Variable (u : Unif).
  Variable (p : program).

  Lemma vars_tree_cutl A: vars_tree (cutl A) `<=` vars_tree A.
  Proof. elim_tree A => /=; last case: ifP => //=; rewrite !fsetUSS//vars_tree_cutr. Qed.

  Lemma vars_tree_cutlF A: fresh (vars_tree (cutl A)) <= fresh (vars_tree A).
  Proof. by apply/fresh_subP/vars_tree_cutl. Qed.

  Lemma vars_tree_step_sub A fv s:
    fv <= (step u bc_run p fv s A).1.1.
  Proof.
    rewrite/bc_run.
    elim_tree A fv s => //=; rewrite ?push//=; last by case: ifP => /=.
    case: t => [|c]//=; rewrite /bc!push/=; case: ifP => //=.
    rewrite (leq_trans _ (max_sigmas_sub _ _))//(leq_trans _ (fresh_rules_sub _ _))//.
    by rewrite -!fsetUA freshUU freshP1 leq_max leqnSn.
  Qed.

  Lemma vars_tree_big_and r0:
    vars_tree (big_and r0) = vars_atoms r0.
  Proof. 
    case: r0 => //=+l; elim: l => //=[|x xs ->] a; first by rewrite vars_atoms1.
    by rewrite !vars_atoms_cons -fsetUA fsetUid.
  Qed.

  Lemma vars_tree_big_or r0 rs:
    vars_tree (big_or r0 rs) = vars_atoms r0 `|` varsU [seq vars_sigma x.1.1 `|` vars_atoms x.2 | x <- rs].
  Proof.
    elim: rs r0 => //=[|[s0 r0] rs IH] l/=; rewrite vars_tree_big_and ?fsetU0 => //.
    rewrite -fsetUA (fsetUC _ (vars_sigma s0.1)).
    by rewrite IH//= !fsetUA//.
  Qed.
  
  Lemma fresh_varsU fF rs: 0 < fF ->
    fresh (varsU [seq vars_sigma x.1 `|` vars_atoms x.2 | x <- rs]) <= max_sigmas fF rs.
  Proof.
    elim: rs fF => //=[|r0 rs IH] f S.
      by rewrite/fresh/=big_nil.
    by rewrite !freshPU -!andbA !freshUU/= !leq_max IH//= !leqnn !orbT.
  Qed.

  Lemma ltn_leq_trans: forall [n m p : nat], m < n -> n <= p -> m < p.
  Proof. move=> n m q hmn hnp; exact: leq_trans hmn hnp. Qed.

  Lemma select_in sP t r s k: 
    select u sP t r s = k ->
      forall (x: Sigma * seq Atom), x \in k -> x.2 \in map premises r.
  Proof.
    move=> <-; elim: r => //[r rs IH]r'/=.
    rewrite in_cons; case H => [[_ s']|]; last by move=> /IH->; rewrite orbT.
    by rewrite in_cons => /orP[/eqP->|/IH->]; rewrite (eqxx,orbT).
  Qed.
  
  Lemma vars_tm_ren_sub s t: vars_tm (ren s t) `<=` codomf s `|` vars_tm t.
  Proof.
    elim: t => //=[v|f Hf a Ha].
      by rewrite fsub1set inE in_fset1; case: fndP => vs/=; rewrite (in_codomf,eqxx)//orbT.
    by rewrite fsubUset (fsubset_trans Hf) ?(fsubset_trans Ha)//fsetUS//(fsubsetUl,fsubsetUr).
  Qed.
  
  Lemma fresh_tm_ext n m a:
    exists x, (fresh_tm n m a).2 = x + m.
  Proof.
    elim: a n m => [q|v|f Hf a Ha] n m/=.
      by exists fmap0; rewrite cat0f.
      case: fndP => /=; first by exists fmap0; rewrite cat0f.
      move=> vm; exists [fmap].[v <- IV n]%fmap.
      by rewrite catfC cat_set_eq remf_id//=fsetU0 fdisjoint1X.
    rewrite push.
    have [x->] := Ha (fresh_tm n m f).1 (fresh_tm n m f).2.
    have [y->] := Hf n m.
    by rewrite catfA; eexists.
  Qed.

  Lemma ren_catf x m f: vars_tm f `<=` domf m -> ren (x + m) f = ren m f.
  Proof.
    elim: f => //[v|f Hf a Ha].
      by rewrite !ren_V [vars_tm _]/= fsub1set fnd_cat => ->.
    by rewrite/= fsubUset => /andP[/Hf->/Ha->].
  Qed.

  Lemma fresh_ren_vars t n r:
    fresh (vars_tm t) <= n ->
    fresh (domf r) <= n ->
    fresh (codomf r) <= n ->
    fresh (vars_tm (ren (fresh_tm n r t).2 t)) <=
    (fresh_tm n r t).1.
  Proof.
    elim: t n r => //=[v|f Hf a Ha] n r + fd fc; last first.
      rewrite !push/= !freshPU => /andP[sf sa].
      apply/andP; split.
        apply/leq_trans/fresh_sub/leq_trans/Hf => //.
        have [x->] := fresh_tm_ext (fresh_tm n r f).1 (fresh_tm n r f).2 a.
        by rewrite ren_catf//fresh_tm_sub1.
      apply/leq_trans/Ha => //.
        by apply/leq_trans/fresh_sub.
        by apply fresh_subd.
      by apply fresh_subc.
    case: ifP => vr.
      rewrite in_fnd/= => H.
      by apply/leq_trans/fc/fresh_subP; rewrite fsub1set in_codomf.
    by move=> H; rewrite fnd_set eqxx/= freshP1.
  Qed.

  Lemma fresh_atoms_vars b n r:
    fresh (vars_atoms b) <= n ->
    fresh (domf r) <= n ->
    fresh (codomf r) <= n ->
    fresh (vars_atoms (fresh_atoms n r b).2) <=
    (fresh_atoms n r b).1.1.
  Proof.
    elim: b n r => [|x xs IH]//= n m; rewrite !push/= !vars_atoms_cons !freshPU.
    move=> /andP[xn xsn sd sc]; apply/andP; split; last first.
      by apply/leq_trans/fresh_atom_sub/IH.
    set X := fresh_atoms _ _ _.
    clear IH.
    case: x xn => //=[|t] xn; first by apply/leq_trans/fresh_atoms_sub.
    rewrite !push/=.
    apply: fresh_ren_vars.
      by apply/leq_trans/fresh_atoms_sub.
      apply/leq_trans/fresh_atoms_subd => //.
    apply/leq_trans/fresh_atoms_subc => //.
  Qed.

  Lemma fresh_rules_vars n n' r r': fresh (v_prog r) <= n ->
    fresh_rules n r = (n', r') -> 
      forall x, x \in r' -> fresh (vars_atoms (premises x)) <= n'.
  Proof.
    rewrite (surjective_pairing (fresh_rules _ _)) => /=+[<-<-{n' r'}]; clear.
    elim: r n => //=[r rs IH]n + x; rewrite !push/=.
    rewrite v_prog_cons !freshPU -andbA => /and3P[sh sb srs].
    rewrite inE => /orP[/eqP->|/IH H]; last by apply: leq_trans (H _) (fresh_rule_sub _ _).
    have := fresh_rules_sub rs n.
    move: (fresh_rules _ _).1 => m nm {IH srs}.
    have {}sh := leq_trans sh nm.
    have {}sb := leq_trans sb nm.
    case: r sh sb => h b; rewrite /varsU_rhead /varsU_rprem /=/fresh_rule !push/=.
    move=> sh sb.
    set X := fresh_tm _ _ _.
    move=> *; apply: fresh_atoms_vars => //.
      by apply/leq_trans/fresh_sub.
      by apply: fresh_subd; rewrite//domf0 freshP0; destruct m.
    by apply/fresh_subc; rewrite//codomf0 freshP0; destruct m.
  Qed.
  
  Lemma simpl_map_env xs:
      [seq vars_sigma x.1.1 `|` vars_atoms x.2
            | x <- [seq (s0, [fmap]%fmap : Env, p0) | '(s0, p0) <- xs]] =
      [seq vars_sigma x.1 `|` vars_atoms x.2
            | x <- xs].
  Proof. by elim: xs => //=-[s a xs]/=->. Qed.

  Lemma vars_tm_bc_sub n c fv fvx s s0 r0 rs:
    sum_mt n fmap0 c  <= fv-> fresh (vars_sigma s.1) <= fv -> 
    bc_run u p fv c s = (fvx, (s0, r0) :: rs) ->
    fresh (vars_tree (big_or r0 rs)) <= fvx  /\ fresh (vars_sigma s0.1) <= fvx.
  Proof.
    case: s => s e.
    move => H1 H2; rewrite/bc_run/bc/=; case: ifP => //= _; rewrite !push/=.
    set X := fresh _.
    case FR: fresh_rules => [fF RF]/=[?]; subst.
    case S: select => //=[[s' e'] xs]/=[???]; subst => /=.
    rewrite !leq_max !leqnn !orbT; split => //.
    rewrite vars_tree_big_or !freshPU !leqnn/=.
    have := fresh_rules_sub (rules p) X; rewrite FR/= => f0.
    have {}f0: 0 < fF by apply: ltn_leq_trans f0.
    rewrite simpl_map_env fresh_varsU// andbT.
    apply/orP; left.
    apply/leq_trans/max_sigmas_sub.
    have /(_ (s',r0)):= select_in S.
    rewrite inE eqxx => /(_ isT)/=/mapP[r rR ?]; subst.
    apply: fresh_rules_vars FR _ rR.
    by rewrite/X freshUU leq_max leqnn orbT.
  Qed.

  Lemma vars_sigma_next_subst s fvA A:
    fresh (vars_tree A) <= fvA -> fresh (vars_sigma s.1) <= fvA -> 
    fresh (vars_sigma (next_subst s A).1) <= fvA.
  Proof.
    elim_tree A s fvA => /=.
      by rewrite 2!freshPU -andbA => /and3P[vA vB vsm] vs; apply/HA.
      by rewrite freshPU => /andP[vA vB vsm]; apply/HB.
    rewrite 2!freshPU -andbA next_subst_and => /and3P[vA vB vsm] vs.
    by case: ifP => dA; auto.
  Qed.
  
  Check bc_sub.
  
  Lemma bc_run_sub fv c s:
    fv <= (bc_run u p fv c s).1.
  Proof. by rewrite/bc_run!push/=bc_sub. Qed.

  Lemma vars_tree_step_sub_flow A R fv fv' s r:
    fresh (vars_tree A) <= fv -> fresh (vars_sigma s.1) <= fv ->
    step u bc_run p fv s A = (fv', r, R) -> ((fresh (vars_tree R) <= fv') * (fresh (vars_sigma s.1) <= fv')).
  Proof.
    elim_tree A R fv fv' r s => /=; only 1,2: by move=> ?? [<-_<-].
      case: t => [|c]; first by move=> ?? [<- _ <-]//=.
      rewrite !push/= => H1 H2 [???]; subst => /=.
      split; last apply: leq_trans H2 (bc_run_sub _ _ _).
      case X: bc_run => [fvx [|[s0 r0] rs]]//=.
        rewrite freshP0.
        move: X; rewrite/bc_run/bc; case: ifP => //= _.
          by move=> [<-]; destruct fv.
        rewrite !push/= => -[<- _].
        apply/leq_trans/max_sigmas_sub.
        apply/leq_trans/fresh_rules_sub.
        by rewrite !freshUU freshP1 !leq_max//.
      rewrite freshUU geq_max.
      have {}f0: 0 < fv by destruct fv.
      apply/andP/vars_tm_bc_sub/X; rewrite//!freshPU freshP1/= codomf0/=H1 !freshP0 f0 !andbT.
      apply/f0.
    - rewrite 2!freshPU -!andbA !push => /and3P[fa fb fs] f/=.
      have Hs := vars_tree_step_sub A fv s.
      move=> [???]; subst.
      split => //; last by apply/leq_trans/vars_tree_step_sub.
      rewrite /= 2!freshPU -andbA.
      move: Hs; case eA: step => [[v' r'] t']//=Hs.
      have [-> H] := HA _ _ _ _ _ fa f eA => /=.
      rewrite !(leq_trans _ Hs)//.
      by case: ifP => //; destruct fv; rewrite//=freshP0.
    - rewrite freshPU; move => /andP[vB vsm] vs; rewrite !push => -[<-_<-]/=.
      have := vars_tree_step_sub B fv sm.
      case eA: step => [[v' r'] t']//=Hs; rewrite freshPU.
      have [-> H] := HB _ _ _ _ _ vB vsm eA; split => //=.
      by apply/leq_trans/Hs.
    rewrite 2!freshPU -andbA !push.
    move=> /and3P[vA vB0 vB] vs.
    case: ifP => sA/=[<- _ <-]/=.
      have := vars_tree_step_sub B fv (next_subst s A).
      case eB: step => [[fvB rB] B']/= Hs.
      rewrite 2!freshPU (HB _ _ _ _ _ _ _ eB)//=; last by apply: vars_sigma_next_subst.
      split => /=; last by apply/leq_trans/Hs.
      rewrite andbT; apply/andP; split; last by apply/leq_trans/Hs.
      case: ifP => _; apply/leq_trans/Hs => //.
      by apply/leq_trans/vA/vars_tree_cutlF.
    have := vars_tree_step_sub A fv s.
    case eA: step => [[fvA rA] A']/= Hs.
    rewrite 2!freshPU (HA _ _ _ _ _ _ _ eA)//=.
    by apply/andP; rewrite -andbA; apply/and3P; split; apply/leq_trans/Hs.
  Qed.

  Lemma vars_tree_prune_sub_flow A R fv b:
    fresh (vars_tree A) <= fv -> prune b A = Some R -> fresh (vars_tree R) <= fv.
  Proof.
    clear.
    elim_tree A R fv b => /=.
      by case: b; case: R.
      by case: t => [|c]? [<-]//.
    - rewrite 2!freshPU => /andP[/andP[Ha Hb] Hs].
      case nA: prune => [B'|]//=.
          by move=> [<-]/=; rewrite 2!freshPU Hb Hs (HA _ _ _ _ nA).
      by case nB: prune => //=-[<-]/=; rewrite freshPU (HB _ _ _ _ nB)//.
    - rewrite freshUU geq_max => /andP[Hb Hs].
      by case nB: prune => //=-[<-]/=; rewrite freshPU (HB _ _ _ _ nB)//.
    rewrite !freshPU -andbA.
    move=> /and3P [Ha Hb Hs].
    case: ifP => sA.
      case nB: prune => [B'|]//=.
        by move=> [<-]/=; rewrite 2!freshPU Ha Hs andbT; apply/HB/nB.
      case nA: prune => [A'|]//=[<-]/=.
      rewrite !freshPU (HA _ _ _ _ nA)//=.
      by rewrite vars_tree_big_and Hs.
    case: ifP => fA.
      case nA: prune => [A'|]//= [<-]/=.
      by rewrite !freshPU (HA _ _ _ _ nA)//= vars_tree_big_and Hs.
    move=> [<-]/=.
    by rewrite !freshPU Ha Hs Hb.
  Qed.

  Lemma vars_tree_step_cut A B fv fv' s:
    step u bc_run p fv s A = (fv', CutBrothers, B) -> vars_tree B `<=` vars_tree A.
  Proof.
    elim: A B fv fv' s => //=.
      by move=> [|?]????; [move=> [_ <-]|rewrite push].
      by move=> ??????>; rewrite !push; case: ifP => /=; case: step => [[?[]]]//.
      by move=> ??????>; rewrite !push; case: ifP => /=; case: step => [[?[]]]//.
    move=> A HA B0 B HB C fv fv' s.
    rewrite!push.
    case: ifP => sA [_ + <-]; case_step_tag X S => //= _.
      rewrite !fsubUset fsubsetU//=.
        rewrite fsubsetU//=; first by rewrite fsubsetUr.
        by rewrite fsubsetU//(HB _ _ _ _ X)orbT.
      by rewrite fsubsetU//vars_tree_cutl.
    by rewrite !fsetSU//; apply: HA X.
  Qed.
    

End vars_tree.
End Private.

Definition vars_tree_prune_sub_flow := Private.vars_tree_prune_sub_flow.
Definition vars_tree_step_sub_flow := Private.vars_tree_step_sub_flow.
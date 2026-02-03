From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Section vars_tree.
  Variable (u : Unif).
  Variable (p : program).

  Lemma fresh_tm_sub fv fv' m tm ign:
    fresh_tm fv m tm = (fv', ign) -> fv `<=` fv'.
  Proof.
    elim: tm fv fv' m ign => /=; only 1,2: by move=> _ > [<-].
      by move=> v fv fv' m ign; case: fndP => H [<-]//; rewrite fsubsetUr.
    move=> f Hf a Ha fv fv' m ign.
    rewrite !push => -[<- _].
    case t1: (fresh_tm fv) => [fv1 f'].
    case t2: fresh_tm => /=[fv2 a'].
    by apply/fsubset_trans/Ha/t2/Hf/t1.
  Qed.

  Lemma rename_sub fv fv' r r':
    rename fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    rewrite/rename !push => -[<- _].
    case X: fresh_tm => /=.
    apply: fresh_tm_sub X.
  Qed.

  Lemma fresh_callable_sub fv fv' r r':
    fresh_callable fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    elim: r r' fv fv'; only 1: by move=> > [<-].
    move=> f Hf a r' fv fv'; rewrite/=!push => -[<- _].
    case X: fresh_callable.
    case R: rename => /=.
    by apply/fsubset_trans/rename_sub/R/Hf/X.
  Qed.

  Lemma fresh_atom_sub fv fv' r r':
    fresh_atom fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    destruct r => //=; first by move=> [<-].
    rewrite push => -[<- _].
    case X: fresh_callable.
    by apply/fresh_callable_sub/X.
  Qed.

  Lemma fresh_atoms_sub fv fv' r r':
    fresh_atoms fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    elim: r r' fv fv' => [|x xs IH] r' fv fvx; first by move=> [<-].
    rewrite/=!push => -[<- _].
    case X: fresh_atoms => /=.
    case Y: fresh_atom => /=.
    by apply/fsubset_trans/fresh_atom_sub/Y/IH/X.
  Qed.

  Lemma fresh_rule_sub fv fv' r r':
    fresh_rule fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    rewrite/fresh_rule !push => -[<- _].
    case X: fresh_callable.
    case Y: fresh_atoms.
    by apply/fsubset_trans/fresh_atoms_sub/Y/fresh_callable_sub/X.
  Qed.

  Lemma fresh_rules_sub rs rs' fv fv': 
    fresh_rules fv rs = (fv', rs') -> fv `<=` fv'.
  Proof.
    elim: rs rs' fv fv' => [|x xs IH] rs' fv fvx; first by move=> [<-].
    rewrite /=!push => -[<- _].
    case X: fresh_rules => /=.
    case Y: fresh_rule.
    by apply/fsubset_trans/fresh_rule_sub/Y/IH/X.
  Qed.

  Lemma select_sub r0 rn fv fv' q m s:
    select u fv q m r0 s = (fv', rn) ->
      fv `<=` fv'.
  Proof.
    elim: r0 rn fv fv' q m s => [|x xs IH] rn fv fv' q m s; first by move=> [<-]//.
    move=> /=.
    case X: H => [s'|]; last by apply: IH.
    case Y: select => [fv2 rs][??]; subst.
    by rewrite fsubsetU// (IH _ _ _ _ _ _ Y) orbT.
  Qed.

  Lemma select_sub_rules r0 rn fv fv' q m s:
    select u fv q m r0 s = (fv', rn) ->
      varsU (seq.map (fun x => vars_sigma x.1 `|` vars_atoms x.2) rn) `<=` fv'.
  Proof.
    elim: r0 rn fv fv' q m s => [|x xs IH] rn fv fv' q m s/=; first by move=> [<-<-]//.
    case X: H => [s'|]; last by apply: IH.
    case Y: select => [fv2 rs][??]; subst => /=.
    rewrite -!fsetUA/= !fsetUS//.
    case: x X; rewrite/=/varsU_rhead/varsU_rprem/= => hd pm _.
    rewrite fsubsetU// fsetUS//=; first by rewrite orbT.
    by apply: IH Y.
  Qed.

  Lemma bc_sub c rs fv fv' s:
    bc u p fv c s = (fv', rs) -> fv `<=` fv'.
  Proof.
    rewrite/bc.
    case X: tm2RC => [[cd chd]|]; last by move=> [<-].
    case: fndP => cP; last by move=> [<-].
    case F: fresh_rules => [fvx rx] H.
    apply/fsubset_trans/select_sub/H/fresh_rules_sub/F.
  Qed.

  Lemma vars_tree_cutl A: vars_tree (cutl A) `<=` vars_tree A.
  Proof. elim_tree A => /=; last case: ifP => //=; rewrite !fsetUSS//vars_tree_cutr. Qed.

  Lemma vars_tree_step_sub A R fv fv' s r:
    step u p fv s A = (fv', r, R) -> fv `<=` fv'.
  Proof.
    elim_tree A R fv fv' r s => /=; only 1-2: by move=> [<-]//.
      case: t => [|c]/=; first by move=> [<-].
      rewrite push => -[<- _ _].
      case bc: bc => /=.
      by apply: bc_sub bc.
    - by rewrite /=!push; case: ifP => dA [<- _ _]; case X: step => [[]]//=; apply: HA X.
    - by rewrite /=!push; case: ifP => dA [<- _ _]; case X: step => [[]]//=; apply: HB X.
    rewrite/= !push.
    case: ifP => sA [<- _ _].
      by case_step_tag eB B'; apply: HB eB.
    by case_step_tag eA A'; apply: HA eA.
  Qed.

  Lemma vars_tree_big_and r0:
    vars_tree (big_and r0) = vars_atoms r0.
  Proof. by elim: r0 => //= -[|c]//=l ->; rewrite/vars_atoms/= -fsetUA fsetUid//. Qed.

  Lemma vars_tree_big_or r0 rs:
    vars_tree (big_or r0 rs) = vars_atoms r0 `|` varsU [seq vars_sigma x.1 `|` vars_atoms x.2 | x <- rs].
  Proof.
    elim: rs r0 => //=[|[s0 r0] rs IH] l/=; rewrite vars_tree_big_and ?fsetU0 => //.
    rewrite -fsetUA (fsetUC _ (vars_sigma s0)).
    by rewrite IH//= !fsetUA//.
  Qed.

  Lemma vars_tm_bc_sub c fv fvx s s0 r0 rs:
    vars_sigma s `<=` fv ->
    vars_tm (Callable2Tm c) `<=` fv ->
    bc u p fv c s = (fvx, (s0, r0) :: rs) ->
    vars_tree (big_or r0 rs) `<=` fvx  /\ vars_sigma s0 `<=` fvx.
  Proof.
    move => H1 H2.
    rewrite/bc/=.
    case X: tm2RC => [[cd hd]|]/=; last by move=> [<-]/=.
    case: fndP => /=hp; last by move=> [<-].
    rewrite !push.
    case FR: fresh_rules => [fF RF]/=.
    case S: select => [fv1 rs1]/=[<-]{fvx}?; subst.
    have Hx := select_sub S.
    have Hy := fresh_rules_sub FR.
    have Hz := fsubset_trans Hy Hx.
    have /= := select_sub_rules S.
    rewrite 2!fsubUset -andbA => /and3P[Ha Hb Hc].
    rewrite vars_tree_big_or fsubUset Hb => //.
  Qed.

  Lemma vars_sigma_get_subst s fvA A:
    vars_tree A `<=` fvA -> vars_sigma s `<=` fvA -> vars_sigma (get_subst s A) `<=` fvA.
  Proof.
    elim_tree A s fvA => /=.
      by rewrite 2!fsubUset -andbA => /and3P[vA vB vsm] vs; apply/HA.
      by rewrite fsubUset => /andP[vA vB vsm]; apply/HB.
    rewrite 2!fsubUset -andbA get_subst_and => /and3P[vA vB vsm] vs.
    by case: ifP => dA; auto.
  Qed.

  Lemma vars_tree_step_sub_flow A R fv fv' s r:
    vars_tree A `<=` fv -> vars_sigma s `<=` fv ->
    step u p fv s A = (fv', r, R) -> ((vars_tree R `<=` fv') * (vars_sigma s `<=` fv')).
  Proof.
    elim_tree A R fv fv' r s => /=; only 1,2: by move=> ?? [<-_<-].
      case: t => [|c]; first by move=> ?? [<- _ <-]//=.
      move=> H1 H2; case X: bc => [fvx c'][<-_<-].
      have H := bc_sub X.
      have ? := fsubset_trans H2 H.
      split => //.
      case: c' X => //=[[s0 r0] rs]//=; rewrite fset0U => H3.
      rewrite fsubUset; apply/andP.
      by apply: vars_tm_bc_sub H3.
    - rewrite 2!fsubUset !push -!andbA => /and3P[vA vB vsm] vs.
      move=> [???]; subst; case eA: step => [[v' r'] t']//=; rewrite 2!fsubUset.
      have [-> H] := HA _ _ _ _ _ vA vs eA; split => //=.
      apply/andP; split; apply/fsubset_trans/vars_tree_step_sub/eA => //.
      by case: ifP => // _; apply/fsubset_trans/vB/vars_tree_cutr.
    - rewrite fsubUset; move => /andP[vB vsm] vs; rewrite !push => -[<-_<-]/=.
      case eA: step => [[v' r'] t']//=; rewrite fsubUset.
      have [-> H] := HB _ _ _ _ _ vB vsm eA; split => //=.
      by apply/fsubset_trans/vars_tree_step_sub/eA.
    rewrite 2!fsubUset -andbA !push.
    move=> /and3P[vA vB0 vB] vs.
    case: ifP => sA/=[<- _ <-]/=.
      case eB: step => [[fvB rB] B']/=.
      rewrite 2!fsubUset (HB _ _ _ _ _ _ _ eB)//=; last by apply: vars_sigma_get_subst.
      split => /=; last first.
        by apply/fsubset_trans/vars_tree_step_sub/eB.
      rewrite andbT; apply/andP; split; last first.
        by apply/fsubset_trans/vars_tree_step_sub/eB.
      case: ifP => _; apply/fsubset_trans/vars_tree_step_sub/eB => //.
      by apply/fsubset_trans/vA/vars_tree_cutl.
    case eA: step => [[fvA rA] A']/=.
    rewrite 2!fsubUset (HA _ _ _ _ _ _ _ eA)//=.
    by apply/andP; rewrite -andbA; apply/and3P; split; apply/fsubset_trans/vars_tree_step_sub/eA.
  Qed.

  Lemma vars_tree_next_alt_sub_flow A R fv b:
    vars_tree A `<=` fv ->
    next_alt b A = Some R -> vars_tree R `<=` fv.
  Proof.
    clear.
    elim_tree A R fv b => /=.
      by case: b; case: R.
      by case: t => [|c]? [<-]//.
    - rewrite 2!fsubUset => /andP[/andP[Ha Hb] Hs].
      case nA: next_alt => [B'|]//=.
          by move=> [<-]/=; rewrite 2!fsubUset Hb Hs (HA _ _ _ _ nA).
      by case nB: next_alt => //=-[<-]/=; rewrite fsubUset (HB _ _ _ _ nB)//.
    - rewrite fsubUset => /andP[Hb Hs].
      by case nB: next_alt => //=-[<-]/=; rewrite fsubUset (HB _ _ _ _ nB)//.
    rewrite !fsubUset -andbA.
    move=> /and3P [Ha Hb Hs].
    case: ifP => sA.
      case nB: next_alt => [B'|]//=.
        by move=> [<-]/=; rewrite 2!fsubUset Ha Hs andbT; apply/HB/nB.
      case nA: next_alt => [A'|]//=[<-]/=.
      rewrite !fsubUset (HA _ _ _ _ nA)//=.
      by rewrite vars_tree_big_and Hs.
    case: ifP => fA.
      case nA: next_alt => [A'|]//= [<-]/=.
      by rewrite !fsubUset (HA _ _ _ _ nA)//= vars_tree_big_and Hs.
    move=> [<-]/=.
    by rewrite !fsubUset Ha Hs Hb.
  Qed.

  Lemma vars_tree_step_cut A B fv fv' s:
    step u p fv s A = (fv', CutBrothers, B) -> vars_tree B `<=` vars_tree A.
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


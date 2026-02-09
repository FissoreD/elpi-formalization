From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Section vars_tree.
  Variable (u : Unif).
  Variable (p : program).

  Lemma rename_sub fv r:
    fv `<=` (rename fv r).1.
  Proof.
    rewrite/rename !push/=.
    by apply/fsubset_trans/fresh_tm_sub; rewrite fsubsetUr.
  Qed.

  Lemma fresh_atom_sub fv r:
    fv `<=` (fresh_atom fv r).1.
  Proof. by case: r => //= c; rewrite push/=rename_sub. Qed.

  Lemma fresh_atoms_sub fv r:
    fv `<=` (fresh_atoms fv r).1.
  Proof.
    elim: r fv => [|x xs IH] fv//=.
    rewrite/=!push/=; apply/fsubset_trans/fresh_atom_sub/IH.
  Qed.

  Lemma fresh_rule_sub fv r:
    fv `<=` (fresh_rule fv r).1.
  Proof.
    rewrite/fresh_rule !push/=.
    by apply/fsubset_trans/fresh_atoms_sub/rename_sub.
  Qed.

  Lemma fresh_rules_sub rs fv: 
    fv `<=` (fresh_rules fv rs).1.
  Proof.
    elim: rs fv => [|x xs IH] fv//=.
    rewrite /=!push/=.
    apply/fsubset_trans/fresh_rule_sub/IH.
  Qed.

  Lemma select_sub_rules r0 rn fv' q m s:
    select u q m r0 s = (fv', rn) ->
      varsU (seq.map (fun x => vars_sigma x.1 `|` vars_atoms x.2) rn) `<=` fv'.
  Proof.
    elim: r0 rn fv' q m s => [|x xs IH] rn fv' q m s/=; first by move=> [<-<-]//.
    case X: H => [s'|]; last by apply: IH.
    case Y: select => [fv2 rs][??]; subst => /=.
    rewrite -!fsetUA/= !fsetUS//.
    case: x X; rewrite/=/varsU_rhead/varsU_rprem/= => hd pm _.
    rewrite fsubsetU// fsetUS//=; first by rewrite orbT.
    by apply: IH Y.
  Qed.

  Lemma bc_sub c fv s:
    fv `<=` (bc u p fv c s).1.
  Proof.
    rewrite/bc.
    case X: callable => [c'|]//=.
    case: fndP => cP//.
    rewrite !push/= fsubsetU//.
    rewrite fresh_rules_sub//.
  Qed.

  Lemma vars_tree_cutl A: vars_tree (cutl A) `<=` vars_tree A.
  Proof. elim_tree A => /=; last case: ifP => //=; rewrite !fsetUSS//vars_tree_cutr. Qed.

  Lemma vars_tree_step_sub A fv s:
    fv `<=` (step u p fv s A).1.1.
  Proof.
    elim_tree A fv s => //=; rewrite ?push//=.
      by case: t => [|c]//=; by rewrite push/=bc_sub.
    case: ifP => sA//=.
  Qed.

  Lemma vars_atoms_cons a xs: vars_atoms [:: a & xs] = vars_atom a `|` vars_atoms xs.
  Proof. by []. Qed.

  Lemma vars_atoms1 a: vars_atoms [:: a] = vars_atom a.
  Proof. by rewrite/vars_atoms/=fsetU0. Qed.

  Lemma vars_tree_big_and r0:
    vars_tree (big_and r0) = vars_atoms r0.
  Proof. 
    case: r0 => //=+l; elim: l => //=[|x xs ->] a; first by rewrite vars_atoms1.
    by rewrite !vars_atoms_cons -fsetUA fsetUid.
  Qed.

  Lemma vars_tree_big_or r0 rs:
    vars_tree (big_or r0 rs) = vars_atoms r0 `|` varsU [seq vars_sigma x.1 `|` vars_atoms x.2 | x <- rs].
  Proof.
    elim: rs r0 => //=[|[s0 r0] rs IH] l/=; rewrite vars_tree_big_and ?fsetU0 => //.
    rewrite -fsetUA (fsetUC _ (vars_sigma s0)).
    by rewrite IH//= !fsetUA//.
  Qed.

  Lemma vars_tm_bc_sub c fv fvx s s0 r0 rs:
    vars_sigma s `<=` fv ->
    vars_tm c `<=` fv ->
    bc u p fv c s = (fvx, (s0, r0) :: rs) ->
    vars_tree (big_or r0 rs) `<=` fvx  /\ vars_sigma s0 `<=` fvx.
  Proof.
    move => H1 H2.
    rewrite/bc/=.
    case X: callable => [c'|]//=.
    case: fndP => /=hp; last by move=> [<-].
    rewrite !push.
    case FR: fresh_rules => [fF RF]/=.
    case S: select => [fv1 rs1]/=[<-]{fvx}?; subst.
    have:= select_sub_rules S => /=.
    rewrite 2!fsubUset -andbA => /and3P[Ha Hb Hc].
    rewrite vars_tree_big_or fsubUset !fsubsetU//(Ha,Hb,Hc) orbT//.
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
      rewrite !push/= => H1 H2 [???]; subst => /=.
      split; last by apply: fsubset_trans H2 (bc_sub _ _ _).
      case X: bc => [fvx [|[s0 r0] rs]]//=.
      rewrite fsubUset; apply/andP.
      by apply: vars_tm_bc_sub X.
    - rewrite 2!fsubUset !push -!andbA => /and3P[vA vB vsm] vs [???]; subst.
      have Hs := vars_tree_step_sub A fv s.
      split; last by apply/fsubset_trans/Hs.
      rewrite /= 2!fsubUset -andbA.
      rewrite (fsubset_trans vsm Hs) andbT.
      move: Hs; case eA: step => [[v' r'] t']//=Hs.
      have [-> H] := HA _ _ _ _ _ vA vs eA => /=.
      by case: ifP => //= _; apply/fsubset_trans/Hs.
    - rewrite fsubUset; move => /andP[vB vsm] vs; rewrite !push => -[<-_<-]/=.
      have := vars_tree_step_sub B fv sm.
      case eA: step => [[v' r'] t']//=Hs; rewrite fsubUset.
      have [-> H] := HB _ _ _ _ _ vB vsm eA; split => //=.
      by apply/fsubset_trans/Hs.
    rewrite 2!fsubUset -andbA !push.
    move=> /and3P[vA vB0 vB] vs.
    case: ifP => sA/=[<- _ <-]/=.
      have := vars_tree_step_sub B fv (get_subst s A).
      case eB: step => [[fvB rB] B']/= Hs.
      rewrite 2!fsubUset (HB _ _ _ _ _ _ _ eB)//=; last by apply: vars_sigma_get_subst.
      split => /=; last by apply/fsubset_trans/Hs.
      rewrite andbT; apply/andP; split; last by apply/fsubset_trans/Hs.
      case: ifP => _; apply/fsubset_trans/Hs => //. 
      by apply/fsubset_trans/vA/vars_tree_cutl.
    have := vars_tree_step_sub A fv s.
    case eA: step => [[fvA rA] A']/= Hs.
    rewrite 2!fsubUset (HA _ _ _ _ _ _ _ eA)//=.
    by apply/andP; rewrite -andbA; apply/and3P; split; apply/fsubset_trans/Hs.
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


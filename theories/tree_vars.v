From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Section vars_tree.
  Variable (u : Unif).
  Variable (p : program).

  Lemma fresh_tm_sub fv fv' r r':
    fresh_tm fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    elim: r r' fv fv' => /=; only 1,2: by move=> > [<-].
      by move=> v r' fv fv' [<- _]; rewrite fsubsetU// fsubsetU1 orbT.
    move=> f Hf a Ha r' fv fv'; rewrite !push => -[<- _].
    case t1: (fresh_tm fv) => [fv1 f'].
    case t2: fresh_tm => [fv2 a'].
    by apply/fsubset_trans/Ha/t2/Hf/t1.
  Qed.

  Lemma fresh_callable_sub fv fv' r r':
    fresh_callable fv r = (fv', r') -> fv `<=` fv'.
  Proof.
    elim: r r' fv fv'; only 1: by move=> > [<-].
    move=> f Hf a r' fv fv'; rewrite/=!push => -[<- _].
    case X: fresh_callable.
    case Y: fresh_tm.
    apply/fsubset_trans/fresh_tm_sub/Y/Hf/X.
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
      varsU (seq.map (fun x => vars_sigma x.1 `|` varsU_rule x.2) rn) `<=` fv'.
  Proof.
    elim: r0 rn fv fv' q m s => [|x xs IH] rn fv fv' q m s/=; first by move=> [<-<-]//.
    case X: H => [s'|]; last by apply: IH.
    case Y: select => [fv2 rs][??]; subst => /=.
    rewrite fsetUS//.
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

  Lemma backchain_sub c c' fv fv' s:
    backchain u p fv s c = (fv', c') ->
    fv `<=` fv'.
  Proof.
    rewrite/backchain push => -[<- _].
    case X: bc => [fvx rs]/=.
    apply/bc_sub/X.
  Qed.

  Lemma vars_tree_cutl A: vars_tree (cutl A) `<=` vars_tree A.
  Proof. elim_tree A => /=; last case: ifP => //=; rewrite !fsetUSS//vars_tree_cutr. Qed.

  Lemma vars_tree_step_sub A R fv fv' s r:
    step u p fv s A = (fv', r, R) -> fv `<=` fv'.
  Proof.
    elim_tree A R fv fv' r s => /=; only 1-2: by move=> [<-]//.
      case: t => [|c]/=; first by move=> [<-].
      rewrite push => -[<- _ _].
      case X: backchain.
      apply/backchain_sub/X.
    - by rewrite /=!push; case: ifP => dA [<- _ _]; case X: step => [[]]//=; apply: HA X.
    - by rewrite /=!push; case: ifP => dA [<- _ _]; case X: step => [[]]//=; apply: HB X.
    rewrite/= !push.
    case X: (step _ _ _ _ A) => [[fvx r'] A']/=; case: ifP.
      destruct r' => //= _; have [[??] sA] := step_success X; subst.
      move => [<- _ _].
      by case Y: step => [[]]; apply/HB/Y.
    by move=> _ [<- _ _]; apply/HA/X.
  Qed.

  Lemma vars_tree_big_and r0:
    vars_tree (big_and r0) = vars_atoms r0.
  Proof. by elim: r0 => //= -[|c]//=l ->; rewrite/vars_atoms/= -fsetUA fsetUid//. Qed.

  Lemma vars_tree_big_or s0 r0 rs:
    vars_sigma s0 `|` vars_tree (big_or (premises r0) rs)
    `<=` vars_sigma s0 `|` varsU_rule r0
     `|` varsU [seq vars_sigma x.1 `|` varsU_rule x.2 | x <- rs].
  Proof.
    elim: rs s0 r0 => //=[|[s0 r0] rs IH] s l/=; rewrite vars_tree_big_and ?fsetU0.
      by rewrite /varsU_rule/varsU_rprem (fsetUC (varsU_rhead _)) fsetUA fsubsetUl.
    rewrite -fsetUA (fsetUC _ (vars_sigma s0)).
    rewrite fsetUA fsetUSS// fsetUSS//.
    by apply/fsubsetUr.
  Qed.

  Lemma vars_tm_bc_sub c c' fv fv' s:
    vars_sigma s `<=` fv ->
    vars_tm (Callable2Tm c) `<=` fv ->
    backchain u p fv s c = (fv', c') ->
    vars_tree c' `<=` fv' /\  vars_sigma s `<=` fv'.
  Proof.
    rewrite/backchain !push => H1 H2 [<-].
    rewrite/bc/=.
    case X: tm2RC => [[cd hd]|]/=; last by move=> <-/=.
    case: fndP => /=hp; last by move=> <-.
    rewrite !push.
    case FR: fresh_rules => [fF RF]/=.
    case S: select => [fv1 rs]/=<-{c'}//=.
    have Hx := select_sub S.
    have Hy := fresh_rules_sub FR.
    have Hz := fsubset_trans Hy Hx.
    split; last first.
      by apply/fsubset_trans/Hz.
    case: rs S => [|[r0 s0] rs]//= S.
    rewrite fset0U.
    rewrite fsetUC.
    apply/fsubset_trans.
      apply/vars_tree_big_or.
    by have:= select_sub_rules S.
  Qed.

  Lemma vars_sigma_get_subst s fvA A:
    vars_tree A `<=` fvA -> vars_sigma s `<=` fvA -> vars_sigma (get_substS s A) `<=` fvA.
  Proof.
    elim_tree A s fvA => /=.
      by rewrite 2!fsubUset -andbA => /and3P[vA vB vsm] vs; apply/HA.
      by rewrite fsubUset => /andP[vA vB vsm]; apply/HB.
    rewrite 2!fsubUset -andbA => /and3P[vA vB vsm] vs;
    by case: ifP => dA; auto.
  Qed.


  Lemma vars_tree_step_sub_flow A R fv fv' s r:
    vars_tree A `<=` fv -> vars_sigma s `<=` fv ->
    step u p fv s A = (fv', r, R) -> ((vars_tree R `<=` fv') * (vars_sigma s `<=` fv')).
  Proof.
    elim_tree A R fv fv' r s => /=; only 1,2: by move=> ?? [<-_<-].
      case: t => [|c]; first by move=> ?? [<- _ <-]//=.
      move=> H1 H2; case X: backchain => [fvx c'][<-_<-].
      by apply/vars_tm_bc_sub/X.
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
    case eA: step => [[fvA rA] A']/=; case: ifP => H.
      destruct rA => //=; have [[??] sA]:= step_success eA; subst.
      move=> [<- ??]; subst.
      case eB: step => [[fvB rB] B']/=.
      rewrite 2!fsubUset (HB _ _ _ _ _ _ _ eB)//=; last by apply: vars_sigma_get_subst.
      split => /=; last first.
        by apply/fsubset_trans/vars_tree_step_sub/eB.
      rewrite andbT; apply/andP; split; last first.
        by apply/fsubset_trans/vars_tree_step_sub/eB.
      case: ifP => _; apply/fsubset_trans/vars_tree_step_sub/eB => //.
      by apply/fsubset_trans/vA/vars_tree_cutl.
    move=> [<-??]; subst => /=; rewrite 2!fsubUset (HA _ _ _ _ _ _ _ eA)//=.
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
    rewrite!push; case eA: step => [[?[]] A']//=.
      by move=> [_ <-]/=; rewrite !fsetSU//; apply: HA eA.
    have [[??] _] := step_success eA; subst.
    case eB: step => [[?[]]]//=[_ <-]/=.
    rewrite !fsubUset fsubsetU//=.
      rewrite fsubsetU//=; first by rewrite fsubsetUr.
      by rewrite fsubsetU//(HB _ _ _ _ eB)orbT.
    by rewrite fsubsetU//=vars_tree_cutl.
  Qed.
    

End vars_tree.


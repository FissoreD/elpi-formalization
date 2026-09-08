From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif fresh sig_lattice sig_compat valid_tree min_max_disj.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Fixpoint vars_tree_atom t : fvS :=
  match t with
  | Unexplored cut | KO | OK => fset0
  | Unexplored (call t) => vars_tm t
  | And A B0 B => vars_tree_atom A `|` vars_tree_atom B `|` vars_atoms B0
  | Or None s B => vars_tree_atom B
  | Or (Some A) s B => vars_tree_atom A `|` vars_tree_atom B
  end.

Lemma vars_atoms_big_and r0: vars_tree_atom (big_and r0) = vars_atoms r0.
Proof.
  case: r0 => [|x xs]//=; elim: xs x => //=[|x xs IH] t; first by rewrite /vars_atoms/= fsetU0; case: t => //.
  by rewrite !vars_atoms_cons !IH !vars_atoms_cons/= -fsetUA fsetUid.
Qed.

Fixpoint disj_tree t :=
  match t with
  | KO | OK | Unexplored _ => true
  | And A _ B => disj_tree A && disj_tree B
  | Or None _ t => disj_tree t
  | Or (Some A) _ B => [&& (vars_tree_atom A # vars_tree_atom B), disj_tree A & disj_tree B]
  end.

Lemma disj_tree_big_and B: disj_tree (big_and B).
Proof. by case: B => //=+l; elim: l => //=. Qed.

Lemma vars_tree_atom_big_or x0 xs:
  vars_tree_atom (big_or x0 xs) = vars_atoms x0 `|` varsU (map (fun x => vars_atoms x.2) xs).
Proof. by elim: xs x0 => //=[|[s0 x0 xs] IH]/=r; rewrite ?fsetU0 vars_atoms_big_and//IH. Qed.


Lemma disj_tree_big_or x0 xs:
  disj_tree (big_or x0 xs) = fdisjoint (vars_atoms x0) (varsU (map (fun x => vars_atoms x.2) xs)) &&
    disj_tree match xs with
    | [::] => KO 
    | (s,x) :: xs => Or None s (big_or x xs)
    end.
Proof.
  by case: xs => //=[|[s0 r0] xs]/=; rewrite disj_tree_big_and//=?fdisjointX0// vars_atoms_big_and vars_tree_atom_big_or.
Qed.

Lemma prune_sub b A R: prune b A = Some R -> vars_tree_atom R `<=` vars_tree_atom A.
Proof.
  elim_tree A b R => /=.
  - by case: b => //; move=> [<-].
  - by move=> [<-]//.
  - case PA: prune => [A'|].
      by move=> [<-]/=; rewrite fsetSU//; apply: HA PA.
    by case PB: prune => [B'|]//=[<-]/=; rewrite //(fsubset_trans (HB _ _ PB))//fsubsetUr.
  - by case PB: prune => [B'|]//=[<-]/=; rewrite //(HB b).
  - case X: ((success A && (prune b B == None)) || (failed A)).
      move=> H.
      have: exists b, omap (fun A : tree => And A B0 (big_and B0)) (prune b A) = Some R.
        by move: X H => /orP[/andP[->/eqP->]|/[dup]/failed_success->-><-]; eauto.
      move=> {H}[x]; case PA: prune => //=-[<-]/=.
      by rewrite vars_atoms_big_and -fsetUA fsetUid fsetSU//(fsubset_trans (HA _ _ PA))//fsubsetUl.
    move: X => /norP[+/negbTE->].
    case: success => //=; last by move=> _ [<-].
    by case PB: prune => //[B'] _[<-]{R}/=; rewrite fsetSU//fsetUS//(HB b).
Qed.

Lemma disj_tree_prune b A R:
  disj_tree A -> prune b A = Some R -> disj_tree R.
Proof.
  elim_tree A b R; only 1,2 : by case: b => _ //-[<-].
  - move=> /=/and3P[dAB dA dB].
    case pA: prune => [A'|].
      by move=> [<-]/=; rewrite dB (HA b)// (fdisjointWl _ dAB)// (prune_sub pA).
    by case pB: prune => [B'|]//=[<-]/=; rewrite (HB false).
  - by move=> /=; case pB: prune => //=[B']+[<-]/=; eauto.
  - move=> /=/andP[dA dB].
    case X: ((success A && (prune b B == None)) || (failed A)).
      move=> H.
      have: exists b, omap (fun A : tree => And A B0 (big_and B0)) (prune b A) = Some R.
        by move: X H => /orP[/andP[->/eqP->]|/[dup]/failed_success->-><-]; eauto.
      by move=> {H}[x]; case PA: prune => //=-[<-]/=; rewrite (HA x)//disj_tree_big_and.
    move: X => /norP[].
    case: success => //=.
      by case P : prune => //= _ _ [<-]//=; rewrite dA (HB b).
    by move=> _ /negbTE->[<-]/=; rewrite dA.
Qed.

Lemma disj_tree_cutl A:
  disj_tree A -> disj_tree (cutl A).
Proof.
  elim_tree A => /=[/and3P[dAB dA dB]|/andP[dA dB]].
    by rewrite HA//fdisjointX0.
  by case: ifP; rewrite//=HA//HB.
Qed.

Lemma vars_atoms_select_sub sig t rs s:
  let sel := select u sig t rs s in
  varsU [seq vars_atoms x.2 | x <- sel] `<=` varsU [seq vars_atoms x.(premises) | x <- rs].
Proof.
  move=> /=; elim: rs => [|[h b] rs IH]/=; first by rewrite fsubset_refl.
  case H: H => [[sig' s']|]/=; first by rewrite fsetUS//.
  by rewrite fsubsetU// IH orbT.
Qed.

Definition leq_codomf m (r: {fmap V -> V}) := 
  [forall x : codomf r, let: IV x := val x in m <= x].

Lemma leq_codomf_fresh_tm:
  forall q m r h, m <= q ->
  let x := fresh_tm q r h in
  leq_codomf m r ->
  leq_codomf m x.2.
Proof.
  move=> /=q m r t; elim: t m q r => //[v|f Hf a Ha] m q r mq.
    rewrite/=; case: ifP => //=vr.
    rewrite/leq_codomf/= codomf_setN?vr//.
    move=> /forallP H; apply/forallP => -[[x]]/=.
    rewrite in_fsetU in_fset1/=; case: eqP; first by move=> [->].
    by move=> /= _ yr; apply: H [`yr].
  move=> mr/=; rewrite !push.
  by apply/Ha/Hf/mr/mq/leq_trans/fresh_sub.
Qed.

Lemma leq_codomf_vars_atoms:
  forall q m r h, m <= q ->
  let x := fresh_atoms q r h in
  leq_codomf m r ->
  leq_codomf m x.1.2.
Proof.
  move=> /=q m r t; elim: t m q r => [|x xs IH] m q r mq l//=.
  rewrite !push/=; case: x => [|t]; first by apply: IH.
  rewrite/=!push/=.
  apply/leq_codomf_fresh_tm/IH/l/mq.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma leq_codomf_ren v t m B:
  vars t `<=` domf B ->
  leq_codomf m B ->
  IV v  \in vars (ren B t) ->
  m <= v.
Proof.
  elim: t v m B => [p|v|f Hf a Ha]//=v' m B; rewrite (fsub1set,fsubUset) (in_fsetU, in_fset1).
    move=> vB; rewrite in_fnd//==> H /eqP H1.
    have v'B : IV v' \in codomf B by apply/codomfP; exists v; rewrite in_fnd H1.
    by have:= forallP H [`v'B].
  by move=> /andP[fB aB] l/orP[/Hf|/Ha]->//.
Qed.

Lemma leq_codomf_vars_atoms_in m A B v b:
  m <= A -> leq_codomf m B ->
  IV v  \in vars_atoms (fresh_atoms A B b).2 ->
  m <= v.
Proof.
  elim: b A B v => //=x xs IH A B v.
  rewrite !push/= vars_atoms_cons in_fsetU.
  case: x => //=[|t]; first by apply: IH.
  rewrite !push/=.
  set Fxs := fresh_atoms _ _ _.
  set Ft := fresh_tm _ _ _.
  case VT: (_ \in _) => //= VX; last by apply: IH VX.
  move=> lmb _.
  apply: leq_codomf_ren VT.
    apply: fresh_tm_sub1.
  apply/leq_codomf_fresh_tm/leq_codomf_vars_atoms/lmb/VX.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma disj_tree_bc p n s t:
  disj_tree match (bc u p n t s).2 with
  | [::] => KO
  | (s0, r) :: xs => Or None s0 (big_or r xs)
  end.
Proof.
  rewrite/bc; case: ifP => ///negbFE IS.
  rewrite !push/=.
  set N := (fresh _); have := leqnn N; rewrite {1}/N; clearbody N.
  rewrite !freshPU -!andbA => /and5P[Fn Fd Fc Ft].
  case: p => r sig/=.
  elim: r => //=-[h b] rs IH; rewrite v_prog_cons/=!freshPU -!andbA /varsU_rhead/varsU_rprem.
  rewrite/= !push/= head_fresh_rule/= => /and3P[Fh Fb Fr].
  case F: fresh_rules IH => [N' rs'] IH.
  case H: H => [[ty n']|]//=; last by apply: IH.
  move: (IH Fr); rewrite-/F; set sel := select _ _ _ _ _ => {}IH.
  rewrite disj_tree_big_or IH andbT /fresh_rule !push/=.
  apply: fdisjointWr (vars_atoms_select_sub _ _ _ _) _.
  have /={}H := fresh_rules_vars Fr F.
  set Frh := fresh_tm _ _ _.
  have NN' : N <= N'.
    move: F; rewrite (surjective_pairing (fresh_rules _ _)) => -[??]; subst.
    by apply: fresh_rules_sub.
  rewrite fdisjoint_sym.
  apply: @min_max_S_disj _ _ 0 (N') (N') ((fresh_atoms Frh.1 Frh.2 b)).1.1 _ _ _.
    by [].
    apply/forallP => -[[v]vP]/=.
    move/varUP : vP => [x[/mapP[k krs'] ? vx]]; subst.
    have:= H _ krs'. apply/leq_trans.
    move: vx; apply: contraTT => Hx.
    have ->// := @fresh_sub_notin (vars_atoms (premises k)) v; rewrite leqNgt.
    by [].
  apply/forallP => -[[v]vP]/=; apply/andP; split.
    apply: leq_trans (leq_codomf_vars_atoms_in _ _ vP); last first.
      apply leq_codomf_fresh_tm.
        by apply: leqnn.
        by apply/forallP => -[]; rewrite codomf0.
      apply/leq_trans/fresh_sub => //.
    by [].
  apply: leq_trans (fresh_atoms_vars _ _ _); last first.
  - apply: fresh_subc; rewrite codomf0 freshP0.
    by destruct N => //=; destruct N'.
  - apply: fresh_subd; apply/leq_trans/NN' => //=.
    by rewrite freshP0; destruct N.
  - by apply: leq_trans Fb (leq_trans NN' (fresh_sub _ _ _)).
  have:= @fresh_sub_notin (vars_atoms (fresh_atoms Frh.1 Frh.2 b).2) v.
  by rewrite vP/= leqNgt; case: leq => ///(_ isT).
Qed.

Lemma disj_tree_step p n s t:
  disj_tree t -> disj_tree (step u p n s t).2.
Proof.
  elim_tree t s => /=.
  - move=> _; case: t => //t; rewrite !push/=.
    apply: disj_tree_bc.
  - move=> /and3P[dAB vA vB]; rewrite !push/=.
    rewrite HA//; case: ifP => //=; first by rewrite fdisjointX0.
    rewrite vB andbT.
    (* TODO: prove that vars_tree_atom on step produces A' `|` E where A' <= A and E is > n *)
    (* I need the Hyp that n contains all vars in t *)
    admit.
  - by move=> vB; rewrite !push/=HB.
  - move=> /andP[dA dB].
    case: ifP => sA; rewrite !push/=?HA//HB//andbT.
    by case: ifP; rewrite//=disj_tree_cutl.
Admitted.

Lemma disj_tree_run p n t t' s s':
  disj_tree t ->
  (exists b n', runT u p n s t (Many s' t') b n') ->
  disj_tree t'.
Proof.
  move=> + [b[n' R]].
  remember (Many _ _) as r eqn:H.
  elim_run R s' t' H => D.
    by move: H => [_<-]; apply: disj_tree_prune NS.
    apply: IH => //.
    move: eA; rewrite (surjective_pairing (step _ _ _ _ _)) => -[_ <-].
    by apply: disj_tree_step.
  by apply/IH/disj_tree_prune/nA.
Qed.

Print Assumptions disj_tree_run.
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

Lemma vars_tree_atom_big_or x0 xs:
  vars_tree_atom (big_or x0 xs) = vars_atoms x0 `|` varsU (map (fun x => vars_atoms x.2) xs).
Proof. by elim: xs x0 => //=[|[s0 x0 xs] IH]/=r; rewrite ?fsetU0 vars_atoms_big_and//IH. Qed.

Lemma vars_tree_atom_cutl t: vars_tree_atom (cutl t) `<=` vars_tree_atom t.
Proof.
  elim_tree t => /=.
    by rewrite fsetU0 (fsubset_trans HA)//fsubsetUl.
  case: ifP; rewrite//=fsetSU//fsubUset (fsubset_trans HA (fsubsetUl _ _)).
  by rewrite (fsubset_trans HB (fsubsetUr _ _)).
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
    apply: leq_trans (all_min_vars_atoms_in _ _ vP); last first.
      apply all_min_fresh_tm.
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

Lemma vars_tree_atom_vars_tree_sub t:
  vars_tree_atom t `<=` vars_tree t.
Proof.
  elim_tree t; rewrite/=?fsubUset.
    rewrite (fsubset_trans HA)//=; last by rewrite -fsetUA fsubsetUl.
    by rewrite fsubsetU//(fsubset_trans HB)//fsubsetUr.
    by rewrite (fsubset_trans HB)//fsubsetUl.
  rewrite fsubsetUr andbT (fsubset_trans HA);last by rewrite -fsetUA fsubsetUl.
  by rewrite fsubsetU//(fsubset_trans HB)//fsubsetUr.
Qed.

Lemma all_min_fset0 n: all_min n fset0.
Proof. by apply/forallP => -[]. Qed.

Lemma vars_atoms_bc prog n t s:
  fresh (vars_sigma s) <= n ->
  fresh (vars t) <= n ->
    exists v' e : fvS,
    [/\ all_min n e,
      vars_tree_atom
      match (bc u prog n t s).2 with
      | [::] => KO
      | (s0, r) :: xs => Or None s0 (big_or r xs)
      end = v' `|` e
      & v' `<=` vars t].
Proof.
  have ? : forall x, exists v' e : fvS, [/\ all_min n e,  fset0 = v' `|` e  & v' `<=` x].
    by exists fset0,fset0; rewrite fsetU0//all_min_fset0.
  rewrite/bc; case: ifP => //= I fsn ft.
  rewrite !push/=.
  set X := fresh _.
  have:= leqnn X; rewrite{1}/X.
  rewrite 3!freshPU -!andbA => /and4P[Xn Xs Xdt].
  clearbody X; case: prog => rs sig/=.
  elim: rs => //=-[h b] rs IH; rewrite v_prog_cons/varsU_rhead/varsU_rprem/=.
  rewrite !freshPU -andbA => /and3P[fh fb frs].
  have [v'[e[H1 H2 H3{IH}]]] := IH frs.
  rewrite /=/fresh_rule/=!push/=.
  case H: H => [[ty s']|]//=; last by exists v', e.
  rewrite !vars_tree_atom_big_or.
  replace (varsU _) with (v' `|` e); last first.
    by move: H2; case: select => //-[]/=? bx l; rewrite vars_tree_atom_big_or.
  clear H2.
  set FA := fresh_atoms _ _ _.
  exists  v', (e `|` vars_atoms FA.2).
  split => //=; last first.
    by rewrite fsetUA (fsetUC e) fsetUA (fsetUC v').
  apply/forallP => -[[x]/=]; rewrite in_fsetU => /orP[]xP.
    by have:= forallP H1 [`xP].
  move: Xn; rewrite freshP1 => Xn.
  apply: all_min_vars_atoms_in xP.
    by apply/leq_trans/fresh_sub/leq_trans/fresh_rules_sub/ltnW.
  apply: all_min_fresh_tm.
    by apply/leq_trans/fresh_rules_sub/ltnW.
  by rewrite codomf0; apply/forallP => -[].
Qed.

Lemma vars_atoms_step p n s t: 
  fresh (vars_sigma s) <= n -> fresh (vars_tree t) <= n ->
  let vs := vars_tree_atom (step u p n s t).2 in
  exists v' e, [/\ all_min n e, vs = v' `|` e & v' `<=` vars_tree_atom t].
Proof.
  have H : forall x, exists v' e : fvS, [/\ all_min n e,  fset0 = v' `|` e  & v' `<=` x].
    by exists fset0,fset0; rewrite fsetU0//all_min_fset0.
  rewrite/=; elim_tree t s => vsn; rewrite //=?push/=.
  - case: t => [|t]; rewrite//=!push/=.
    by apply: vars_atoms_bc.
  - rewrite 2!freshPU -andbA => /and3P[vA vB vs].
    have [v'[e[H1 H2 H3]]] := HA s vsn vA.
    case: ifP => //=cA.
      rewrite fsetU0; exists v', e; split => //.
      by rewrite (fsubset_trans H3)//fsubsetUl.
    exists (v'`|` vars_tree_atom B), e; split => //.
      by rewrite -fsetUA (fsetUC _ e) fsetUA H2.
    by rewrite fsetSU//.
  - by rewrite freshPU => /andP[vB vs]; apply: HB.
  - rewrite !freshPU -andbA/= => /and3P[vA vB vB0]/=.
    have [v'[e[H1 H2 H3]]] := HA s vsn vA.
    case: ifP => //=sA; last first.
      exists (v'`|` vars_tree_atom B `|` vars_atoms B0), e; split => //.
        rewrite H2 -!fsetUA (fsetUC _ e) !fsetUA; f_equal.
        by rewrite -!fsetUA; f_equal; rewrite fsetUC.
      by rewrite !fsetSU.
    have [vx[ex[H1' H2' H3']]] := HB (next_subst s A) (vars_sigma_next_subst vA vsn) vB.
    case: ifP => K; rewrite H2'.
      exists (vars_tree_atom (cutl A) `|` vx `|` vars_atoms B0), ex; split => //.
        by rewrite -!fsetUA; do 2 f_equal; apply: fsetUC.
      rewrite fsetSU//fsubUset (fsubset_trans H3' (fsubsetUr _ _)) andbT.
      by rewrite (fsubset_trans (vars_tree_atom_cutl _))//fsubsetUl.
    exists (vars_tree_atom A `|` vx `|` vars_atoms B0), ex; split => //.
      by rewrite -!fsetUA; do 2 f_equal; apply: fsetUC.
    rewrite fsetSU//fsubUset (fsubset_trans H3' (fsubsetUr _ _)) andbT.
    by rewrite fsubsetUl.
Qed.

Lemma disj_tree_step p n s t: fresh (vars_sigma s) <= n -> fresh (vars_tree t) <= n ->
  disj_tree t -> disj_tree (step u p n s t).2.
Proof.
  elim_tree t s => /=vsn. 
  - move=> _ _; case: t => //t; rewrite !push/=.
    apply: disj_tree_bc.
  - rewrite 2!freshPU -andbA.
    move=> /and3P[vrA vrB vrs] /and3P[dAB vA vB]; rewrite !push/=.
    rewrite HA//; case: ifP => //=; first by rewrite fdisjointX0.
    rewrite vB andbT.
    move=> _.
    have /=[v'[e[AM VT VS]]] := vars_atoms_step p vsn vrA.
    rewrite VT fdisjointUX (fdisjointWl VS)//=.
    apply: fdisjointWr (vars_tree_atom_vars_tree_sub _) _.
    rewrite fdisjoint_sym.
    apply: min_max_S_disj 0 (n) (n) (fresh e) _ _ _ => //.
      apply/forallP => //=-[[x]xP]/=.
      apply/leq_trans/vrB.
      rewrite leqNgt; apply/contraTN/xP => H.
      by have:= fresh_sub_notin H.
    apply/forallP => -[[x]xP]/=.
    have/=->:= forallP AM [`xP].
    rewrite leqNgt; apply/contraTN/xP => H.
    by have:= fresh_sub_notin H.
  - by rewrite freshPU => /andP[vrB vsm]; move=> vB; rewrite !push/=HB.
  - rewrite !freshPU -andbA => /and3P[vrA vrB vrB0] /andP[dA dB].
    case: ifP => sA; rewrite !push/=?HA//.
    apply/andP; split.
      by case: ifP; rewrite//=disj_tree_cutl.
    by apply/HB/dB/vrB/vars_sigma_next_subst.
Qed.

Lemma fresh_vars_tree_sub p v0 s1 A: fresh (vars_sigma s1) <= v0 -> fresh (vars_tree A) <= v0 ->
  fresh (vars_tree (step u p v0 s1 A).2) <= (step u p v0 s1 A).1.1.
Proof.
  elim_tree A v0 s1 => //=vs; rewrite ?push/=?freshPU-?andbA.
  - case: t => [|t]// H.
    have b0: 0 < v0 by destruct v0.
    rewrite !push/=.
    case X: bc => //=[n'[|[s0 r0]rs]]//=; first rewrite freshP0.
      by have:= bc_sub u p t v0 s1; rewrite X; destruct v0, n'.
    have ST : sum_mt 0 fmap0 t <= v0.
      by rewrite/sum_mt !freshPU/= codomf0 freshP0 freshP1 /= b0.
    rewrite freshPU.
    by have [->] := vars_tm_bc_sub ST vs X.
  - move=> /and4P[vrA vrB vrd vrc].
    have H:= vars_tree_step_sub u p A v0 s1.
    rewrite HA//=(leq_trans vrc H).
    rewrite (leq_trans vrd H) !andbT.
    case: ifP => //=; last by rewrite (leq_trans vrB H).
    rewrite (leq_trans _ H)//freshP0.
    by destruct v0.
  - move=> /and3P[vB vrd vrc].
    have H:= vars_tree_step_sub u p B v0 sm.
    by rewrite (leq_trans vrc H)(leq_trans vrd H) !andbT HB//= freshPU vrd.
  - move=> /and3P[vrA vrB vrB0].
    have H:= vars_tree_step_sub u p A v0 s1.
    have {}HA := HA _ _ vs vrA.
    case: ifP => /=sA; rewrite !freshPU/=; last first.
      by rewrite HA !(leq_trans _ H).
    have FS := vars_sigma_next_subst vrA vs.
    have {}HB := HB v0 (next_subst s1 A) FS vrB.
    have H':= vars_tree_step_sub u p B v0 (next_subst s1 A).
    rewrite (leq_trans vrB0)// HB !andbT.
    suffices HH: fresh (vars_tree A) <= (step u p v0 (next_subst s1 A) B).1.1.
      by case: ifP; rewrite//(leq_trans (vars_tree_cutlF _)).
    rewrite (leq_trans vrA)//.
Qed.

Lemma disj_tree_run p n t t' s s':
  fresh (vars_tree t) <= n ->
  fresh (vars_sigma s) <= n ->
  disj_tree t ->
  (exists b n', runT u p n s t (Many s' t') b n') ->
  disj_tree t'.
Proof.
  move=> +++ [b[n' R]].
  remember (Many _ _) as r eqn:H.
  elim_run R s' t' H => Lt Ls D.
    by move: H => [_<-]; apply: disj_tree_prune NS.
    move: eA; rewrite (surjective_pairing (step _ _ _ _ _)) => -[+ ?]; subst.
    rewrite (surjective_pairing (fst _)) => -[??]; subst.
    apply/IH/disj_tree_step => //.
    by apply: fresh_vars_tree_sub.
    by rewrite (leq_trans Ls)//vars_tree_step_sub.
  apply/IH/disj_tree_prune/nA => //.
  by apply: vars_tree_prune_sub_flow nA.
Qed.

Print Assumptions disj_tree_run.
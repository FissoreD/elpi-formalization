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

Lemma disj_tree_big_or p n s t:
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
  set F := fresh_rules _ _.
  case H: H => [[ty n']|]//=; last by apply: IH.
  move: (IH Fr); case S: select => //=[|[s0 x0] xs]/=; rewrite disj_tree_big_and//=.
  move=> {}IH; rewrite IH andbT.
  rewrite vars_atoms_big_and/fresh_rule !push/=fdisjoint_sym.
  rewrite-/F in S; set Frh := fresh_tm _ _ _.
  apply: min_max_S_disj 0 F.1.+1 F.1 ((fresh_atoms Frh.1 Frh.2 b)).1.1 _ _ _.
    by [].
    apply/forallP => -[[v]vP]/=.
    admit.
  apply/forallP => -[[v]vP]/=; apply/andP; split.
  (*TODO: all vars in `vars_tree_atom (big_or x0 xs)` are <= F.1 *)
  (*      all vars in `(fresh_atoms (fresh_tm F.1 fmap0 h).1 (fresh_tm F.1 fmap0 h).2 b).2` are > F.1 *)
Admitted.

Lemma disj_tree_step p n s t:
  disj_tree t -> disj_tree (step u p n s t).2.
Proof.
  elim_tree t s => /=.
  - move=> _; case: t => //t; rewrite !push/=.
    by apply: disj_tree_big_or.
  - move=> /and3P[dAB vA vB]; rewrite !push/=.
    rewrite HA//; case: ifP => //=; first by rewrite fdisjointX0.
    rewrite vB andbT.
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
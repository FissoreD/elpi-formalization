From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop fresh.

Definition all_min m (r: {fset V}) := 
  [forall x : r, let: IV x := val x in m <= x].

Definition all_max M (r: {fset V}) := 
  [forall x : r, let: IV x := val x in x <= M].

Definition min_maxS (s:{fset V}) m M :=
  [forall x : s, let: IV x := val x in m <= x < M].

Lemma all_min_fresh_tm:
  forall q m r h, m <= q ->
  let x := fresh_tm q r h in
  all_min m (codomf r) ->
  all_min m (codomf x.2).
Proof.
  move=> /=q m r t; elim: t m q r => //[v|f Hf a Ha] m q r mq.
    rewrite/=; case: ifP => //=vr.
    rewrite/all_min/= codomf_setN?vr//.
    move=> /forallP H; apply/forallP => -[[x]]/=.
    rewrite in_fsetU in_fset1/=; case: eqP; first by move=> [->].
    by move=> /= _ yr; apply: H [`yr].
  move=> mr/=; rewrite !push.
  by apply/Ha/Hf/mr/mq/leq_trans/fresh_sub.
Qed.

Lemma all_min_vars_atoms:
  forall q m r h, m <= q ->
  let x := fresh_atoms q r h in
  all_min m (codomf r) ->
  all_min m (codomf x.1.2).
Proof.
  move=> /=q m r t; elim: t m q r => [|x xs IH] m q r mq l//=.
  rewrite !push/=; case: x => [|t]; first by apply: IH.
  rewrite/=!push/=.
  apply/all_min_fresh_tm/IH/l/mq.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma all_min_ren v t m B:
  vars_tm t `<=` domf B ->
  all_min m (codomf B) ->
  IV v  \in vars_tm (ren B t) ->
  m <= v.
Proof.
  elim: t v m B => [p|v|f Hf a Ha]//=v' m B; rewrite (fsub1set,fsubUset) (in_fsetU, in_fset1).
    move=> vB; rewrite in_fnd//==> H /eqP H1.
    have v'B : IV v' \in codomf B by apply/codomfP; exists v; rewrite in_fnd H1.
    by have:= forallP H [`v'B].
  by move=> /andP[fB aB] l/orP[/Hf|/Ha]->//.
Qed.

Lemma all_min_vars_atoms_in m A B v b:
  m <= A -> all_min m (codomf B) ->
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
  apply: all_min_ren VT.
    apply: fresh_tm_sub1.
  apply/all_min_fresh_tm/all_min_vars_atoms/lmb/VX.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma min_max_fresh_tm r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_tm M r q in
  min_maxS (codomf x.2) m x.1.
Proof.
  elim: q M r => /=[p|v|f Hf a Ha] M r// mm MM; last by (rewrite push; apply/Ha/Hf; rewrite//(leq_trans mm)//fresh_sub).
  case: fndP => vr//=; rewrite codomf_setN//.
  apply/forallP => -[[x] xP]/=; move: xP.
  rewrite 2!inE; case: eqP => [[->]|]; first by rewrite mm/=.
  by move=> xm H; have /andP[->/leq_trans->]:= forallP MM [`H].
Qed.

Lemma min_max_fresh_atom r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_atom M r q in
  min_maxS (codomf x.1.2) m x.1.1.
Proof. by case: q => //=t mm MM; rewrite !push/=; apply: min_max_fresh_tm. Qed.

Lemma min_max_fresh_atoms r m M q:
  m <= M ->
  min_maxS (codomf r) m M ->
  let x := fresh_atoms M r q in
  min_maxS (codomf x.1.2) m x.1.1.
Proof.
  elim: q M r => //=[x xs IH] M r// mm MM; rewrite !push/=.
  by apply/min_max_fresh_atom/IH/MM/mm/leq_trans/fresh_atoms_sub.
Qed.

Lemma min_maxP s:
  min_maxS s 0 (fresh s).
Proof.
  apply/forallP => -[[x] xP]/=.
  case: (boolP (_ < _)) => //=.
  by rewrite -leqNgt => /fresh_sub_notin; rewrite xP.
Qed.

Lemma min_max_fresh_tm0 fv q:
  let x := fresh_tm fv fmap0 q in
  min_maxS (codomf x.2) fv x.1.
Proof.
  move=> /=.
  have MM : min_maxS (codomf fmap0) fv fv.
    by move=> t; apply/forallP => -[[x]]; rewrite /= codomf0//.
  by have := @min_max_fresh_tm fmap0 fv fv q (leqnn _) (MM _).
Qed.

Lemma min_maxU a b m M:
  min_maxS a m M -> min_maxS b m M -> min_maxS (a `|` b) m M.
Proof. 
  move=> M1 M2; apply/forallP => -[[x]xP]/=; move: xP; rewrite inE => /orP[]H.
    by have:= forallP M1 [`H].
  by have:= forallP M2 [`H].
Qed.

Lemma vars_tm_ren_codom_sub w t1: vars_tm t1 `<=` domf w -> vars_tm (ren w t1) `<=` codomf w.
Proof.
  elim: t1 => //=[v|f Hf a Ha].
    by rewrite fsub1set => vw; rewrite in_fnd/=fsub1set in_codomf.
  by rewrite !fsubUset => /andP[/Hf-> /Ha->].
Qed.

Lemma min_max_fresh_rules fv r:
  let x := fresh_rules fv r in
  min_maxS (v_prog x.2) fv x.1.
Proof.
  move=> /=; apply/forallP => -[[x]xP]/=.
  elim: r fv xP => //=r rs IH fv; rewrite !push/= v_prog_cons.
  rewrite 2!inE => /orP[]; last first.
    move=> /IH/andP[->]/= Hx.
    by apply/leq_trans/fresh_rule_sub.
  set X:= (fresh_rules _ _).1.
  rewrite/fresh_rule; case: r => h b; rewrite /varsU_rhead/varsU_rprem !push/=.
  set Y:= fresh_tm _ _ _.
  move=> /orP[].
    have/= H:= @min_max_fresh_tm0 X h.
    rewrite -/Y in H.
    move=> H1.
    have:= vars_tm_ren_codom_sub (fresh_tm_sub1 X fmap0 h).
    rewrite-/Y => Hx.
    have /andP[Hl Hr] := forallP H [`(fsubsetP Hx _ H1)].
    apply/andP; split; last first.
      by apply/leq_trans/fresh_atoms_sub.
    apply/leq_trans/Hl/fresh_rules_sub.
    Search fresh_atoms.
  elim: b => //-[|t]/= xs {}IH; rewrite !push/=vars_atoms_cons/=.
    by rewrite fset0U.
  rewrite inE => /orP[]; last first.
    move=> /IH/andP[->] H.
    apply: leq_trans H _.
    by apply fresh_sub.
  clear IH.
  set F := fresh_atoms _ _ _.
  set Z := fresh_tm _ _ _.
  have xx: fv <= F.1.1.
    apply/leq_trans/fresh_atoms_sub/leq_trans/fresh_sub/fresh_rules_sub.
  have yy: min_maxS (codomf F.1.2) fv F.1.1.
    have kk : fv <= Y.1 by apply/leq_trans/fresh_sub/fresh_rules_sub.
    have zz : min_maxS (codomf Y.2) fv Y.1.
      apply/min_max_fresh_tm; first by apply/fresh_rules_sub.
      by rewrite codomf0//; apply/forallP => -[].
    have/= H := @min_max_fresh_atoms Y.2 fv Y.1 xs kk zz.
    by rewrite -/F in H.
  have/= H:= @min_max_fresh_tm F.1.2 fv F.1.1 t xx yy.
  rewrite-/Z/= in H.
  move=> Hx.
  have:= vars_tm_ren_codom_sub (fresh_tm_sub1 F.1.1 F.1.2 t).
  rewrite-/Z => Hy.
  by have := forallP H [`(fsubsetP Hy _ Hx)].
Qed.

Lemma min_max_S_disj s1 s2 m1 m2 M1 M2:
  M1 <= m2 ->
  min_maxS s1 m1 M1 ->
  min_maxS s2 m2 M2 ->
  fdisjoint s1 s2.
Proof.
  move=> mm H1 H2; apply/fdisjointP => -[x] xs1.
  case: (boolP (_ \in _)) => //xs2.
  have /andP[m1x xM1] := forallP H1 [`xs1].
  have /andP[m2x xM2] := forallP H2 [`xs2].
  have {xM1} xm2 := leq_trans xM1 mm.
  have:= leq_trans xm2 m2x.
  by rewrite ltnn.
Qed.
From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop fresh unif tree_vars.
Open Scope fmap_scope.
Open Scope fset_scope.

(* Lemma fresh_tm_limits fv m h:
  fresh (codomf m) <= fv ->
  fv < fresh (vars (fresh_tm fv m h).1) <= (vars (fresh_tm fv m h)).1. *)

(* Lemma fresh_tm_limits fv m h:
  vars h `<=` domf m ->
  fresh (codomf m) <= fv ->
  vars (ren m h) = fset0 \/
  fv < fresh (vars (ren m h)) <= fresh (codomf m).
Proof.
  move=> hm mf.
  elim: h hm => //=[p|v|f Hf a Ha].
    by left.
    rewrite fsub1set => vm; rewrite in_fnd/=; right.
    case MV: m.[vm] => [n]; rewrite freshP1.
    Search fresh.
    have:= freshP mf.
    Search fresh codomf.
    rewrite freshP0.
  Search ren fsubset.

(* Search ren vars leq. *) *)

Search fresh_atoms.

Lemma fresh_vars_atoms_limits n m r:
  fresh (domf m) <= n ->
  fresh (vars_atoms r) <= n ->
  let f := fresh_atoms n m r in
  [/\ f.1.1 = n & vars_atoms f.2 = fset0] \/ 
  [/\ n.+1 < fresh (vars_atoms f.2) <= f.1.1 & true].
Admitted.


Lemma fresh_rule_limits fv x: 
  let f := (fresh_rule fv x) in
  (varsU_rule f.2 = fset0) \/ fv < fresh (varsU_rule f.2) <= f.1.
Proof.
  case: x => h b/=.
  rewrite/fresh_rule !push/varsU_rule/=/varsU_rhead/varsU_rprem/=.
  rewrite !freshUU/=leq_max geq_max.
  set fh := fresh_tm  _ _ _.
  set fb := fresh_atoms _ _ _.
  set r  := ren _ _.
  case: (set0IN (vars r)) => [->|[k kfr]].
    rewrite fset0U freshP0.
    case: (set0IN (vars_atoms fb.2)) => [->|[k kfr]]; [by left; []|right].
    apply/and3P; split.
    - apply/orP; right.
      rewrite (leq_ltn_trans (fresh_sub fv [fmap] h))//=-/fh.
      Search fresh vars_atoms.
      admit.
    - move: kfr; rewrite/fb. rewrite/fb/fresh_atoms.
      (* case: b fb kfr => //=[|x xs] fb.
        rewrite/fh/fresh_tm.
      Search fresh vars_atoms. *)
Admitted.

Lemma vars_rules_limits fv fv' rs rs':
  let r := varsU [seq varsU_rule i  | i <- rs'] in
  fresh_rules fv rs = (fv', rs') ->
  r = fset0 \/ fv < fresh r <= fv'.
Proof.
  elim: rs fv fv' rs' => /=[>[_<-]//|x xs IH fv fv' rs']; first by left.
  rewrite !push/= => -[<-<- {fv' rs'}].
  have:= fresh_rules_sub xs fv.
  case frs: fresh_rules => [fv' xs']/=ff.
  have /= := fresh_rule_limits fv' x.
  have:= (IH _ _ _ frs).
  set fr := varsU_rule _; set fr' := varsU _ => {}IH.
  move=> [->|/andP[H1 H2]].
    rewrite fset0U; case: IH => [->|/andP[-> H2]/=]; [left; by []|right].
    by rewrite (leq_trans H2)//fresh_rule_sub.
  right; case: IH => [->|/andP[IH1 IH2]].
    by rewrite fsetU0 (leq_ltn_trans ff).
  rewrite /= freshUU leq_max IH1 orbT/= geq_max H2/=.
  by rewrite (leq_trans IH2)//fresh_rule_sub.
Qed.

Lemma vars_tree_bc_limits p t s fv fvx s0 r0 rs: 
  fresh (vars_tm t) <= fv ->
  fresh (vars_sigma s) <= fv ->
  bc u p fv t s = (fvx, (s0, r0) :: rs) ->
  exists2 k : fvS, 
    fv < fresh k <= fvx & 
      k `|` vars_tm t `|` vars_sigma s = vars_tree (big_or r0 rs) `|` vars_sigma s0.
Proof.
  rewrite/bc; case: ifP; first by [].
  move=> /negbFE Is ft fs; rewrite !push/= => -[?]; subst.
  case: p => /= p sP.
  set t' := deref _ _.
  set fv' := fresh (_ `|` _).
  case X: fresh_rules => [fv'' rs']/=/[dup]+->.
  have:= vars_rules_limits .
  
  (* have: fv' < fresh (varsU (map varsU_rule rs')) <= fv''. *)

    (* have:= fresh_rules_sub p fv'; rewrite X/=. *)
    Search fresh_rules.
  
  Search R "vars".
  About fresh_rules.
  have: varsU (vars_rule )
  elim: rs' X => //x xs.
  move=> H; rewrite H.
  have:= leqnn fv'.
  (* About select. *)
  (* have:= fresh_rules_sub p fv'. *)
  rewrite {1}/fv' 3!freshUU !geq_max -!andbA freshP1.
  move=> /and4P[ff fs' ft' fp].
  elim: rs'.
  move: H; rewrite/select.
  elim: rs'.

  Search vars deref.
  Search maxn leq.
  have ff : fv < fv'.
    by rewrite/fv'; rewrite -!fsetUA freshUU freshP1 leq_max ltnSn.
  have ft':= leq_trans (leqW ft) ff.
  have fs':= leq_trans (leqW fs) ff.

  Search (_ <= _.+1).
  have : 
  


    move=>[<-].



Lemma vars_tree_step_sub_flow A R fv fv' s r:
  fresh (vars_tree A) <= fv -> fresh (vars_sigma s) <= fv ->
  step u p fv s A = (fv', r, R) -> 
    (vars_tree R `<=` vars_tree A `|` vars_sigma s \/ (exists2 k, fv < fresh k <= fv' & k `|` vars_tree A `|` vars_sigma s = vars_tree R)).
Proof.
  elim_tree A R fv fv' r s => /=; only 1,2: by move=> _ _[<-_<-]/=; left.
  - case: t; first by move=> _ _[<-_<-]/=; left.
    move=> t ft fs; rewrite !push/= => -[???]; subst.
    case X: bc => [fvx [|[s0 r0] rs]]//=; [by left; []|right].

    have:= vars_tm_bc_sub _ fs X.


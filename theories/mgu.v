From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From det Require Import finmap ctx.
From det Require Import lang unif.

(* TODO:
  goal : f X = f Y
  base = fmap0
  s = X -> Y
  s'= Y -> X
  (Y -> X) = (X -> Y) + ?x
  Quale x??
*)
(* Definition mgu_help base s l := *)
  (* forall s', acyclic s' -> mp base s' -> unifier s' l ->  *)
    (* exists x, s' = composition s x. *)
Definition invm (m: {fmap V -> V}) :=
  [forall x: domf m, (m.[? m.[valP x]] == Some (val x))].
 
Lemma invm_injective m: invm m -> injectiveb m.
Proof.
  move=> I; apply/injectiveP => -[x xP] [y yP] H.
  have:= forallP I [`xP]; rewrite valPE/= {}H; case: fndP => //ypm /eqP[yx].
  have:= forallP I [`yP]; rewrite valPE/= in_fnd yx => /eqP[?]; subst.
  by apply: val_inj => /=.
Qed.

Lemma invm0: invm fmap0. by apply/forallP => -[]. Qed.

Record ren_mgu := mk_renm {
  renm_map :> {fmap V -> V};
  renm_inv : invm renm_map
}.


Definition is_mgu (mgu s : Sigma) :=
  exists r : ren_mgu,
      forall t, ren r (deref s (deref mgu t)) = deref s t.


Definition mgu_help base mgu l :=
  forall s, acyclic s -> unifier s l -> is_mgu base s -> is_mgu mgu s.

Lemma mgu_help_refl b l: mgu_help b b l.
Proof. by move=> *. Qed.

Lemma mgu_help_tt b s t l: mgu_help b s l -> mgu_help b s ((t, t) :: l).
Proof. by move=> H x A /=/andP[_ U] M; apply: H. Qed.

Lemma mgu_help_app b s f1 f2 a1 a2 l:
  mgu_help b s [:: (f1, f2), (a1, a2) & l] ->
  mgu_help b s ((Tm_App f1 a1, Tm_App f2 a2) :: l).
Proof.
  move=> H x A /=; rewrite unif_pair_app -andbA => /and3P[U1 U2 U].
  by apply: H; rewrite//= U1 U2.
Qed.

Lemma mgu_help_cons_comm s s' t1 t2 l:
  mgu_help s s' ((t1, t2) :: l) ->
  mgu_help s s' ((t2, t1) :: l).
Proof.
  move=> H x A /=/andP[/eqP/= U1 U2] M.
  by apply: H => //=; rewrite /unif_pair/map_prod1/= U1 eqxx.
Qed.

Lemma is_mgu_deref_sigma v t mgu s (vs': v \in domf s):
  acyclic mgu -> acyclic s -> v \notin vars t ->
  s.[vs'] = deref s t -> v \notin domf mgu ->
  is_mgu mgu s -> is_mgu (deref_sigma v t mgu) s.
Proof.
  move=> Am As vt H vm [r C].
  exists r => q.
  rewrite -(C q); f_equal.
  elim: q => //[v'|f/= -> a ->//].
  rewrite !deref_V FmapE.fmapE.
  case: eqP => vv; subst.
    by rewrite not_fnd// -H/=in_fnd.
  case: fndP => vm'; [rewrite in_fnd|rewrite not_fnd] => //.
  rewrite ffunE valPE/= /derefkv; simpl in vm'.
  (* TODO: externalize *)
  move: (mgu.[_]) => q{v' vv vm'}; elim: q => //[v'|/=f -> a ->//].
  rewrite !deref_V FmapE.fmapE not_fnd//=.
  case: eqP => vv; subst => //=.
  by rewrite in_fnd H.
Qed.

Lemma mgu_help_deref_sigma v t s l mgu:
  acyclic s -> v \notin domf s -> v \notin vars t ->
  mgu_help (deref_sigma v t s) mgu (deref_list v t l) ->
  mgu_help s mgu ((Tm_V v, t) :: l).
Proof.
  move=> A vs vt IH.
  move=> x A' /=/andP[/eqP/= + Ul] M.
  case: (boolP (is_var t)) => VT; last first.
    case: fndP => /=; last by destruct t.
    move=> vx H.
    apply: IH => //.
      apply: unifier_deref_list => //.
      apply/forallP => -[y yP]; rewrite valPE ffunE[val _]/=.
      by move: yP; rewrite !inE orbF => /eqP?; subst; rewrite eqxx/= -H in_fnd.
    by apply: is_mgu_deref_sigma.
  destruct t as [|v'|] => //.
  simpl in *.
  case: fndP => vx/= H.
    apply: IH => //.
      apply: unifier_deref_list => //=.
      apply/forallP => -[y yP]; rewrite valPE ffunE[val _]/=.
      by move: yP; rewrite !inE orbF => /eqP?; subst; rewrite eqxx/= -H in_fnd.
    by apply: is_mgu_deref_sigma => //; rewrite fdisjointX1 in D1.
  rewrite inE in vt.
  move: H; case: fndP => //= vx'; last by move=> [?]; subst; rewrite eqxx in vt.
  move=> H.
  apply: IH => //.
    by apply: unifier_deref_list_not_in.
  move: M => [r M].
  exists r => //t.
  have {M} := M t.
  elim: t => //[v2|/=f Hf a Ha[H1 H2]]; last by rewrite Hf// Ha.
  rewrite !deref_V FmapE.fmapE.
  case: eqP => vv; subst.
    by rewrite not_fnd//= not_fnd//= (in_fnd vx')/= -H.
  case: fndP => //v2s.
    by case: fndP => v2x; rewrite in_fnd ffunE valPE/= derefkv_not_in//.
  case: fndP => v2x; rewrite not_fnd//.
Qed.


Lemma montanariPmgu b l s mgu: acyclic s -> disjoint_L s l ->
  montanari s b l = Some mgu -> mgu_help s mgu l.
Proof.
  move: mgu; montanari_ind s b l => mgu A//; cycle -1.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D M].
    have {IH M} := IH _ A _ M; rewrite disjoint_L_cons/= d2 d1 D.
    move=> /(_ isT).
    apply: mgu_help_cons_comm.
  - by move=> _ [<-]; apply: mgu_help_refl.
  - by rewrite disjoint_L_cons => /and3P[Dt _ Dl] M; apply/mgu_help_tt/IH.
  - rewrite disjoint_L_cons /=!fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 D] M.
    apply/mgu_help_app/IH; auto.
    by rewrite !disjoint_L_cons/=d1 d2 d3 d4.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M IH} := IH _ (acyclic_sigma_deref_sigma _ _ A) (disjoint_deref_sigma_deref_list A _ _ _) M.
    rewrite inE in vt.
    rewrite inE/= eq_sym => /(_ vt D1 D1 vt D3) IH.
    apply: mgu_help_cons_comm; rewrite !fdisjointX1 in D1, D2.
    by apply: mgu_help_deref_sigma IH; rewrite//=inE eq_sym.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M}IH := IH _ (acyclic_sigma_deref_sigma vt D2 A) (disjoint_deref_sigma_deref_list A D2 vt D3) M.
    by apply: mgu_help_deref_sigma IH; rewrite fdisjointX1 in D1. 
Qed.

Definition mgux m t1 t2 :=
  acyclic m /\ deref m t1 = deref m t2 /\ forall s, acyclic s -> deref s t1 = deref s t2 -> 
    exists r : ren_mgu,
      forall t, ren r (deref s (deref m t)) = (deref s t).

Definition mgu m t1 t2 :=
  acyclic m /\ deref m t1 = deref m t2 /\ forall s, acyclic s -> deref s t1 = deref s t2 -> 
    exists s',
      forall t, deref s' (deref m t) = (deref s t).
      
Lemma mmgu: forall m t1 t2, mgux m t1 t2 -> mgu m t1 t2.
Proof.
  move=> m t1 t2 [A[D H]].
  repeat split => //; move=> s As Ds.
  have [[r M]/= F] := H _ As Ds.
  exists ([fmap x : domf r => Tm_V (r.[valP x])] + [fmap x : domf s => ren r s.[valP x]]).
  move=> t; rewrite -(F t).
  elim: t {F} => //[v|/=f -> a ->//].
  rewrite !deref_V.
  case: fndP => vm.
    move: (m.[vm]) => t; elim: t => //[v'|/=f -> a ->//]; last first.
    rewrite !deref_V; rewrite FmapE.fmapE [domf _]/=.
    case: (fndP s) => vs'//.
      by rewrite (@in_fnd _ _ [fmap _ => _])/= ffunE valPE//.
    rewrite ren_V; case: fndP => //=vr; [rewrite in_fnd|rewrite not_fnd] => //.
    by rewrite ffunE valPE//=.
  rewrite !deref_V.
  rewrite fnd_cat [domf _]/=; case: (fndP s) => vs.
    by rewrite (@in_fnd _ _ [fmap _ => _]) ffunE valPE.
  rewrite ren_V; case: fndP => //=vr; [rewrite in_fnd|rewrite not_fnd] => //.
  rewrite ffunE valPE//.
Qed.

Lemma ren_empty t: ren fmap0 t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.

Lemma is_mgu0 s: is_mgu fmap0 s.
Proof.
  exists (mk_renm invm0) => t/=.
  by rewrite ren_empty deref_empty.
Qed.

(*SNIPT: unif_correct *)
Lemma unify_correct t1 t2 s:
  unify t1 t2 fmap0 = Some s -> mgu s t1 t2.
(*ENDSNIPT: unif_correct *)
Proof.
  move=> U.
  have H := montanariPmgu acyclic_sigma0 (disjoint_Lempty _) U.
  apply: mmgu.
  rewrite !deref_empty in H; repeat split.
    apply: unif_acyclic acyclic_sigma0 U.
    by have:= unify_P acyclic_sigma0 U.
  move=> s' A D.
  have:= H s' A; rewrite/=/unif_pair/map_prod1 D eqxx.
  move=> /(_ isT (is_mgu0 _)) [r].
  by exists r.
Qed.

(*SNIPT: unify_complete *)
Lemma unify_complete:
  forall t1 t2, (exists s, acyclic s /\ deref s t1 = deref s t2) -> exists s', unify t1 t2 fmap0 = Some s'.
(*ENDSNIPT: unify_complete *)
Proof.
  move=> t1 t2 [sx [H1 H2]].
  rewrite /unify/montanari_deref/montanari_pair.
  have:= exists_montanari acyclic_sigma0 (disjoint_Lempty _) (ex_intro _ sx _).
  move=> /(_ fset0 [::(deref fmap0 t1, deref fmap0 t2)] ).
  rewrite H1/= /unif_pair/map_prod1/= !deref_empty H2 eqxx fdisjointX0.
  move=> /(_ (And3 isT isT isT)).
  case M: montanari => [s'|]// _.
  by eexists.
Qed.

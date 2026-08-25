From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang ctx.
From det Require Import tree tree_prop unif.

(* valid_tree_subst *)
Fixpoint vts_aux s A :=
  let vts_aux := vts_aux s in
  match A with
  | Unexplored _ | OK | KO => true
  | Or None sm B => [&& mp s sm & vts_aux B]
  | Or (Some A) sm B => [&& mp s sm, vts_aux A & vts_aux B]
  | And A B0 B => vts_aux A && vts_aux B
  end.

Fixpoint vts s A :=
  match A with
  | Unexplored _ | OK | KO => true
  | Or None sm B => vts sm B
  | Or (Some A) sm B => [&& vts_aux s A, vts s A & vts sm B]
  | And A B0 B => [&& vts_aux s A, vts_aux s B, vts s A & vts s B]
  end.

Lemma vts_aux_big_andA s x xs: vts_aux s (big_andA x xs).
Proof. by elim: xs x => //=. Qed.

Lemma vts_aux_big_and s xs: vts_aux s (big_and xs).
Proof. case: xs => //= ??; apply: vts_aux_big_andA. Qed.

Lemma vts_big_and s l : vts s (big_and l).
Proof. by case: l => //= x xs; elim: xs x => //=x xs ->; rewrite vts_aux_big_andA. Qed.

Definition all_mp T sm (l: seq (_ * T)) := all (mp sm) (map fst l).

Lemma all_mp_cons T s x xs: @all_mp T s (x :: xs) = mp s x.1 && all_mp s xs.
Proof. by []. Qed.

Lemma mp_trans: transitive mp.
Proof.
  move=> s1 s0 s2 H1 H2; apply/forallP => -[x xP].
  have:= forallP H1 [`xP]; rewrite [val _]/= valPE => /eqP.
  case: fndP => //= xQ [H]; have:= forallP H2 [`xQ] => /eqP.
  case: fndP => //=xR []; rewrite valPE -{}H => <-.
  rewrite derefxx//.
Qed.

Lemma mp_vts_aux o n t: mp o n -> vts_aux n t -> vts_aux o t.
Proof.
  move=> MP; elim_tree t => //=.
    by move=> /and3P[/(mp_trans MP)->/HA->/HB->].
    by move=> /andP[/(mp_trans MP)->/HB->].
  by move=> /andP[/HA->].
Qed.

Lemma mp_vts o n t: mp o n -> vts n t -> vts o t.
Proof.
  move=> MP; elim_tree t => //=.
    by move=> /and3P[/mp_vts_aux->///HA->->].
  by move=> /and4P[/mp_vts_aux->///mp_vts_aux->///HA->/HB->].
Qed.

Lemma all_mp_trans {T} o n t: mp o n -> @all_mp T n t -> all_mp o t.
Proof. by move=> mon H; apply/allP => x xH; have:= allP H x xH; apply/mp_trans. Qed.

Lemma vts_aux_big_or o a l : all_mp o l -> vts_aux o (big_or a l).
Proof.
  elim: l o a => //= [|[n x] xs IH] o a; first by rewrite vts_aux_big_and.
  by rewrite all_mp_cons => /=/andP[mp/IH->]; rewrite mp vts_aux_big_and.
Qed.


Lemma vts_big_or o a l : vts o (big_or a l).
Proof.
  elim: l o a => //= [|[n x] xs IH] o a; first by rewrite vts_big_and.
  rewrite //=vts_big_and vts_aux_big_and/= IH//.
Qed.

Lemma vt_aux_cut {A} s: vts_aux s A -> vts_aux s (cutl A).
Proof.
  elim_tree A s => /=.
    by move=> /and3P[H1 H2 H3]; rewrite H1 HA.
    by move=> /andP[H1 H2]; rewrite H1 HB.
  by move=> /andP[H1 H2]; case: ifP => //=; rewrite HA//HB//.
Qed.

Lemma vt_cut {A} s: vts s A -> vts s (cutl A).
Proof.
  elim_tree A s => //=.
    by move=> /and3P[H1 H2 H3]; rewrite HA//vt_aux_cut.
    by apply: HB.
  by move=> /and4P[H1 H2 H3 H4]; case: ifP; rewrite//=!vt_aux_cut//HA//HB.
Qed.

Definition u := mk_Unif unify matching.

(* TODO: already in mut_excl *)
Lemma idempotent_H sP fv q hd s1 r:
  idempotent s1 -> H u sP fv q hd s1 = Some r -> idempotent r.2.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a Ha] fv [p'|//|f' a']// s1 r.
    by case: eqP => //= _ A; case: fndP => //=pP[<-].
  move=> A.
  case H: H => [[[|[] tyl tyr] s1']|]//=.
    case M: matching => //= [s1''][?]; subst.
    by apply: matching_idempotent M; apply: Hf H.
  case M: unify => //= [s1''][?]; subst.
  by apply: unif_idempotent M; apply: Hf H.
Qed.


Lemma mp_H froz m l1 l2 s s':
  idempotent s -> H u froz m l1 l2 s = Some s' -> mp s s'.2.
Proof.
  move=>As; elim: l1 s' l2 => //=[p|f Hf a Ha] s' [p'|v'|f' a']//=.
    by case: eqP => //->; case: fndP => //= pf [<-]//=; rewrite mp_id.
  case H: H => //[[[//|md tl tr] s'']].
  case X: (_ a') => //=[sx][<-{s'}]/=.
  apply: mp_trans (Hf _ _ H) _.
  have /=As'' := idempotent_H As H.
  have Hx := disjoint_L_deref _ _ As''.
  case: md X {H} => //=; apply: montanari_mp => //=.
Qed.

Lemma all_mp_select sig t rules s: idempotent s ->
  all_mp s (select u sig t rules s).
Proof.
  move=> A; elim: rules => //= r0 rs IH.
  case H: H => [[ty s']|]//=; rewrite all_mp_cons IH andbT.
  by apply: mp_H H.
Qed.

Lemma all_mp_bc p sv t s r:
  (bc u p sv t s) = r -> all_mp s r.2.
Proof.
  move=> <-; rewrite/bc.
  case (boolP (idempotent s)) => A//=.
  by rewrite !push/=; apply: all_mp_select.
Qed.

Lemma mp_next_subst o A n: mp o n ->
  vts_aux o A -> mp o (next_subst n A).
Proof.
  elim_tree A o n => mon/=.
    by move=> /and3P[H1 H2 H3]; rewrite HA//.
    by move=> /andP[H1 H2]; rewrite HB//.
  move=> /andP[H1 H2]/=; rewrite next_subst_and.
  by case: ifP => //; rewrite !(HA,HB)//.
Qed.

Lemma bc_mp_all p sv sv' t n l:
  bc u p sv t n = (sv', l) ->
  all_mp n l.
Proof.
  rewrite (surjective_pairing (bc _ _ _ _ _)) => -[_{sv'}<-{l}].
  rewrite/bc; case: ifP => //= /negbFE A.
  by rewrite !push/= all_mp_select.
Qed.

Lemma vts_aux_step p o n sv A: mp o n ->
  vts_aux o A -> vts_aux o (step u p sv n A).2.
Proof.
  elim_tree A n o sv => //=mon.
  + case: t => [|t]//=; rewrite push.
    case B : bc => [sv' [|[x sx] xs]]//= _.
    have:= bc_mp_all B; rewrite all_mp_cons.
    move=> /andP[/(mp_trans mon)-> H].
    by rewrite vts_aux_big_or//(all_mp_trans mon).
  + move=> /and3P[H vA vB]; set S:= step _ _ _ _ _.
    by rewrite !push/=HA//=H; case: ifP.
  + by move=> /andP[mn vB]; rewrite !push/= mn/= HB//=.
  + move=> /andP[va vb]; case: ifP => _; rewrite !push/=; last by rewrite HA.
    apply/andP; split; first by case: ifP; rewrite//vt_aux_cut.
    by rewrite HB//mp_next_subst.
Qed.

Lemma vts_step p o n sv A: mp o n ->
  vts o A -> vts o (step u p sv n A).2.
Proof.
  elim_tree A o n sv => /=mon.
  + case: t => [|t]//= _; rewrite push/=.
    case B : bc => [sv' [|[x sx] xs]]//=.
    by rewrite vts_big_or.
  + move=> /and3P[H vA vB]; set S:= step _ _ _ _ _.
    have Hx : vts sm (if is_cb S.1.2 then KO else B) by case: ifP.
    by rewrite !push/= HA//= Hx vts_aux_step//.
  + move=> mp; rewrite !push/= HB//.
    admit.
  + move=> /and4P[va vb van vbn].
    rewrite !fun_if !push/= vbn vb HA//!(HB,vts_aux_step)// ?(mp_id,mp_next_subst)//.
    rewrite !fun_if/= !vt_cut//!vt_aux_cut//= va van.
    repeat case: ifP => //.
Admitted.

Lemma vts_aux_prune o A R b: 
  vts_aux o A -> prune b A = Some R -> vts_aux o R.
Proof.
  elim_tree A R o b => /=.
  + by case: R => //=; case: b => //.
  + by case: t => [|c]//= _ [<-]//.
  + move=> /and3P[mp vA bB]; case nA: prune => [A'|]//=.
      by move=> [<-]/=; rewrite (HA A' _ b)//mp.
    by case nB: prune => [B'|]//[<-]/=; rewrite (HB _ _ _ _ nB)// mp.
  + by move=> /andP[mp vB]; case nB: prune => [B'|]//=[<-]/=; rewrite mp; apply/HB/nB.
  + move=>/andP[vA vB].
    case: ifP => /= _.
      case X: prune => [D|].
        by move=>[<-]/=; rewrite vA /= (HB _ _ _ _ X)//.
      case Y: prune => //=[A'].
      by move=> [<-]/=; rewrite (HA _ _ true)//= vts_aux_big_and//.
    case: ifP => fA; last first.
      by move=> [<-]/=; rewrite vA.
    case X: prune => [D|]//=.
    by move=> [<-]/=; rewrite (HA _ _ false)//= vts_aux_big_and.
  Qed.
  
Lemma vts_prune o A R b: 
  vts o A -> prune b A = Some R -> vts o R.
Proof.
  elim_tree A R o b => /=.
  + by case: R => //=; case: b => //.
  + by case: t => [|c]//= _ [<-]//.
  + move=> /and3P[mp vA bB]; case nA: prune => [A'|]//=.
      by move=> [<-]/=; rewrite (HA _ _ _ _ nA)//=bB andbT (vts_aux_prune _ nA).
    by case nB: prune => [B'|]//[<-]/=; rewrite (HB _ _ _ _ nB)// mp.
  + by move=> vb; case nB: prune => [B'|]//=[<-]/=; apply: HB nB.
  + move=>/and4P[vAa vBa vA vB].
    case: ifP => /= _.
      case X: prune => [D|].
        by move=>[<-]/=; rewrite vA /= (HB _ _ _ _ X)//vAa (vts_aux_prune _ X).
      case Y: prune => //=[A'].
      by move=> [<-]/=; rewrite (HA _ _ true)//= vts_aux_big_and// vts_big_and (vts_aux_prune _ Y).
    case: ifP => fA; last first.
      by move=> [<-]/=; rewrite vA vAa vBa.
    case X: prune => [D|]//=.
    by move=> [<-]/=; rewrite (HA _ _ false)//= vts_aux_big_and (vts_aux_prune _ X)//vts_big_and.
  Qed.

Lemma valid_tree_run p s1 fv A b fv' s R: idempotent s1 ->
  vts s1 A -> runT u p fv s1 A (Many s R) b fv' -> vts s1 R.
Proof.
  remember (Many _ _) as S eqn:HS.
  move=> ++ H.
  elim_run H s R HS => As1 vA.
  + by move: HS => [??]; subst; apply: vts_prune NS.
  + move: eA; rewrite (surjective_pairing (step _ _ _ _ _)) => -[].
    rewrite (surjective_pairing (step _ _ _ _ _).1) => -[???]; subst.  
    apply: IH (vts_step _ _ _ _); rewrite// mp_id//.
  + by apply: IH (vts_prune vA nA).
Qed.

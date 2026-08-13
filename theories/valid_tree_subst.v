From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang ctx.
From det Require Import tree tree_prop unif.

(* valid_tree_subst *)
Fixpoint vts s A :=
  match A with
  | TA _ | OK | KO => true
  | Or None sm B => [&& mp s sm & vts s B]
  | Or (Some A) sm B => 
      [&& mp s sm, vts s A & vts s B]
  | And A B0 B => vts s A && vts s B
  end.

Lemma vts_big_and s l : vts s (big_and l).
Proof. case: l => //=x xs; elim: xs x => //=. Qed.

Definition all_mp T sm (l: seq (_ * T)) := all (mp sm) (map fst l).

Lemma all_mp_cons T s x xs: @all_mp T s (x :: xs) = mp s x.1 && all_mp s xs.
Proof. by []. Qed.

Lemma vts_big_or s a l : all_mp s l -> vts s (big_or a l).
Proof.
  elim: l a => //= [|[s' x] xs IH] a H; first by apply: vts_big_and.
  move: H; rewrite all_mp_cons => /andP[H1 H2]/=.
  by rewrite IH//vts_big_and H1.
Qed.

Lemma vt_cut {A} s: vts s A -> vts s (cutl A).
Proof.
  elim_tree A s => /=.
    by move=> /and3P[H1 H2 H3]; rewrite H1 HA.
    by move=> /andP[H1 H2]; rewrite H1 HB.
  by move=> /andP[H1 H2]; case: ifP => //=; rewrite HA//HB//.
Qed.

Definition u := mk_Unif unify matching.

Lemma mp_trans: transitive mp.
Proof.
  move=> s1 s0 s2 H1 H2; apply/forallP => -[x xP].
  have:= forallP H1 [`xP]; rewrite [val _]/= valPE => /eqP.
  case: fndP => //= xQ [H]; have:= forallP H2 [`xQ] => /eqP.
  case: fndP => //=xR []; rewrite valPE -{}H => <-.
  rewrite derefxx//.
Qed.

Lemma mp_H f m l1 l2 s s':
  acyclic_sigma s -> H u f m l1 l2 s = Some s' -> mp s s'.
Proof.
  elim: m l1 l2 s => [|x xs IH][|l1 l1s][|l2 l2s]//=s A.
    by move=> [<-]; apply: mp_id.
  case M: (_ l2) => [s2|]//= H.
  have D: disjoint_L s [:: (deref s l2, deref s l1)].
    by rewrite disjoint_L_cons !acyclic_deref_disjoint// disjoint_L0.
  suffices [A' M'] : acyclic_sigma s2 /\ mp s s2.
    by apply/mp_trans/IH/H.
  by move: M; case: x => //= M; have -> := matching_acyclic A M;
  have := montanari_mp A D M.
Qed.

Lemma all_mp_select pred args modes rules s r: acyclic_sigma s ->
  select u pred args modes rules s = r -> all_mp s r.2.
Proof.
  move=> A <-; elim: rules => //= r0 rs IH.
  case: ifP => _ //=; case H: H => [s'|]//.
  rewrite//push/=all_mp_cons/= IH andbT.
  by apply: mp_H H.
Qed.

Lemma all_mp_bc p sv t s r:
  (bc u p sv t s) = r -> all_mp s r.2.
Proof.
  move=> <-; rewrite/bc.
  case (boolP (acyclic_sigma s)) => A//=.
  set D := deref _ _; case X: get_tm_hd => [pred|]//=.
  case: fndP => //=pp.
  rewrite !push/=.
  by apply: all_mp_select erefl.
Qed.

Lemma vt_step p o n sv A r: mp o n ->
  vts n A -> step u p sv n A = r -> vts o r.2.
Proof.
  move=>++<-; clear r.
  elim_tree A o n sv => /= mon.
  + case: t => [|t]//=; rewrite push/=.
    case B : bc => [sv' [|[x sx] xs]]/=//= _.
    have:= all_mp_bc B; rewrite all_mp_cons/=.
    move=> /andP[H /vts_big_or].
    admit.
  + move=> /and3P[H vA vB]; set S:= step _ _ _ _ _.
    have Hx : vts n (if is_cb S.1.2 then KO else B) by case: ifP.
    rewrite !push/= HA//=. H Hx andbT/= /S.
    apply: HA.
    rewrite andbT/=.
    app HA s sv; rewrite S.
    apply: 
    have:= HA _ sv vA.

    case: bc => [_ []]//=. -[]//= _ >; rewrite valid_tree_big_or.
  + move=> /andP[vA bB]; rewrite !push/= HA//=; case: ifP => //.
  + by move=> vB; rewrite !push /=; apply: HB.
  + move=> /andP[vA].
    rewrite !push.
    case: ifP => [sA vB /= | sA]/=.
      have {HB} := HB (next_subst s A) sv vB.
      case X: step => //[[?[]]C]/=vC; try by rewrite sA vA vC.
      rewrite success_cut sA/= vC valid_tree_cut//.
    move=> /eqP -> {B HB}.
    have:= HA s sv vA.
    case X: step => //[[sv' []]A']/=vA'; only 1-3: by rewrite eqxx vA' valid_tree_big_and if_same.
    have [? sA']:= step_success X; subst.
    congruence.
Qed.

Lemma valid_tree_prune A R b: 
  valid_tree A -> prune b A = Some R -> valid_tree R.
Proof.
  elim_tree A R b => /=.
  + by case: R => //=; case: b => //.
  + by case: t => [|c]//= _ [<-]//.
  + move=> /andP[vA bB]; case nA: prune => [A'|]//=.
      by move=> [<-]/=; rewrite (HA A' b)//.
    case nB: prune => [B'|]//[<-]/=; apply/HB/nB.
    by move: bB => /orP[/eqP->|/spec_base_or[?[?]]]//<-; apply: valid_tree_big_or.
  + by move=> vB; case nB: prune => [B'|]//=[<-]/=; apply/HB/nB.
  + move=>/andP[vA].
    case: ifP => /=[sA vB|sA]; subst.
      case X: prune => [D|].
        move=>[<-]/=; rewrite vA sA/= (HB _ _ vB X)//.
      case Y: prune => //=[A'].
      by move=> [<-]/=; rewrite (HA _ true)//= valid_tree_big_and eqxx !if_same.
    move=> /eqP->{B HB}.
    case: ifP => fA; last first.
      by move=> [<-]/=; rewrite vA sA eqxx.
    case X: prune => [D|]//=.
    by move=> [<-]/=; rewrite (HA _ false)//= eqxx valid_tree_big_and !if_same.
  Qed.

Lemma valid_tree_run s1 fv A b fv' s R:
  valid_tree A -> runT u p fv s1 A (Many s R) b fv' -> valid_tree R.
Proof.
  remember (Many _ _) as S eqn:HS.
  move=> + H.
  elim_run H s R HS => vA.
  + by move: HS => [??]; subst; apply: valid_tree_prune NS.
  + by apply: IH (valid_tree_step vA eA).
  + by apply: IH (valid_tree_prune vA nA).
Qed.

From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Inductive mode := input | output.
Definition mode_to_bool m := match m with input => true | _ => false end.
Coercion mode_to_bool : mode >-> bool.

Inductive Det := Func | Pred.
Inductive B := Exp | d of Det.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr input x y) (at level 3).
Notation "x '--o-->' y" := (arr output x y) (at level 3).

Definition D2o D : 'I_2 := match D with Func => @Ordinal 2 0 isT | Pred => @Ordinal 2 1 isT end.
Definition o2D (i : 'I_2) : option Det := match val i with 0 => Some Func | 1 => Some Pred | _ => None end.
Lemma D2oK : pcancel D2o o2D. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy Det (pcan_type D2oK).

Definition B2o B : GenTree.tree Det := match B with Exp => GenTree.Node 0 [::] | d D => GenTree.Leaf D end.
Definition o2B (i :  GenTree.tree Det) : option B := match i with GenTree.Node 0 [::] => Some Exp | GenTree.Leaf x => Some (d x) | _ => None end.
Lemma B2oK : pcancel B2o o2B. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy B (pcan_type B2oK).

Fixpoint S2o S : GenTree.tree (B) := match S with b x => GenTree.Leaf (x) | arr i x y => GenTree.Node i [:: S2o x; S2o y] end.
Fixpoint o2S (i :  GenTree.tree (B)) : option S := match i with GenTree.Leaf x => Some (b x) | GenTree.Node ((0 | 1) as m) [:: x; y] => obind (fun x => obind (fun y => Some (arr (if m == 0 then output else input) x y)) (o2S y) ) (o2S x)  | _ => None end.
Lemma S2oK : pcancel S2o o2S. Proof. by elim=> //= -[] ? -> ? ->. Qed.
HB.instance Definition _ := Countable.copy S (pcan_type S2oK).

Goal b Exp == b Exp. by []. Qed.

(* Leave the one line code for the extracted code *)
(*SNIP: base_type*)
Inductive P := IP of nat. Inductive V := IV of nat.
(*ENDSNIP: base_type*)

derive P.
HB.instance Definition _ := hasDecEq.Build P P_eqb_OK.
Definition Kp_of_nat x := IP x.
Definition nat_of_Kp x := match x with IP x => x end.
Lemma Kp_is_nat : cancel nat_of_Kp Kp_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy P (can_type Kp_is_nat).

derive mode.
HB.instance Definition _ := hasDecEq.Build mode mode_eqb_OK.

derive V.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.
Definition V_of_nat x := IV x.
Definition nat_of_V x := match x with IV x => x end.
Lemma V_is_nat : cancel nat_of_V V_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy V (can_type V_is_nat).

(*SNIP: tm_type*)
Inductive Tm := 
  | Tm_P of P
  | Tm_V of V     | Tm_App  of Tm & Tm.
(*ENDSNIP: tm_type*)

derive Tm.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.

(*SNIP: atom_type*)
Inductive Atom := cut | call of Tm.
(*ENDSNIP: atom_type*)

(*SNIP: R_type*)
Record R := mkR { head : Tm; premises : list Atom }.
(*ENDSNIP: R_type*)

derive Atom.
derive R.
HB.instance Definition _ := hasDecEq.Build Atom Atom_eqb_OK.
HB.instance Definition _ := hasDecEq.Build R (R_eqb_OK).

Elpi Command derive.eqbOK.register_axiomx.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.eqType.db.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
   main [str Type, str IsT, str IsTinhab, str Eqb, str Correct, str Refl] :- !,
     coq.locate Type GrType,
     coq.locate IsT GRisT,
     coq.locate IsTinhab GRisTinhab,
     coq.locate Eqb GrEqb,
     coq.locate Correct GrCorrect,
     coq.locate Refl GrRefl,
     GrRefl = const R,
     GrCorrect = const C,
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ _ (eqb-done GrType)),
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ (before "eqb-for:whd") (eqb-for (global GrType) (global GrType) (global GrEqb))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (eqcorrect-for GrType C R)),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (correct-lemma-for (global GrType) (global GrCorrect))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (refl-lemma-for (global GrType) (global GrRefl))),
     coq.elpi.accumulate _ "derive.eqType.db" (clause _ _ (eqType GrType eqb.axiom)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ _ (reali-done GrType)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "reali:fail") (reali (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "realiR:fail") (realiR (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.trivial.db" (clause _ _ (param1-inhab-db (global GRisT) (global GRisTinhab))).
  main _ :- coq.error "usage: derive.eqbOK.register_axiom T is_T is_T_inhab eqb eqb_correct eqb_refl.".
}}.
Elpi Export derive.eqbOK.register_axiomx.

(*SNIP: sigma_type*)
Definition Sigma := {fmap V -> Tm}.
(*ENDSNIP: sigma_type*)

Definition is_Sigma (x : Sigma) := unit.
Lemma is_Sigma_inhab : forall x, is_Sigma x. Proof. exact (fun x => tt). Qed.
Definition Sigma_eqb (x y : Sigma) := x == y.
Lemma Sigma_eqb_correct : forall x, eqb_correct_on Sigma_eqb x. Proof. by move=>??/eqP. Qed.
Lemma Sigma_eqb_refl : forall x, eqb_refl_on Sigma_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
HB.instance Definition _ : hasDecEq Sigma := Equality.copy Sigma _.

Definition sigT := {fmap P -> S}.

Notation fvS := {fset V}.

Definition is_sigT (x : sigT) := unit.
Lemma is_sigT_inhab : forall x, is_sigT x. Proof. exact (fun x => tt). Qed.
Definition sigT_eqb (x y : sigT) := x == y.
Lemma sigT_eqb_correct : forall x, eqb_correct_on sigT_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigT_eqb_refl : forall x, eqb_refl_on sigT_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigT is_sigT is_sigT_inhab sigT_eqb sigT_eqb_correct sigT_eqb_refl.
HB.instance Definition _ : hasDecEq sigT := Equality.copy sigT _.

(*SNIP: program_type*)
Record program := { rules : seq R; sig :> sigT }.
(*ENDSNIP: program_type*)
derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

(*SNIP: unif_type*)
Record Unif := mk_Unif {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : fvS -> Tm -> Tm -> Sigma -> option Sigma;
}.  
(*ENDSNIP: unif_type*)

Fixpoint get_tm_hd tm :=
  match tm with
  | Tm_App f a => get_tm_hd f
  | Tm_P K => inl K
  | Tm_V V => inr V
  end.

Module test.
  Local Notation p := (Tm_P (IP 1)).
  Local Notation one := (Tm_P (IP 2)).
  Notation two := (Tm_P (IP 3)).
  Local Notation int := Exp.

  (* t is the atom `p 1 2` *)
  Local Definition t := (Tm_App (Tm_App p one) two).
  (* ty is the type of p := pred p int -> int *)
  Local Definition ty := arr input (b Exp) (arr output (b Exp) (b (d Pred))).

  Local Goal get_tm_hd    t = inl (IP 1). by []. Qed. 
End test.

Open Scope fset_scope.

Fixpoint vars_tm t : fvS :=
  match t with
  | Tm_P _ => fset0
  | Tm_V v => fset1 v
  | Tm_App l r => vars_tm l `|` vars_tm r
  end.

Definition vars_atom A : fvS :=
  match A with cut => fset0 | call c => vars_tm c end.

Definition varsU (l: seq fvS) :=
  foldr (fun a e => a `|` e) fset0 l.

Definition vars_atoms L := varsU (map vars_atom L).

Definition varsU_rprem r : fvS := vars_atoms r.(premises).
Definition varsU_rhead (r: R) : fvS := vars_tm r.(head).
Definition varsU_rule r : fvS := varsU_rhead r `|` varsU_rprem r.

Definition fresh  (fv : fvS) : nat := (\max_(i <- fv) let: (IV n) := i in n ).+1.
Definition freshP (fv : fvS) : IV (fresh fv) \in fv = false.
Proof.
  rewrite/fresh; case: in_fsetP => // -[[x] xP] /= []/eq_leq.
  by rewrite (big_fsetD1 _ xP) /= ltnNge => /negbTE<-; rewrite leq_maxl.
Qed.

Fixpoint fresh_tm (n: nat)  (m:{fmap V -> V}) t : nat * {fmap V -> V} :=
  match t with
  | Tm_P _ => (n,m)
  | Tm_V v =>
       if v \in domf m then (n,m)
       else (n.+1, m.[v <- IV n])
  | Tm_App l r => let '(n, m) := fresh_tm n m l in fresh_tm n m r
  end.


Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => odflt tm (s.[?V])
  | Tm_P _ => tm
  | Tm_App h ag => Tm_App (deref s h) (deref s ag)
  end.

Lemma deref_App s f a: deref s (Tm_App f a) = Tm_App (deref s f) (deref s a).
Proof. by []. Qed.

Lemma deref_empty t: deref fmap0 t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.

Definition codom_vars (s:Sigma) := 
  varsU (map vars_tm (codom s)).

Lemma varUP (v:V) (s: seq fvS):
  reflect (exists x : {fset V}, x \in s /\ v \in x) (v \in varsU s).
Proof.
  move=> /=; case vs: (_ \in _); constructor.
    elim: s v vs => //= x xs IH v; rewrite in_fsetU => /orP[] H.
      by exists x; rewrite in_cons eqxx//.
    have:= IH _ H => -[e [H1 H2]].
    by exists e; rewrite in_cons H1 orbT.
  move: vs; apply/contraFnot => -[+ []].
  elim: s v => //= x xs IH v vs.
  rewrite in_cons in_fsetU => /orP[/eqP?|]; subst; first by move => ->.
  by move=> H1 H2; rewrite (IH v vs)//orbT.
Qed.

Lemma codom_vars_sub_vt v s (vs: v \in domf s): vars_tm s.[vs] `<=` codom_vars s.
Proof.
  rewrite/codom_vars.
  apply/fsubsetP => /=v' H.
  apply/varUP; exists (vars_tm s.[vs]); split => //.
  by apply/map_f/codomP; eexists.
Qed.

Lemma codom_vars_sub s k: codom_vars s.[\ k] `<=` codom_vars s.
Proof.
  rewrite{1}/codom_vars.
  apply/fsubsetP => x /varUP[y [yP xP]].
  move: yP => /mapP[t ts]?; subst.
  suffices: exists k (H: k \in domf s), s.[H] = t.
    move=> [z[Hz ?]]; subst; by apply/fsubsetP/xP/codom_vars_sub_vt.
  have {ts} [[y yP] H] := codomP ts; subst.
  have ys : y \in domf s by move: yP {xP}; rewrite domf_rem inE => /andP[].
  exists y, ys.
  suffices [->//] : Some s.[ys] = Some (s.[\ k] [` yP]).
  rewrite -!in_fnd !FmapE.fmapE !inE; move: yP {xP}; rewrite domf_rem !inE.
  by move=> /andP[yk ts]; rewrite in_fnd yk ts.
Qed.

Definition idempotent (s: Sigma) := [disjoint domf s & codom_vars s].

Lemma add_some T (x z: T): Some x = Some z -> x = z. by move=> []. Qed.

Lemma codom_vars_cat s e:
  codom_vars (s + e) = codom_vars s.[\ domf e] `|` codom_vars e.
Proof.
  apply/fsetP => x; rewrite inE.
  case: (boolP (_ \in _)).
    move=> xse; apply/esym; move: xse.
    move=> /varUP[y[/mapP[t + ?] xy]]; subst.
    move=> /codomP[[q /[dup]]].
    rewrite {1}domf_cat inE.
    case: (boolP (_ \in domf e)) => qe; rewrite (orbT,orbF).
      move=> _ qse ?; subst.
      apply/orP; right; apply/varUP; exists (vars_tm ((s + e) [` qse])); split => //.
      apply/mapP; eexists => //; apply/codomP; exists [`qe].
      by apply/add_some; rewrite-in_fnd fnd_cat qe in_fnd.
    move=> qs qse ?; subst.
    apply/orP; left; apply/varUP; exists (vars_tm ((s + e) [` qse])); split => //.
    apply/mapP; eexists => //.
    apply/codomP.
    have qsde: q \in domf s.[\domf e] by rewrite domf_rem inE qs qe.
    by exists [`qsde]; apply/add_some; rewrite-!in_fnd fnd_cat fnd_rem (negbTE qe) in_fnd.
  move=> xsk; apply/esym; move: xsk; apply/contraNF.
  move=> /orP[/varUP[fv[/mapP[t ts ? xf]]]|xv]; subst; apply/varUP.
    exists (vars_tm t); split => //.
    apply/mapP; eexists => //; apply/codomP.
    have {ts} [[z zP ?]] := codomP ts; subst.
    move: zP (zP) xf; rewrite {1}domf_rem inE => /andP[zk zs] zP xf.
    have zks: z \in domf (s + e) by rewrite domf_cat inE zs.
    by exists [`zks]; apply/add_some; rewrite -!in_fnd fnd_rem fnd_cat in_fnd (negbTE zk).
  move/varUP: xv => [v[/mapP[t /codomP[[y yP] ?] ?]] xv]; subst.
  eexists (vars_tm e.[yP]); split => //.
  apply/mapP; eexists => //; apply/codomP.
  have ksk: y \in domf (s + e) by rewrite domf_cat !inE yP orbT.
  by exists [`ksk]; apply/add_some; rewrite -!in_fnd fnd_cat yP.
Qed.

Lemma codom0_set (T:choiceType) (K:Type) (v:T) (s:K): codom fmap0.[v <- s] = [::s].
Proof. by rewrite/= codomE/= fsetU0 enum_fset1/= ffunE//=eqxx. Qed.

Lemma codom_vars_set s k v:
  codom_vars s.[k <- v] = codom_vars s.[~k] `|` vars_tm v.
Proof.
  have:= codom_vars_cat s [fmap].[k <- v].
  rewrite -setf_catr catf0 =>->.
  rewrite dom_setf fsetU0; f_equal.
  by rewrite/codom_vars codom0_set//= fsetU0.
Qed.

Lemma idempotent_set s k v:
  idempotent s.[k <- v] = 
    [&& idempotent s.[~k], (k \notin vars_tm v), (k \notin codom_vars s.[~k]) &
      fdisjoint (domf s) (vars_tm v)].
Proof.
  rewrite /idempotent dom_setf fdisjointUX fdisjoint1X !codom_vars_set.
  rewrite !fdisjointXU; rewrite !inE; case: (boolP (_ \in _)); rewrite ?(andbF,andbT)// => ks.
  rewrite domf_rem orFb; case: (boolP (_ \in _)); rewrite ?(andbF,andbT)// => ksf.
  rewrite andTb.
  case (boolP (fdisjoint (domf s) (vars_tm v))); rewrite !(andbT,andbF)// => D.
  case F: (fdisjoint (domf s)); apply/esym.
    by apply/fdisjointWl/F/fsubD1set.
  move: F; apply/contraFF => H1.
  apply/fsetDidPl/fsetP => x.
  move/fsetDidPl: H1 => /fsetP/(_ x); rewrite !inE.
  case: (boolP (_ \in _)) => //=xsk; case: eqP => //= ?; subst.
  by rewrite xsk in ks.
Qed.

Lemma idempotent_rem s k: idempotent s -> idempotent s.[\ k].
Proof.
  move=> H; apply/fdisjointWr/fdisjointWl/H.
    by rewrite codom_vars_sub.
  by rewrite domf_rem; apply/fsubsetP => x; rewrite inE => /andP[_ ->].
Qed.

Lemma empty_rem {T:choiceType} K k: (fmap0 : {fmap T -> K}).[~k] = (fmap0 : {fmap T -> K}).
Proof. by apply/fmapP => p;rewrite fnd_rem1 not_fnd//if_same. Qed.

Lemma idempotent_0: idempotent fmap0.
Proof. by rewrite/idempotent fdisjoint0X. Qed.

Lemma codom0 (T:choiceType) K: codom (fmap0 : {fmap T -> K}) = [::].
Proof. by rewrite /fmap0 codomE/= enum_fset0. Qed.

Lemma codom_vars0: codom_vars fmap0 = fset0.
Proof. by rewrite/codom_vars codom0. Qed.

Goal ~ (idempotent [fmap].[IV 0 <- Tm_V (IV 0)]).
Proof. by rewrite idempotent_set empty_rem idempotent_0 codom_vars0 fdisjoint0X/= !inE. Qed.

Goal ~ (idempotent [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)]).
Proof. by rewrite idempotent_set !inE remf1_id ?inE// codom_vars_set !inE/= eqxx orbT/= andbF. Qed.

Goal ~ (idempotent [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)].[IV 2 <- Tm_P (IP 1)]).
Proof.
  rewrite idempotent_set remf1_id?inE// idempotent_set inE.
  by rewrite remf1_id?inE//= fdisjointX0 andbT codom_vars_set !inE/= eqxx orbT/= andbF.
Qed.

Goal (idempotent [fmap].[IV 0 <- Tm_V (IV 1)]).
Proof.
  by rewrite idempotent_set empty_rem idempotent_0 codom_vars0 !inE fdisjoint0X.
Qed.

Definition idempotent_ren (m: {fmap V -> V}) := 
  (* idempotent [fmap s => Tm_V m.[valP s]]. *)
  [disjoint domf m & codomf m].

Lemma idempotent_ren0: idempotent_ren ctx.fmap0.
Proof. rewrite/idempotent_ren fdisjoint0X//. Qed.

Fixpoint ren (s: {fmap V -> V}) tm :=
  match tm with
  | Tm_V V => Tm_V (odflt V (s.[?V]))
  | Tm_P _ => tm
  | Tm_App h ag => Tm_App (ren s h) (ren s ag)
  end.

Lemma injectiveb0 : injectiveb (fmap0 : {fmap V -> V}).
by apply/injectiveP=> -[].
Qed.

Lemma injectiveb1 (k : choiceType) (T : k) (S : eqType) (w : S) : 
  injectiveb [fmap x : fset1 T => w].
apply/injectiveP=> -[x Hx] [y Hy] _; apply:val_inj => /=.
by move: Hx Hy; rewrite !inE => /eqP -> /eqP ->. 
Qed.

Lemma push T1 T2 T3 (t : T1 * T2) (F : _ -> _ -> T3) : (let: (a, bx) := t in F a bx) = F t.1 t.2.
  by case: t => /=.
Qed.

Definition sum_mt n m t := fresh (IV n |` domf m `|` codomf m `|` vars_tm t).

Definition rename n (m : {fmap V -> V}) t :=
  let: nm := fresh_tm n m t in
  (nm, ren nm.2 t).

Lemma set0IN (T: choiceType) (s: {fset T}): s = fset0 \/ exists k, k \in s.
Proof. have:= fset_0Vmem s => -[->|]; auto => -[x H]; right; exists x; auto. Qed.

Lemma not_in_deref s t:
  [disjoint domf s & vars_tm t] ->
  deref s t = t.
Proof.
  elim: t => //=[v|f Hf a Ha].
    by rewrite fdisjointX1 => H; rewrite not_fnd.
  by rewrite fdisjointXU => /andP[/Hf->/Ha->].
Qed.

Lemma deref_V s v: deref s (Tm_V v) = odflt (Tm_V v) (s.[?v]).
Proof. by []. Qed.

Lemma deref2' s e t:
  idempotent (s+e) -> deref (s+e) (deref e t) = deref (s+e) t.
Proof.
  move=> A; elim: t => //[v|/=f->a->//].
  rewrite !deref_V fnd_cat.
  case: fndP => ve.
    rewrite/= not_in_deref//; apply/fdisjointWr/A.
    apply/fsubset_trans.
      apply/codom_vars_sub_vt.
    by rewrite codom_vars_cat fsubsetUr.
  by rewrite !deref_V fnd_cat (negbTE ve).
Qed.

Lemma catf2 (K:choiceType) V (s: {fmap K -> V}): s + s = s.
Proof. by apply/fmapP => x; rewrite fnd_cat if_same. Qed.

Lemma deref2 s t:
  (idempotent s) -> deref s (deref s t) = deref s t.
Proof. by have:= @deref2' s s t; rewrite catf2. Qed.

Lemma vars_tm_deref_sub s t:
  vars_tm (deref s t) `<=` codom_vars s `|` vars_tm t.
Proof.
  apply/fsubsetP => x; rewrite inE.
  elim: t => //[v|f Hf a Ha]/=.
    case: fndP => /=vs; rewrite !inE; last by move=> ->; rewrite orbT.
    move=> H; apply/orP; left.
    by apply/fsubsetP/H/codom_vars_sub_vt.
  by rewrite !inE => /orP[/Hf|/Ha]/orP[]->; rewrite //!orbT.
Qed.

Lemma deref_rem s t s1:
  fdisjoint s (vars_tm t) ->
  deref s1.[\ s] t = deref s1 t.
Proof.
  elim: t => //[v|f Hf a Ha/=].
    by rewrite fdisjointX1 !deref_V fnd_rem => /negbTE->//.
  rewrite fdisjointXU => /andP[sf sa].
  by rewrite Ha//Hf.
Qed.

Lemma deref_codom k s t:
  k \notin vars_tm t ->
  k \notin codom_vars s -> k \notin vars_tm (deref s t).
Proof.
  have:= vars_tm_deref_sub s t => /fsubsetP/(_ k); rewrite !inE.
  case: (boolP (_ \in _)) => // H /(_ isT)/orP[]->//.
Qed.

Lemma idempotent_deref_disjoint s t:
  idempotent s -> [disjoint domf s & vars_tm (deref s t)].
Proof.
  move=> A; elim: t => //=; only 1: by rewrite fdisjointX0.
    move=> v; case: fndP => //=vs.
      by apply/fdisjointWr/A/codom_vars_sub_vt.
    by rewrite fdisjointX1.
  by move=> f Hf a Ha; rewrite fdisjointXU Hf.
Qed.

Lemma ren_app m l r : ren m (Tm_App l r) = Tm_App (ren m l) (ren m r).
Proof. by []. Qed.

Lemma deref_P s v: deref s (Tm_P v) = Tm_P v. by []. Qed.

Lemma ren_P b p: ren b (Tm_P p) = Tm_P p. by []. Qed.

Lemma ren_V b v: ren b (Tm_V v) = Tm_V (odflt v b.[?v]). by []. Qed.

Definition fresh_atom n m a :=
  match a with
  | cut => (n, m, cut)
  | call t => let: (n, m, t) := rename n m t in (n, m, call t)
  end.

Definition fresh_atoms fv m a :=
  foldr (fun x '(fv,m,xs) => let: (fv,m, x) := fresh_atom fv m x in (fv,m,x::xs)) (fv,m,[::]) a.

Definition fresh_rule fv r :=
  let: (fv, m, head) := rename fv fmap0 r.(head) in
  let: (fv, m, premises) := fresh_atoms fv m r.(premises) in
  (fv, mkR head premises ).

Definition vars_sigma (s: Sigma) := domf s `|` codom_vars s.

Lemma vars_sigma0: vars_sigma fmap0 = fset0.
Proof. by rewrite/vars_sigma domf0 codom_vars0 fsetU0. Qed.

Definition fresh_rules fv rules :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_rule fv x in (fv,x::xs)) (fv,[::]) rules.

Fixpoint get_input_vars (sP:sigT) t : {fset V} * option S :=
  match t with
  | Tm_P p => (fset0, sP.[?p])
  | Tm_V _  => (fset0, None)
  | Tm_App f a =>
    let: (fv, ty) := get_input_vars sP f in
    match ty with
    | Some (arr m _ r) => (fv `|` if m == input then vars_tm a else fset0, Some r)
    | _ => (fv, None)
    end
  end.

(* Unification between query and rule-head *)
(* fv is the set of "frozen" variables appearing in input position in the query
   the are not touched when unified with the matching procedure (input mode)

   An example (using montanari algorithm) that can assign input variables
   is the following:
    let f be a predicate with 3 inputs
    query := f X 3
    rule  := f W W
    =================
    frozen variables X
    unification problems : W = X, W = 3
    step 1: X = W ===> W -> X, the list of unif problems becoes : X = 3 
    step 2: since X is frozen, this unification fails
*)
Fixpoint H u (sP:sigT) fv (q : Tm) (h: Tm) s : option (S * Sigma) :=
  match q,h with
  | Tm_P p, Tm_P p' => if p == p' then omap (fun x => (x, s)) sP.[?p] else None
  | Tm_App f a, Tm_App f' a' =>
    if H u sP fv f f' s is Some (arr m _ r, s) then
      let f := if m == input then u.(matching) fv else u.(unify) in
      omap (fun x => (r, x)) (f a' a s)
    else None
  | _, _ => None
  end.

Fixpoint select u (sP:sigT) (q: Tm) (rules: list R) sigma : seq (Sigma * seq Atom) :=
  match rules with
  | [::] => [::]
  | rule :: rules =>
    match H u sP (get_input_vars sP q).1 q rule.(head) sigma with
    | None => select u sP q rules sigma
    | Some (_, sigma1) => (sigma1, rule.(premises)) :: select u sP q rules sigma
    end
  end.

Section s.
Variable u : Unif.

Definition v_prog pr := varsU (map varsU_rule pr).

Lemma v_prog_cons x xs: v_prog (x::xs) = varsU_rhead x `|` varsU_rprem x `|` v_prog xs.
Proof. by []. Qed.

Definition max_sigmas n (s: seq (Sigma * seq Atom)) : nat :=
  foldr (fun e n => maxn n (maxn (fresh (vars_atoms e.2)) (fresh (vars_sigma e.1)))) n s.

(*SNIP: bc_type*)
Definition bc : program -> nat -> Tm -> Sigma -> nat * seq (Sigma * seq Atom) :=
(*ENDSNIP: bc_type*)
  fun pr fv (query:Tm) s =>
  if ~~ idempotent s then (fv, [::])
  else
  let query := deref s query in
  let: (fv, rules) := fresh_rules (fresh (IV fv |` vars_sigma s `|` vars_tm query `|` v_prog pr.(rules))) (pr.(rules)) in
  let: rules := select u pr.(sig) query rules s in 
  (max_sigmas fv rules, rules).
End s.

Fixpoint is_det_sig (sig:S) : bool :=
  match sig with
  | b (d Func) => true
  | b (d Pred) => false
  | b Exp => false
  | arr _ _ s => is_det_sig s
  end.

Definition has_cut_seq:= (has (fun x => cut == x)).

Definition tm_is_det (sP: sigT) (t : Tm) : bool :=
  match get_tm_hd t with
  | inl P => if sP.[?P] is Some s then is_det_sig s else false
  | _ => false
  end.

Fixpoint all_but_last {T : Type} P (l : seq T) :=
  match l with 
  | [::] | (_ :: [::]) => true
  | x :: xs => P x && all_but_last P xs
  end.

Lemma tm_is_det_app sP f1 a1:
  tm_is_det sP (Tm_App f1 a1) = tm_is_det sP f1.
Proof. by []. Qed.

Lemma get_tm_hd_app t t0:
  (get_tm_hd (Tm_App t t0)) = (get_tm_hd t).
Proof. by []. Qed.

Lemma callabe_some_deref s1 c p:
  (get_tm_hd c) = inl p -> get_tm_hd (deref s1 c) = inl p.
Proof. elim: c p => //=[x p [<-]|f Hf a Ha p]; rewrite (deref_P,deref_App)//=; auto. Qed.

Lemma is_det_der s s1 c : tm_is_det s c ->
  exists q (kP: q \in domf s), 
    get_tm_hd (deref s1 c) = inl q /\ is_det_sig s.[kP].
Proof.
  rewrite/tm_is_det/=.
  case X: get_tm_hd => //=[p].
  case: fndP => //pP.
  exists p, pP; split => //.
  by apply: callabe_some_deref; rewrite X.
Qed.

Definition ground t := vars_tm t == fset0.

Lemma ground_V v: ground (Tm_V v) = false.
Proof. by rewrite/ground/=; apply:contraFF erefl => /eqP/fsetP /(_ v); rewrite !inE eqxx. Qed.

Lemma ground_app f a: ground (Tm_App f a) = ground f && ground a.
Proof. by rewrite /ground/= fsetU_eq0. Qed.

Lemma idempotent_set_D k t: ground t -> idempotent fmap0.[k <- t].
Proof.
  rewrite idempotent_set empty_rem fdisjoint0X idempotent_0 codom_vars0.
  by rewrite /ground => /eqP->//.
Qed.

Lemma ground_deref s t: ground t -> deref s t = t.
Proof.
  elim: t => //[v|f Hf a Ha].
    by rewrite ground_V.
  by rewrite ground_app => /=/andP[/Hf->/Ha->].
Qed.

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Fixpoint term_arg t :=
  match t with
  | Tm_App t _ => (term_arg t).+1
  | _ => 0
  end.

Fixpoint eat_ty n sig :=
  match n with
  | 0 => Some sig
  | n.+1 => match sig with arr _ _ r => eat_ty n r | _ => None end
  end.

Lemma eat_ty_arr n md tf ta m tl tr:
  eat_ty n (arr md tf ta) = Some (arr m tl tr) -> eat_ty n ta = Some tr.
Proof.
  elim: n md tf ta m tl tr => [|n IH] md tf ta m tl tr/=; first by move=>[_ _ <-].
  by case: ta => [|>]; [case n|apply: IH].
Qed.

Lemma HP u sP fv t1 t2 s r: H u sP fv t1 t2 s = Some r -> 
  [/\ get_tm_hd t1 = get_tm_hd t2, term_arg t1 = term_arg t2 &
    exists p, exists2 pP : p \in sP, get_tm_hd t1 = inl p & eat_ty (term_arg t1) sP.[pP] = Some r.1]
  .
Proof.
  elim: t1 t2 fv s r => //=[p|f Hf a Ha] [p'|v|f' a']//= fv s r.
    case: eqP => //<-; case: fndP => //=pP[<-]; split => //.
    by exists p, pP.
  case H: H => //[[[|m tl tr] s']]//=.
  case : (_ s') => //= sz [?]; subst => /=.
  have /=[Hx Hy [p [pP H1 H2]]] := Hf _ _ _ _ H.
  split => //; first by rewrite Hy.
  eexists p, pP => //=.
  move: H2; case: sP.[pP] => //=; first by case: term_arg.
  by clear => md tf ta; apply: eat_ty_arr.
Qed.

Lemma selectP u sP t1 s rs x xs: select u sP t1 rs s = (x::xs) -> 
  exists2 p, p \in sP & get_tm_hd t1 = inl p.
Proof.
  elim: rs x xs => //=r rs IH x xs.
  case H: H => [[ty s']|]//; last by apply: IH.
  case S: select => [|y ys][??]; subst; last apply: IH S.
  have [_ _ [p[pP {}H _]]] := HP H.
  by exists p => //.
Qed.

Lemma H_same_ty u sP fv1 fv2 f f1 f2 s1 s2 r1 r2:
  H u sP fv1 f f1 s1 = Some r1 ->
  H u sP fv2 f f2 s2 = Some r2 ->
  r1.1 = r2.1.
Proof.
  move=> H1 H2.
  have[Ha1 Hb1 [z1[P1]]]:= HP H1.
  have[Ha2 Hb2 [z2[P2]]]:= HP H2.
  move=> -> + [?]; subst.
  by rewrite (bool_irrelevance P1 P2) => ->[].
Qed.

Lemma select_cons u sP q r rs s:
  select u sP q (r :: rs) s =
    match lang.H u sP (get_input_vars sP q).1 q (head r) s with
    | Some (_, s1) => (s1, premises r) :: select u sP q rs s
    | None => select u sP q rs s
    end.
Proof. by []. Qed.
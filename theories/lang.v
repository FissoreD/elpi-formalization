From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.

Lemma orPT b1 b2 : (b1 || b2) -> (b1 + b2)%type.
by case: b1; case: b2; constructor.
Qed.

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
Inductive P := IP of nat. Inductive D := ID of nat. Inductive V := IV of nat.
(*ENDSNIP: base_type*)

derive P.
HB.instance Definition _ := hasDecEq.Build P P_eqb_OK.
Definition Kp_of_nat x := IP x.
Definition nat_of_Kp x := match x with IP x => x end.
Lemma Kp_is_nat : cancel nat_of_Kp Kp_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy P (can_type Kp_is_nat).

derive D.
HB.instance Definition _ := hasDecEq.Build D D_eqb_OK.

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
  | Tm_P of P     | Tm_D    of D
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

Definition empty : Sigma := empty.

Definition is_Sigma (x : Sigma) := unit.
Lemma is_Sigma_inhab : forall x, is_Sigma x. Proof. exact (fun x => tt). Qed.
Definition Sigma_eqb (x y : Sigma) := x == y.
Lemma Sigma_eqb_correct : forall x, eqb_correct_on Sigma_eqb x. Proof. by move=>??/eqP. Qed.
Lemma Sigma_eqb_refl : forall x, eqb_refl_on Sigma_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
HB.instance Definition _ : hasDecEq Sigma := Equality.copy Sigma _.

Definition sigT := {fmap P -> S}.
Definition empty_sig : sigT := [fmap].

Notation fvS := {fset V}.

Definition is_sigT (x : sigT) := unit.
Lemma is_sigT_inhab : forall x, is_sigT x. Proof. exact (fun x => tt). Qed.
Definition sigT_eqb (x y : sigT) := x == y.
Lemma sigT_eqb_correct : forall x, eqb_correct_on sigT_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigT_eqb_refl : forall x, eqb_refl_on sigT_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigT is_sigT is_sigT_inhab sigT_eqb sigT_eqb_correct sigT_eqb_refl.
HB.instance Definition _ : hasDecEq sigT := Equality.copy sigT _.

(*SNIP: program_type*)
Record program := { rules : seq R; sig : sigT }.
(*ENDSNIP: program_type*)
derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

(*SNIP: unif_type*)
Record Unif := mk_Unif {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  
(*ENDSNIP: unif_type*)

Fixpoint flatten_mode m :=
  match m with
  | arr m _ l => m :: flatten_mode l
  | b _ => [::]
  end.

Fixpoint flatten_sig m :=
  match m with
  | arr _ l r => l :: flatten_sig r
  | b _ => [::]
  end.

Fixpoint count_tm_ag t := 
  match t with
  | Tm_App L _ => 1 + count_tm_ag L
  | _ => 0
  end.

Fixpoint flatten_term tm :=
  match tm with
  | Tm_App f a => rcons (flatten_term f) a
  | Tm_P K => [::]
  | Tm_D K => [::]
  | Tm_V V => [::]
  end.

Fixpoint get_tm_hd tm :=
  match tm with
  | Tm_App f a => get_tm_hd f
  | Tm_P K => inl K
  | Tm_D K => inr (inl K)
  | Tm_V V => inr (inr V)
  end.


Module test.
  Notation p := (Tm_P (IP 1)).
  Notation one := (Tm_P (IP 2)).
  Notation two := (Tm_P (IP 3)).
  Notation int := Exp.

  (* t is the atom `p 1 2` *)
  Definition t := (Tm_App (Tm_App p one) two).
  (* ty is the type of p := pred p int -> int *)
  Definition ty := arr input (b Exp) (arr output (b Exp) (b (d Pred))).

  Goal flatten_mode ty = [::input; output]. by []. Qed.
  Goal flatten_term t =  [::one  ; two   ]. by []. Qed.
  Goal get_tm_hd    t = inl (IP 1). by []. Qed. 
End test.

Open Scope fset_scope.

Fixpoint vars_tm t : fvS :=
  match t with
  | Tm_D _ => fset0
  | Tm_P _ => fset0
  | Tm_V v => fset1 v
  | Tm_App l r => vars_tm l `|` vars_tm r
  end.

Fixpoint vars_tmL t : list V :=
  match t with
  | Tm_D _ => [::]
  | Tm_P _ => [::]
  | Tm_V v => [::v]
  | Tm_App l r => vars_tmL l ++ vars_tmL r
  end.

Definition vars_atom A : fvS :=
  match A with cut => fset0 | call c => vars_tm c end.

Definition varsU (l: seq fvS) :=
  foldr (fun a e => a `|` e) fset0 l.

Definition vars_atoms L := varsU (map vars_atom L).

Definition varsU_rprem r : fvS := vars_atoms r.(premises).
Definition varsU_rhead (r: R) : fvS := vars_tm r.(head).
Definition varsU_rule r : fvS := varsU_rhead r `|` varsU_rprem r.

Lemma freshV (fv : fvS) :  exists v : V, v \notin fv.
Proof.
exists (IV (\sum_(i <- fv) let: (IV n) := i in n ).+1)%N.
case: in_fsetP => // -[[x] xP] /= [] /eq_leq.
by rewrite (big_fsetD1 _ xP) /= -ltn_subRL subnn ltn0.
Qed.

Definition fresh  (fv : fvS) : V := xchoose (freshV fv).
Definition freshP (fv : fvS) : (fresh fv) \in fv = false.
Proof. by apply: negbTE (xchooseP (freshV fv)). Qed.

Fixpoint fresh_tm fv m t : {fset V} * {fmap V -> V} :=
  match t with
  | Tm_D _ => (fv, m)
  | Tm_P _ => (fv, m)
  | Tm_V v =>
       if v \in domf m then (fv, m)
       else let v' := fresh (fv `|` codomf m) in (v' |` fv,  m + [fmap v : fset1 v => v'])
  | Tm_App l r => 
      let: (fv, m) := fresh_tm fv m l in 
      let: (fv, m) := fresh_tm fv m r in (fv, m)
  end.

Fixpoint deref1 (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (deref1 s h) (deref1 s ag)
  end.

Fixpoint deref_aux n (s: Sigma) (tm:Tm) :=
  match n with 
  | 0 => tm
  | n.+1 => deref_aux n s (deref1 s tm)
  end.

Definition deref (s:Sigma) (tm:Tm) := deref_aux #|` domf s | s tm.

Lemma deref_aux_App n s f a: 
  deref_aux n s (Tm_App f a) = Tm_App (deref_aux n s f) (deref_aux n s a).
Proof. elim: n f a => //=. Qed.

Lemma deref_App s f a: deref s (Tm_App f a) = Tm_App (deref s f) (deref s a).
Proof. rewrite/deref deref_aux_App//. Qed.

Lemma deref1_empty t: deref1 empty t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.

Lemma deref_aux_empty n t: deref_aux n empty t = t.
Proof. by elim: n t => //= n IH t; rewrite deref1_empty//. Qed.

Lemma deref_empty t: deref empty t = t.
Proof. by []. Qed.

Fixpoint deref_vars n s tm :=
  let tm := deref1 s tm in
  match n with
  | 0 => fset0
  | n.+1 => vars_tm tm `|` (deref_vars n s tm)
  end.

Definition acyclic_sigma (s: Sigma) :=
  [forall x : domf s, val x \notin deref_vars #|` domf s | s (Tm_V (val x))].
  (* [forall x : domf s, val x \notin vars_tm (deref s (Tm_V (val x)))]. *)

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 0)]).
Proof.
  rewrite /acyclic_sigma => /forallP.
  have: IV 0 \in (domf ctx.empty.[IV 0 <- Tm_V (IV 0)]) by rewrite !inE eqxx.
  move=> H /(_ (Sub (IV 0) H)); rewrite /= fsetU0 cardfs1/= !FmapE.fmapE/= !inE//.
Qed.

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)]).
Proof.
  rewrite /acyclic_sigma => /forallP.
  have: IV 0 \in (domf ctx.empty.[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)]) by rewrite !inE eqxx.
  move=> H /(_ (Sub (IV 0) H)); rewrite /= !fsetU0 cardfs2/= !FmapE.fmapE/= !inE !FmapE.fmapE eqxx inE//.
Qed.

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)].[IV 2 <- Tm_D (ID 0)]).
Proof.
  rewrite /acyclic_sigma => /forallP.
  have: IV 0 \in (domf ctx.empty.[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)].[IV 2 <- Tm_D (ID 0)]) by rewrite !inE eqxx.
  move=> H /(_ (Sub (IV 0) H)).
  rewrite /= fsetU0 (cardfsD1 (IV 2))/= 2!inE eqxx add1n/=.
  rewrite in_fnd ?inE//= !ffunE/= !FmapE.fmapE/= !inE/=.
  rewrite fsetU1K//=?inE//!cardfs2/= !FmapE.fmapE/= !inE//=.
Qed.

Goal (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)]).
Proof.
  apply/forallP => -[x xP]/=.
  move: xP; rewrite !inE.
  case: eqP => //->/=.
  rewrite fsetU0 cardfs1/= !FmapE.fmapE/= !inE//.
Qed.

Definition acyclic_ren (m: {fmap V -> V}) := 
  (* acyclic_sigma [fmap s => Tm_V m.[valP s]]. *)
  [disjoint domf m & codomf m].

Lemma acyclic_ren0: acyclic_ren ctx.empty.
Proof. rewrite/acyclic_ren fdisjoint0X//. Qed.

Lemma fresh_Tm_App fv m l r :
  fresh_tm fv m (Tm_App l r) =
    let rl := fresh_tm fv m l in
    fresh_tm rl.1 rl.2 r.
Proof.
by rewrite /= [fresh_tm _ _ l]surjective_pairing [fresh_tm _ _ r]surjective_pairing /=.
Qed.

Fixpoint ren (s: {fmap V -> V}) tm :=
  match tm with
  | Tm_V V => Tm_V (odflt V (lookup V s))
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (ren s h) (ren s ag)
  end.

Lemma push T1 T2 T3 (t : T1 * T2) (F : _ -> _ -> T3) : (let: (a, bx) := t in F a bx) = F t.1 t.2.
  by case: t => /=.
Qed.

Definition rename fv tm m :=
  let: (fv', m) := fresh_tm (vars_tm tm `|` fv) m tm in
  ((fv', m), ren m tm).

Lemma acyclic_sigma0: acyclic_sigma empty.
(* Proof. by rewrite/acyclic_sigma/=; apply/forallP. Qed. *)
Proof. by rewrite/acyclic_sigma; apply/forallP => //=-[]. Qed.

Require Import Lia.

Lemma set0IN (T: choiceType) (s: {fset T}): s = fset0 \/ exists k, k \in s.
Proof. have:= fset_0Vmem s => -[->|]; auto => -[x H]; right; exists x; auto. Qed.

Lemma fset_sub_rem (s: Sigma) k:
  domf s `\ k = domf s.[~ k].
Proof.
  rewrite/=.
  apply/fsetP => x; rewrite !inE/=.
  case: eqP => //=H; subst; first by rewrite andbF.
  by rewrite andbb//.
Qed.

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

Lemma codom_vars_sub v s (vs: v \in domf s): vars_tm s.[vs] `<=` codom_vars s.
Proof.
  rewrite/codom_vars.
  apply/fsubsetP => /=v' H.
  apply/varUP; exists (vars_tm s.[vs]); split => //.
  by apply/map_f/codomP; eexists.
Qed.

Lemma codom_vars_rem s k: codom_vars s.[~k] `<=` codom_vars s.
Proof.
  rewrite{1}/codom_vars.
  apply/fsubsetP => x /varUP[y [yP xP]].
  move: yP => /mapP[t ts]?; subst.
  suffices: exists k (H: k \in domf s), s.[H] = t.
    move=> [z[Hz ?]]; subst; by apply/fsubsetP/xP/codom_vars_sub.
  have {ts} [[y yP] H] := codomP ts; subst.
  have ys : y \in domf s by move: yP {xP}; rewrite -fset_sub_rem !inE => /andP[].
  exists y, ys.
  suffices [->//] : Some s.[ys] = Some (s.[~ k] [` yP]).
  rewrite -!in_fnd !FmapE.fmapE !inE; move: yP {xP}; rewrite -fset_sub_rem !inE.
  by case: eqP => //= _ ->.
Qed.


Fixpoint relT k t1 t2 :=
  match t1 with
  | Tm_V v => (v == k) || (t1 == t2)
  | Tm_D _ | Tm_P _ => (t1 == t2)
  | Tm_App f a =>
    match t2 with
    | Tm_App f' a' => relT k f f' && relT k a a'
    | _ => false
    end
  end.

Lemma relT_refl k: reflexive (relT k).
Proof. by elim => //=[v|a -> f ->]//; rewrite eqxx orbT. Qed.

Lemma relT_deref s t1 t2 k:
  relT k t1 t2 -> relT k (deref1 s.[~ k] t1) (deref1 s.[~ k] t2).
Proof.
  elim: t1 t2 => [p|d|v|f Hf a Ha] t2; only 1, 2: by move=> /=/eqP<-.
    rewrite {1}[relT _ _ _]/= => /orP[/eqP ->{v}|].
      by rewrite {1}/deref1 fnd_rem1 !eqxx/= eqxx.
    by move=> /eqP<-{t2}; rewrite relT_refl.
  case: t2 => // f' a'/= /andP[rf rt].
  by rewrite Ha//Hf.
Qed.

Lemma relT_deref_rem s t1 t2 k:
  relT k t1 t2 -> relT k (deref1 s.[~ k] t1) (deref1 s t2).
Proof.
  elim: t1 t2 => [p|d|v|f Hf a Ha] t2; only 1, 2: by move=> /=/eqP<-.
    rewrite {1}[relT _ _ _]/= => /orP[/eqP ->{v}|].
      by rewrite {1}/deref1 fnd_rem1 !eqxx/= eqxx.
    move=> /eqP<-{t2}; rewrite/deref1 !fnd_rem1; case: eqP => //=.
      by move=> ->; rewrite eqxx.
    by rewrite relT_refl.
  case: t2 => // f' a'/= /andP[rf rt].
  by rewrite Ha//Hf.
Qed.

Lemma deref1_vars_in_rem y k s t1 t2: y != k -> relT k t1 t2 -> 
  y \in vars_tm (deref1 s.[~ k] t1) -> y \in vars_tm (deref1 s t2).
Proof. 
  move=> /eqP H; elim: t1 t2 => //[v|f Hf a Ha] t2.
    rewrite {1}/deref1 fnd_rem1; case: eqP => vk; subst => /=. 
      by rewrite /= inE => _ /eqP.
    by move=> /orP[|]/eqP// <-/=.
  case: t2 => //= f' a' /andP[R1 R2]; rewrite !inE.
  by move => /orP[/Hf->//|/Ha]{}Ha; rewrite (Ha _ R2) orbT.
Qed.

Lemma deref_vars_deref1_in_rem n y k s t1 t2: y != k -> relT k t1 t2 ->
  y \in deref_vars n s.[~k] t1 -> y \in deref_vars n s.[~k] t2.
Proof.
  move=> yk; elim: n s t1 t2 => //= n IH s t1 t2 R; rewrite !inE => /orP[H|H].
    by rewrite (deref1_vars_in_rem yk R)// remove2.
  rewrite (IH _ _ _ _ H) ?orbT// relT_deref//.
Qed.

Lemma deref_vars_in_rem n y k s t: y != k ->
  y \in deref_vars n s.[~ k] t -> y \in deref_vars n s t.
Proof.
  move=> yk; elim: n t => //= n IH t; rewrite !inE => /orP[H|H].
    by rewrite (deref1_vars_in_rem yk (relT_refl _ _) H).
  rewrite IH//?orbT//.
  by apply/deref_vars_deref1_in_rem/H/relT_deref_rem/relT_refl.
Qed.

Lemma deref_vars_add_sub n k s t: deref_vars n s t `<=` deref_vars (n + k) s t.
Proof. by elim: n k s t => //= n IH k s t; rewrite fsetUSS//. Qed.

Lemma acyclic_sigma_rem s k: acyclic_sigma s -> acyclic_sigma s.[~ k].
Proof.
  rewrite/acyclic_sigma => /forallP H; apply/forallP => -[y ysk].
  rewrite [val _]/=.
  move: ysk; rewrite -fset_sub_rem !inE => /andP[yk ys].
  have {H} := H (Sub y ys).
  rewrite [val _]/=; apply/contra => H.
  have {}H := deref_vars_in_rem yk H.
  rewrite (cardfsD1 k); rewrite addnC.
  apply/fsubsetP/H/deref_vars_add_sub.
Qed.

Lemma deref1_singl k s t t':
  s = ctx.empty.[k <- t'] -> vars_tm t `<=` vars_tm t' ->
  k \in vars_tm t -> k \in vars_tm (deref1 s t).
Proof.
  move=> ->; elim: t t' => [p|d|v|f Hf a Ha] t'//; try by rewrite/= fsubset0 => /eqP->.
    rewrite/deref1 fnd_set not_fnd//; case: eqP => //= H.
    by rewrite fsub1set !inE => + /eqP->.
  rewrite/= !inE fsubUset => /andP[H1 H2] /orP[] H; [rewrite Hf|rewrite Ha] => //.
  by rewrite orbT.
Qed.

(* Lemma varsU_subset_rem (s:Sigma) k:
  varsU (map vars_tm (codom s)) `<=` 
    varsU (map vars_tm (codom s.[~ k])).
Proof.
  rewrite/codom.
  Search codom *)

Lemma codom0: codom empty = [::].
Proof. by rewrite /empty codomE/= enum_fset0. Qed.

Lemma codom_vars0: codom_vars empty = fset0.
Proof. by rewrite/codom_vars codom0. Qed.

(* Lemma wip cand (s:Sigma) (cs : cand \in s):
  cand \notin deref_vars #|` domf s| s s.[cs] -> cand \notin codom_vars s.
Proof.
  apply:contra.
  remember #|` domf s| as n eqn:Hn; elim: n s cs Hn => //[|n IH] s cs Hn.
    by have /fmap_nil H := cardfs0_eq (esym Hn); rewrite {1}H/= codom_vars0.
  have [] := set0IN (domf s).
    by move : Hn => + /fmap_nil X; rewrite {1}X cardfs0.
  move=> /=[k ks]; rewrite inE => H.
    
  Search (~~ (_ || _)).
  rewrite (cardfsD1 k (domf s)) ks add1n in Hn; case: Hn.
  rewrite fset_sub_rem => Hn.
  move:
  have := IH (s.[~ k]) _ Hn. *)

Lemma deref_refl_not_in (s:Sigma) t:
  [forall k : domf s, val k \notin vars_tm t] ->
  deref1 s t = t.
Proof.
  elim: t s => //[v|f Hf a Ha]//= s.
    by case: fndP => //=ks H; have:= forallP H (Sub v ks); rewrite /= inE eqxx.
  move=> H; rewrite !(Hf,Ha)//; apply/forallP => -[k kP]/=;
  by have:= forallP H (Sub k kP); rewrite !inE/=; apply:contra => ->//; rewrite orbT.
Qed.

(* returns only the mapping in s pointing to terms containing v *)
(* for example, in {x : t1, y: t2, z : t3}, if w in t2 and t3, then
   filter_in returns {x: t1, y: t2} *)
Definition filter_in (s:Sigma) v : Sigma :=
  filterf s (fun x => if s.[?x] is Some t then v \in vars_tm t else false).

Lemma filter_in0 v: filter_in fmap0 v = fmap0.
Proof. by apply/fmapP => k; rewrite !not_fnd//; rewrite !inE//. Qed.

Lemma filter_in_setN v s k t:
  v \notin vars_tm t -> k \notin s ->
  filter_in s.[k<-t] v = filter_in s v.
Proof.
  move=> H ks; apply/fmapP => x; rewrite !fnd_filterf fnd_set.
  by case: eqP => [->{x}|]//; rewrite not_fnd// (negbTE H).
Qed.

Lemma filter_in_setT v s k t:
  v \in vars_tm t -> k \notin s ->
  filter_in s.[k<-t] v = (filter_in s v).[k<-t].
Proof.
  move=> H ks; apply/fmapP => x; rewrite !fnd_filterf fnd_set.
  by rewrite fnd_set fnd_filterf; case: eqP; first by rewrite H.
Qed.

(* returns a variable v in s which is not in the codomain of s *)
Fixpoint get_father v n (s : Sigma) :=
  let f := filter_in s v in
  match n with
  | 0 => v
  | n.+1 => 
    if pick (domf f) is Some v then get_father (val v) n s
    else v
  end.

Lemma get_father1 v n s: get_father v n.+1 s =  
    if pick (domf (filter_in s v)) is Some v then get_father (val v) n s
    else v. by []. Qed.

Lemma get_father0n v s: get_father v 0 s = v. by []. Qed.

Goal let s := fmap0.[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 2)].[IV 2 <- Tm_D (ID 0)] in 
  get_father (IV 2) #|`domf s| s = IV 0.
Proof.
  rewrite/= (cardfsD1 (IV 2)) !inE add1n fsetU1K?inE// fsetU0 cardfs2.
  rewrite !get_father1 filter_in_setN ?inE//.
  rewrite filter_in_setT ?inE// filter_in_setN?inE//.
  rewrite filter_in0 dom_setf fsetU0.
  rewrite/pick enum_fset1 [ohead _]/=.
  cbn iota.
  rewrite [val _]/= get_father1 filter_in_setN?inE//.
  rewrite filter_in_setN?inE// filter_in_setT?inE// filter_in0 dom_setf fsetU0.
  rewrite/pick enum_fset1 [ohead _]/=.
  cbn iota.
  rewrite [val _]/= get_father1 filter_in_setN?inE//.
  rewrite filter_in_setN?inE// filter_in_setN?inE// filter_in0.
  by rewrite/pick enum_fset0/=.
Qed.

Lemma filter_in_domf v s k: v \in domf (filter_in s k) -> v \in domf s.
Proof. by rewrite/filter_in/= !inE; case: fndP. Qed.

Lemma get_father_domf k n s:  k \in domf s -> get_father k n s \in domf s.
Proof. 
  elim: n k => //n IH k ks; rewrite get_father1.
  by case P: pick => [[v' v'P]|//]; apply/IH/filter_in_domf/v'P.
Qed.

Lemma get_father_codomf k n s:  
  acyclic_sigma s -> #|` domf s | = n ->
  k \in domf s -> get_father k n s \notin codom_vars s.
Proof.
  elim: n k s => //[|n IH] k s A; first by move=> /cardfs0_eq/fmap_nil->//.
  move=> H1 H2.
  rewrite get_father1.
  case: pickP; last first.
    move=> H; apply/varUP => -[x[xc kx]].
    move : xc => /mapP/=[t xc ?]; subst.
    move/codomP: xc => [[v vP]]?; subst.
    have Z: v \in filter_in s k by rewrite/filter_in !inE in_fnd vP.
    by move: H => /(_ [`Z]).
  move=> [x xF] _/=.
  move: H1; rewrite (cardfsD1 k) H2 add1n => -[?]; subst.
  rewrite fset_sub_rem in IH.
  have xsk: x \in domf s.[~ k].
    rewrite -fset_sub_rem !inE (filter_in_domf xF) andbT.
    case: eqP => //?; subst.
    have/=:= forallP A [`(filter_in_domf xF)].
    move: xF; rewrite/= !inE; case: fndP => //= ks H.
    by clear H2; rewrite (cardfsD1 k) ks add1n/= in_fnd/= !inE H.
  have {IH} := IH x _ (acyclic_sigma_rem k A) erefl xsk.
  rewrite -fset_sub_rem.
  apply: contra.
  move: (#|` _ |) => n; elim: n => //.
    admit.
  move=> n IH; rewrite !get_father1.
  case: pickP => [[z zs]|] _.
    rewrite [val _]/= => HH.
    case: pickP => //[[y ys]|].
      move=> _; rewrite [val _]/=.
      admit.
    admit.
  move=> xs.
  case: pickP => [[w wP]/= _|].
    admit.
  admit.
Admitted.

(* Lemma acyclic_sigmaPP s:
  acyclic_sigma s -> 
    s = fmap0 \/ 
    exists (k: V),
      (if s.[?k] is Some t then deref1 s t = t else false).
Proof.
Abort. *)

Lemma acyclic_sigma1 s: acyclic_sigma s ->
  s = fmap0 \/ exists k : V, k \in domf s /\ k \notin codom_vars s.
Proof.
  have [] := set0IN (domf s); first by move => /fmap_nil ->; left.
  move=> [k ks] A; right.
  by exists (get_father k #|` domf s| s); rewrite get_father_domf//get_father_codomf.
Qed.

Lemma deref_succ_id1 k s: 
  k \in domf s -> k \notin codom_vars s ->
    forall t, k \notin vars_tm (deref1 s t).
Proof.
  move=> D C.
  elim => //=[v|f /negP Hf a Ha].
    move: C; apply: contra.
    case: fndP => //=vs.
      by move=> /fsubsetP -/(_ _ (codom_vars_sub _)).
    by rewrite inE => /eqP?; subst; rewrite D in vs.
  move: Ha; apply: contra.
  rewrite inE => /orP[H|//]; auto.
Qed.

Lemma deref1_unreachable s k t:
  k \notin vars_tm t -> deref1 s.[~ k] t = deref1 s t.
Proof.
  elim: t => // [v|f Hf a Ha].
    by rewrite/deref1 fnd_rem1 inE eq_sym => ->.
  by rewrite /= inE; case kf: (_ \in _) => //= /Ha ->; rewrite Hf//kf.
Qed.

Lemma deref1_codom k s t:
  k \notin vars_tm t ->
  k \notin codom_vars s -> k \notin vars_tm (deref1 s t).
Proof.
  move=> H; apply/contra.
  elim: t H => //=[v|f Hf a Ha] /negP kv.
    case: fndP => //= vs H.
    apply/fsubsetP/H/codom_vars_sub.
  move: kv => /negP; rewrite !inE negb_or => /andP[kf ka] /orP[kf'|ka']; auto.
Qed.

Lemma unreachable m s k t:
   k \notin codom_vars s -> k \notin vars_tm t ->
  deref_aux m s.[~ k] t = deref_aux m s t.
Proof.
  elim: m t => //= n IH t HD HV.
  rewrite deref1_unreachable//IH//.
  by apply: deref1_codom.
Qed.

Lemma deref_vars1 n s t:
  deref_vars n.+1 s t = vars_tm (deref1 s t) `|` deref_vars n s (deref1 s t).
Proof. by []. Qed.

Lemma deref_succ_id n s t: 
  acyclic_sigma s -> #|` domf s | <= n -> deref_aux n s t = deref s t.
Proof.
  move: (leqnn #|` domf s|) t n => //=.
  move: (x in _ <= x) => size; move: s.
  elim: size => //=.
    move=> s; rewrite leqn0 => /eqP/cardfs0_eq/fmap_nil->/= *.
    by rewrite !deref_aux_empty.
  move=> n IH s H t m H1 H2.
  case: m H2 => //[|m] H2.
    move:H2; rewrite leqn0 => /eqP/cardfs0_eq/fmap_nil->/= *.
    by rewrite !deref_empty.
  have [->|] := acyclic_sigma1 H1.
    by rewrite/deref !deref_aux_empty.
  move=> [k[HD HC]].
  have K := deref_succ_id1 HD HC t.
  rewrite/=.
  pose s' := s.[~k].
  have DD: #|` domf s'|.+1 = #|` domf s| by rewrite (cardfsD1 k (domf s)) HD add1n fset_sub_rem.
  rewrite -DD in H H2.
  have {}H: #|` domf s'| <= n by [].
  have {}H2: #|` domf s'| <= m by [].
  have:= IH s.[~k] H (deref1 s t) m _ H2.
  rewrite /deref !unreachable// -DD => ->//.
  by apply/acyclic_sigma_rem.
Qed.

Fixpoint get_lowest_aux v n (s : Sigma) :=
  match n with
  | 0 => v
  | n.+1 =>
    if s.[?v] is Some t then
      let vars := vars_tm t `&` domf s in
      if pick vars is Some v then get_lowest_aux (val v) n s
      else v
    else v
  end.

Definition get_lowest v s := get_lowest_aux v #|` domf s | s.

Lemma get_lowest_domf v s: v \in domf s -> get_lowest v s \in domf s.
Proof.
  move=> vs; rewrite/get_lowest; elim: #|` _ | v vs => [|n IH]//=v vs.
  rewrite in_fnd; case: pickP => //= -[k kP]/= _.
  by apply: IH; move: kP; rewrite !inE => /andP[].
Qed.

(* Devo dimostrare che la unif/match assegano nuove variabili:
   che non toccano il codomonio. Quindi unif a b s = s' -> exists e, e + s' = s.
   Dimostro prima che deref mi da un termine che contiene variabili non nel
   dominio (vedi acyclic_deref_disjoint), sono queste le variabili assegnate.
   In ricorsione, la dimostrazione deve essere vera

   Quando faccio unif a b s = s' -> exists s'', unif b a s = s''
   La prova di questo lemma mi sembra difficile (o impossibile, per l'induzione sul nodo app),
  
   Penso si debba avere un lemma scritto come:

*)
Lemma get_lowest_codom v s (vs : v \in domf s): acyclic_sigma s -> 
  [forall v: vars_tm (s [` get_lowest_domf vs]), val v \notin domf s].
Proof.
  move=> A; apply/forallP => /=-[k ks]/=.
  (* move: (eqxx #|` domf s|) v vs => /eqP.
  move: (x in _ = x) => size; move: s.
  elim: size => //=[|n IH] s.
    by move=> /cardfs0_eq/fmap_nil->/= *; apply/forallP.
  move=> H v vs A.
  move: H; rewrite (cardfsD1 v) vs add1n => -[?]; subst.
  have:= IH (s.[~ get_lowest k s]) _ _ _ (acyclic_sigma_rem _ A). + (get_lowest ). _ t (acyclic_sigma_rem _ A).
  rewrite domf_rem !cardfsD !fsetI1 kP get_lowest_domf// !cardfs1 => /(_ erefl).
  Search deref. *)
Admitted.


Lemma acyclic_deref_disjoint s t:
  acyclic_sigma s -> [disjoint vars_tm (deref s t) & domf s].
Proof.
  (* rewrite/acyclic_sigma. *)
  move: (eqxx #|` domf s|) t => /eqP.
  move: (x in _ = x) => size; move: s.
  elim: size => //=[|n IH] s.
    by move=> /cardfs0_eq/fmap_nil->/= *; rewrite fdisjointX0.
  move=> H t.
  case: (set0IN (domf s)); first by move=> /fmap_nil ->/=; rewrite fdisjointX0.
  move=> [k kP] A.
  move: H; rewrite (cardfsD1 k) kP add1n => -[?]; subst.
  have:= IH (s.[~ get_lowest k s ]) _ t (acyclic_sigma_rem _ A).
  rewrite domf_rem !cardfsD !fsetI1 kP get_lowest_domf// !cardfs1 => /(_ erefl).
  Search deref.
Admitted.

Lemma ren_app m l r : ren m (Tm_App l r) = Tm_App (ren m l) (ren m r).
Proof. by []. Qed.

(* Lemma deref_aux_ren_V b v:
  deref_aux #|` domf b| [fmap x => Tm_V b.[valP x]] (Tm_V v) =
  Tm_V (odflt v b.[? v]).
Proof.
  case: fndP => vb/=; last first.
    by move: #|` _ |; elim => //= n IH; rewrite not_fnd.
  rewrite (cardfsD1 v) vb /= in_fnd/= ffunE valPE.
  move: #|` _ |; elim => [// | n IH]/=.
  case: fndP => //= bb; rewrite ffunE valPE.
  have:= fdisjointP H _ bb.
  move=> /codomfP/= Hx; exfalso; apply:Hx.
  by exists v; rewrite in_fnd.
Qed. *)

Lemma deref_aux_P s n v: deref_aux n s (Tm_P v) = Tm_P v.
Proof. elim: n => //. Qed.

Lemma deref_P s v: deref s (Tm_P v) = Tm_P v.
Proof. apply/deref_aux_P. Qed.

Lemma ren_P b p: ren b (Tm_P p) = Tm_P p. by []. Qed.

Lemma deref_aux_D s n v: deref_aux n s (Tm_D v) = Tm_D v.
Proof. elim: n => //. Qed.

Lemma deref_D s v: deref s (Tm_D v) = Tm_D v.
Proof. apply/deref_aux_D. Qed.

Lemma ren_D b p: ren b (Tm_D p) = Tm_D p. by []. Qed.

(* Lemma deref_ren_V b v: acyclic_ren b ->
  deref [fmap x => Tm_V b.[valP x]] (Tm_V v) = Tm_V (odflt v b.[? v]).
Proof. by move=> H; rewrite/deref/=deref_aux_ren_V. Qed. *)

Lemma ren_V b v: ren b (Tm_V v) = Tm_V (odflt v b.[?v]). by []. Qed.

Lemma not_in_deref_aux_V n s v: 
  v \notin domf s -> deref_aux n s (Tm_V v) = Tm_V v.
Proof. by elim: n => //= n IH H; rewrite not_fnd // IH. Qed.

Lemma not_in_deref_V s v: v \notin domf s -> deref s (Tm_V v) = Tm_V v.
Proof. apply: not_in_deref_aux_V. Qed.

Lemma ren_isP b tm p: ren b tm = Tm_P p -> exists p', tm = Tm_P p'.
Proof. by case: tm => [p'|d|v|f a]//; eexists. Qed.

Lemma ren_isApp b hd f2 a2: ren b hd = Tm_App f2 a2 -> exists f1 a1, hd = Tm_App f1 a1.
Proof. case: hd => [p|d|v|f1 a1]//=; eauto. Qed.

Lemma rename_isApp fv hd fv' f2 a2 m:
  rename fv hd m = (fv', Tm_App f2 a2) ->
  exists f1 a1, hd = Tm_App f1 a1.
Proof.
  rewrite/rename !push => -[?+]; subst.
  case: hd => [p|d|v|f1 a1]//=; eauto.
Qed.

Definition fresh_atom fv a m :=
  match a with
  | cut => (fv, m, cut)
  | call t => let: (fv, m, t) := rename fv t m in (fv, m, call t)
  end.

Definition fresh_atoms fv a m :=
  foldr (fun x '(fv,m,xs) => let: (fv,m, x) := fresh_atom fv x m in (fv,m,x::xs)) (fv,m,[::]) a.

Definition fresh_rule fv r :=
  let: (fv, m, head) := rename fv r.(head) fmap0 in
  let: (fv, m, premises) := fresh_atoms fv r.(premises) m in
  (fv, mkR head premises ).

Definition vars_sigma (s: Sigma) := domf s `|` codom_vars s.

Lemma vars_sigma0: vars_sigma empty = fset0.
Proof. by rewrite/vars_sigma domf0 codom_vars0 fsetU0. Qed.

Definition fresh_rules fv rules :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_rule fv x in (fv,x::xs)) (fv,[::]) rules.

(* Unification between query and rule-head *)
Fixpoint H u (md: seq mode) (q : list Tm) (h: list Tm) s : option Sigma :=
  match md,q,h with
  | [::], [::], [::] => Some s
  | md :: tl, x :: xs, y :: ys => 
    let f := if md == input then u.(matching) else u.(unify) in
    obind (f x y) (H u tl xs ys s)
  | _, _, _ => None
  end.

Fixpoint select u (hd:P) args md (rules: list R) sigma : (fvS * seq (Sigma * seq Atom)) :=
  match rules with
  | [::] => (fset0, [::])
  | rule :: rules =>
    let hd' := get_tm_hd rule.(head) in
    let args' := flatten_term rule.(head) in
    if inl hd != hd' then select u hd args md rules sigma
    else
    match H u md args args' sigma with
    | None => select u hd args md rules sigma
    | Some (sigma1) => 
      let: (fv, rs) := select u hd args md rules sigma in
      (vars_sigma sigma1 `|` varsU_rule rule `|` fv, (sigma1, rule.(premises)) :: rs)
    end
  end.

Section s.
Variable u : Unif.

(*SNIP: bc_type*)
Definition bc : program -> fvS -> Tm -> Sigma -> fvS * seq (Sigma * seq Atom) :=
(*ENDSNIP: bc_type*)
  fun pr fv (query:Tm) s =>
  if ~~ acyclic_sigma s then (fv, [::])
  else
  let query := deref s query in
  match get_tm_hd query with
    | inl kP =>  
      match pr.(sig).[? kP] with 
        | Some sig => 
          let args := flatten_term query in
          let: (fv, rules) := fresh_rules (vars_sigma s `|` vars_tm query `|` fv) (pr.(rules)) in
          let: (fv', rules) := select u kP args (flatten_mode sig) rules s
          in (fv `|` fv', rules)
        | None => (fv, [::])
        end
    | _ => (fv, [::]) (*this is a call with flex head or head being a data, in elpi it is an error! *)
    end.
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

(* Lemma is_detH u sP md s s' t t':
  H u md t t' s = Some s' ->
    tm_is_det sP t' = tm_is_det sP t.
Proof.
  elim: md s s' t t' => //=.
    by move=> s s' []//= p t'; case: eqP => //=?; subst.
  move=> [m _] tl Hl s1 s2 []//=f1 a1 []//= f2 a2.
  case H: H => //= _.
  rewrite !tm_is_det_app; apply: Hl H.
Qed. *)

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

Lemma varsU_empty: codom empty = [::].
Proof. apply/eqP; by rewrite -size_eq0 size_map enum_fset0. Qed.

Definition ground t := vars_tm t == fset0.

Lemma codom0_set v s: codom empty.[v <- s] = [::s].
Proof. by rewrite/= codomE/= fsetU0 enum_fset1/= ffunE//=eqxx. Qed.

Lemma acyclic_sigma_set_D k t:
  k \notin vars_tm t -> ground t ->
  acyclic_sigma empty.[k <- t].
Proof.
  rewrite/acyclic_sigma/=.
  rewrite/deref/= fsetU0 cardfs1 /ground => H /eqP G.
  apply/forallP => -[x xP]; rewrite deref_vars1 [val _]/=.
  move: xP; rewrite inE => /eqP?; subst.
  by rewrite /= !FmapE.fmapE eqxx/= fsetU0.
Qed.

Lemma ground_deref1 s t: ground t -> deref1 s t = t.
Proof. 
  rewrite/ground; elim: t => //=[v|f Hf a Ha].
    by move=> /eqP /fsetP /(_ v); rewrite !inE eqxx.
  by rewrite fsetU_eq0 => /andP => -[/Hf -> /Ha->].
Qed.

Lemma ground_deref s t: ground t -> deref s t = t.
Proof. by rewrite/deref; elim: #|`_| t => //= n IH*; rewrite ground_deref1//IH. Qed.

Lemma ground_V v: ground (Tm_V v) = false.
Proof. by rewrite/ground/=; apply:contraFF erefl => /eqP/fsetP /(_ v); rewrite !inE eqxx. Qed.

Lemma ground_app f a: ground (Tm_App f a) = ground f && ground a.
Proof. by rewrite /ground/= fsetU_eq0. Qed.


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
  matching : fvS -> Tm -> Tm -> Sigma -> option Sigma;
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


Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (deref s h) (deref s ag)
  end.

Definition derefkv k v (tm:Tm) := deref [fmap].[k<-v] tm.

(* Fixpoint deref1 (s: Sigma) (tm:Tm) :=
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

Definition deref (s:Sigma) (tm:Tm) := deref_aux #|` domf s | s tm. *)

(* Lemma deref_aux_App n s f a: 
  deref_aux n s (Tm_App f a) = Tm_App (deref_aux n s f) (deref_aux n s a).
Proof. elim: n f a => //=. Qed. *)

Lemma deref_App s f a: deref s (Tm_App f a) = Tm_App (deref s f) (deref s a).
Proof. by []. Qed.

Lemma deref_empty t: deref empty t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.


(* Lemma deref_aux_empty n t: deref_aux n empty t = t.
Proof. by elim: n t => //= n IH t; rewrite deref1_empty//. Qed.

Lemma deref_empty t: deref empty t = t.
Proof. by []. Qed. *)

(* Fixpoint deref_vars n s tm :=
  let tm := deref1 s tm in
  match n with
  | 0 => fset0
  | n.+1 => vars_tm tm `|` (deref_vars n s tm)
  end. *)

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

Lemma codom_vars_sub s k: codom_vars s.[~k] `<=` codom_vars s.
Proof.
  rewrite{1}/codom_vars.
  apply/fsubsetP => x /varUP[y [yP xP]].
  move: yP => /mapP[t ts]?; subst.
  suffices: exists k (H: k \in domf s), s.[H] = t.
    move=> [z[Hz ?]]; subst; by apply/fsubsetP/xP/codom_vars_sub_vt.
  have {ts} [[y yP] H] := codomP ts; subst.
  have ys : y \in domf s by move: yP {xP}; rewrite domf_rem inE => /andP[].
  exists y, ys.
  suffices [->//] : Some s.[ys] = Some (s.[~ k] [` yP]).
  rewrite -!in_fnd !FmapE.fmapE !inE; move: yP {xP}; rewrite domf_rem !inE.
  by case: eqP => //= _ ->.
Qed.

Definition acyclic_sigma (s: Sigma) := [disjoint domf s & codom_vars s].

(* Definition acyclic_sigma (s: Sigma) :=
  [forall x : domf s, val x \notin deref_vars #|` domf s | s (Tm_V (val x))]. *)
  (* [forall x : domf s, val x \notin vars_tm (deref s (Tm_V (val x)))]. *)

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

Lemma codom0_set v s: codom empty.[v <- s] = [::s].
Proof. by rewrite/= codomE/= fsetU0 enum_fset1/= ffunE//=eqxx. Qed.

Lemma codom_vars_set s k v:
  codom_vars s.[k <- v] = codom_vars s.[~k] `|` vars_tm v.
Proof.
  have:= codom_vars_cat s [fmap].[k <- v].
  rewrite -setf_catr catf0 =>->.
  rewrite dom_setf fsetU0; f_equal.
  by rewrite/codom_vars codom0_set//= fsetU0.
Qed.

Lemma acyclic_sigma_set s k v:
  acyclic_sigma s.[k <- v] = 
    [&& acyclic_sigma s.[~k], (k \notin vars_tm v), (k \notin codom_vars s.[~k]) &
      fdisjoint (domf s) (vars_tm v)].
Proof.
  rewrite /acyclic_sigma dom_setf fdisjointUX fdisjoint1X !codom_vars_set.
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

Lemma acyclic_sigma_rem s k: acyclic_sigma s -> acyclic_sigma s.[~ k].
Proof.
  move=> H; apply/fdisjointWr/fdisjointWl/H.
    by rewrite codom_vars_sub.
  by rewrite domf_rem; apply/fsubsetP => x; rewrite inE => /andP[_ ->].
Qed.

Lemma empty_rem k: empty.[~k] = empty.
Proof. by apply/fmapP => p;rewrite fnd_rem1 not_fnd//if_same. Qed.

Lemma acyclic_sigma0: acyclic_sigma empty.
Proof. by rewrite/acyclic_sigma fdisjoint0X. Qed.

Lemma codom0: codom empty = [::].
Proof. by rewrite /empty codomE/= enum_fset0. Qed.

Lemma codom_vars0: codom_vars empty = fset0.
Proof. by rewrite/codom_vars codom0. Qed.

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 0)]).
Proof. by rewrite acyclic_sigma_set empty_rem acyclic_sigma0 codom_vars0 fdisjoint0X/= !inE. Qed.

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)]).
Proof. by rewrite acyclic_sigma_set !inE remf1_id ?inE// codom_vars_set !inE/= eqxx orbT/= andbF. Qed.

Goal ~ (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)].[IV 1 <- Tm_V (IV 0)].[IV 2 <- Tm_D (ID 0)]).
Proof.
  rewrite acyclic_sigma_set remf1_id?inE// acyclic_sigma_set inE.
  by rewrite remf1_id?inE//= fdisjointX0 andbT codom_vars_set !inE/= eqxx orbT/= andbF.
Qed.

Goal (acyclic_sigma [fmap].[IV 0 <- Tm_V (IV 1)]).
Proof.
  by rewrite acyclic_sigma_set empty_rem acyclic_sigma0 codom_vars0 !inE fdisjoint0X.
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

Require Import Lia.

Lemma set0IN (T: choiceType) (s: {fset T}): s = fset0 \/ exists k, k \in s.
Proof. have:= fset_0Vmem s => -[->|]; auto => -[x H]; right; exists x; auto. Qed.

(* Lemma deref1_singl k s t t':
  s = ctx.empty.[k <- t'] -> vars_tm t `<=` vars_tm t' ->
  k \in vars_tm t -> k \in vars_tm (deref1 s t).
Proof.
  move=> ->; elim: t t' => [p|d|v|f Hf a Ha] t'//; try by rewrite/= fsubset0 => /eqP->.
    rewrite/deref1 fnd_set not_fnd//; case: eqP => //= H.
    by rewrite fsub1set !inE => + /eqP->.
  rewrite/= !inE fsubUset => /andP[H1 H2] /orP[] H; [rewrite Hf|rewrite Ha] => //.
  by rewrite orbT.
Qed. *)

(* Lemma varsU_subset_rem (s:Sigma) k:
  varsU (map vars_tm (codom s)) `<=` 
    varsU (map vars_tm (codom s.[~ k])).
Proof.
  rewrite/codom.
  Search codom *)

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
  acyclic_sigma (s+e) -> deref (s+e) (deref e t) = deref (s+e) t.
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
  (acyclic_sigma s) -> deref s (deref s t) = deref s t.
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

Lemma deref_succ_id1 k s: 
  k \in domf s -> k \notin codom_vars s ->
    forall t, k \notin vars_tm (deref s t).
Proof.
  move=> D C.
  elim => //=[v|f Hf a Ha]; last by rewrite inE (negbTE Hf)//.
  case: fndP => vs/=.
    move: C; apply: contra => H.
    apply/fsubsetP/H/codom_vars_sub_vt.
  rewrite inE; case: eqP => ?//; subst.
  by rewrite D in vs.
Qed.

Lemma deref_rem s k t:
  k \notin vars_tm t -> deref s.[~ k] t = deref s t.
Proof.
  elim: t => //= [v|f Hf a Ha].
    by rewrite/deref; rewrite inE fnd_rem1 eq_sym => ->.
  by rewrite inE => /norP[/Hf->/Ha->].
Qed.

Lemma deref_codom k s t:
  k \notin vars_tm t ->
  k \notin codom_vars s -> k \notin vars_tm (deref s t).
Proof.
  have:= vars_tm_deref_sub s t => /fsubsetP/(_ k); rewrite !inE.
  case: (boolP (_ \in _)) => // H /(_ isT)/orP[]->//.
Qed.

Lemma acyclic_deref_disjoint s t:
  acyclic_sigma s -> [disjoint domf s & vars_tm (deref s t)].
Proof.
  move=> A; elim: t => //=; only 1, 2: by rewrite fdisjointX0.
    move=> v; case: fndP => //=vs.
      by apply/fdisjointWr/A/codom_vars_sub_vt.
    by rewrite fdisjointX1.
  by move=> f Hf a Ha; rewrite fdisjointXU Hf.
Qed.

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


Lemma deref_P s v: deref s (Tm_P v) = Tm_P v. by []. Qed.

Lemma ren_P b p: ren b (Tm_P p) = Tm_P p. by []. Qed.

Lemma deref_D s v: deref s (Tm_D v) = Tm_D v. by []. Qed.

Lemma ren_D b p: ren b (Tm_D p) = Tm_D p. by []. Qed.

(* Lemma deref_ren_V b v: acyclic_ren b ->
  deref [fmap x => Tm_V b.[valP x]] (Tm_V v) = Tm_V (odflt v b.[? v]).
Proof. by move=> H; rewrite/deref/=deref_aux_ren_V. Qed. *)

Lemma ren_V b v: ren b (Tm_V v) = Tm_V (odflt v b.[?v]). by []. Qed.

Lemma not_in_deref_V s v: v \notin domf s -> deref s (Tm_V v) = Tm_V v.
Proof. move=> H; rewrite/= not_fnd//. Qed.

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
(* mv is the set of "frozen" variables appearing in input position in the query
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
Fixpoint H u fv (md: seq mode) (q : list Tm) (h: list Tm) s : option Sigma :=
  match md,q,h with
  | [::], [::], [::] => Some s
  | md :: tl, x :: xs, y :: ys => 
    let f := if md == input then u.(matching) fv else u.(unify) in
    obind (H u fv tl xs ys) (f y x s)
  | _, _, _ => None
  end.

Fixpoint get_frozen_vars ms qargs :=
  match ms with
  | [::] => fset0
  | m :: ms =>
    match qargs with
    | [::] => fset0
    | x :: xs => 
      if m == input then vars_tm x `|` get_frozen_vars ms xs
      else get_frozen_vars ms xs
    end
  end.

Fixpoint select u (hd:P) args md (rules: list R) sigma : (fvS * seq (Sigma * seq Atom)) :=
  match rules with
  | [::] => (fset0, [::])
  | rule :: rules =>
    let hd' := get_tm_hd rule.(head) in
    let args' := flatten_term rule.(head) in
    if inl hd != hd' then select u hd args md rules sigma
    else
    match H u (get_frozen_vars md args) md args args' sigma with
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

Lemma ground_V v: ground (Tm_V v) = false.
Proof. by rewrite/ground/=; apply:contraFF erefl => /eqP/fsetP /(_ v); rewrite !inE eqxx. Qed.

Lemma ground_app f a: ground (Tm_App f a) = ground f && ground a.
Proof. by rewrite /ground/= fsetU_eq0. Qed.

Lemma acyclic_sigma_set_D k t: ground t -> acyclic_sigma empty.[k <- t].
Proof.
  rewrite acyclic_sigma_set empty_rem fdisjoint0X acyclic_sigma0 codom_vars0.
  by rewrite /ground => /eqP->//.
Qed.

Lemma ground_deref s t: ground t -> deref s t = t.
Proof.
  elim: t => //[v|f Hf a Ha].
    by rewrite ground_V.
  by rewrite ground_app => /=/andP[/Hf->/Ha->].
Qed.

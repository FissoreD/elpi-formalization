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

Definition deref s tm := deref_aux #|` domf s | s tm.

Lemma deref_aux_App n s f a: 
  deref_aux n s (Tm_App f a) = Tm_App (deref_aux n s f) (deref_aux n s a).
Proof. elim: n f a => //=. Qed.

Lemma deref_App s f a: deref s (Tm_App f a) = Tm_App (deref s f) (deref s a).
Proof. rewrite/deref deref_aux_App//. Qed.

Lemma deref_empty t: deref empty t = t.
Proof. by []. Qed.

Fixpoint acyclic_aux n s (seen: {fset V}) tm :=
  let tm' := deref1 s tm in
  let vtm' := vars_tm tm' in
  match n with
  | 0 => true
  | n.+1 => (seen `&` vtm' == fset0) && (acyclic_aux n s (seen `|` vtm') tm')
  end.

Definition acyclic_sigma (s: Sigma) :=
  (* [forall x : domf s, acyclic_aux #|` domf s | s [fset (val x)] s.[valP x]]. *)
  [forall x : domf s, val x \notin vars_tm (deref s (Tm_V (val x)))].

Definition acyclic_ren (m: {fmap V -> V}) := 
  (* acyclic_sigma [fmap s => Tm_V m.[valP s]]. *)
  [disjoint domf m & codomf m].

Lemma fresh_Tm_App fv m l r :
  fresh_tm fv m (Tm_App l r) =
    let rl := fresh_tm fv m l in
    fresh_tm rl.1 rl.2 r.
Proof.
by rewrite /= [fresh_tm _ _ l]surjective_pairing [fresh_tm _ _ r]surjective_pairing /=.
Qed.

Definition ren (m: {fmap V -> V}) := deref [fmap x : domf m => Tm_V m.[valP x]].

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

Lemma deref_succ_id n s t: 
  acyclic_sigma s -> n > #|` domf s | -> deref_aux n s t = deref s t.
Proof.
  rewrite/acyclic_sigma/deref/=.
  
  (* remember (#|` domf s|) as N eqn:H. *)
  (* rewrite -H. *)
  move: (leqnn #|` domf s|) t n => //=.
  move: (x in _ <= x) => size; move: s.
  elim: size => //=.
    (* admit.
  move=> n IH s H t m.
  Search (domf _).
  (* move=> s


  elim: (x in _ <= x) s (leqnn #|` domf s|) t n => //=.
    admit.
  case: n => //=[n]. *)
  suffices [k[s' Hk]]: exists k (s': Sigma), s' = s.[~ k].
    (* subst. *)
    move=> H1 H2.
    have {}IH := IH s'; subst. *)
Admitted.

Lemma ren_app m l r : ren m (Tm_App l r) = Tm_App (ren m l) (ren m r).
Proof. by rewrite/ren deref_App. Qed.

Lemma deref_aux_ren_V b v:
  acyclic_ren b ->
  deref_aux #|` domf b| [fmap x => Tm_V b.[valP x]] (Tm_V v) =
  Tm_V (odflt v b.[? v]).
Proof.
  case: fndP => vb/= H; last first.
    by move: #|` _ |; elim => //= n IH; rewrite not_fnd.
  rewrite (cardfsD1 v) vb /= in_fnd/= ffunE valPE.
  move: #|` _ |; elim => [// | n IH]/=.
  case: fndP => //= bb; rewrite ffunE valPE.
  have:= fdisjointP H _ bb.
  move=> /codomfP/= Hx; exfalso; apply:Hx.
  by exists v; rewrite in_fnd.
Qed.

Lemma deref_aux_P s n v: deref_aux n s (Tm_P v) = Tm_P v.
Proof. elim: n => //. Qed.

Lemma deref_P s v: deref s (Tm_P v) = Tm_P v.
Proof. apply/deref_aux_P. Qed.

Definition ren_P b p: ren b (Tm_P p) = Tm_P p := deref_P _ _.

Lemma deref_aux_D s n v: deref_aux n s (Tm_D v) = Tm_D v.
Proof. elim: n => //. Qed.

Lemma deref_D s v: deref s (Tm_D v) = Tm_D v.
Proof. apply/deref_aux_D. Qed.

Definition ren_D b p: ren b (Tm_D p) = Tm_D p := deref_D _ _.

Lemma deref_ren_V b v: acyclic_ren b ->
  deref [fmap x => Tm_V b.[valP x]] (Tm_V v) = Tm_V (odflt v b.[? v]).
Proof. by move=> H; rewrite/deref/=deref_aux_ren_V. Qed.

Lemma ren_V b v: acyclic_ren b ->
  ren b (Tm_V v) = Tm_V (odflt v b.[?v]).
Proof. by apply/deref_ren_V. Qed.

Lemma ren_VE b v: exists x, ren b (Tm_V v) = Tm_V x.
Proof. 
  rewrite/ren/deref; elim: #|`_| v => //=[|n IH] v; eauto. 
  by case: fndP => //= vb; rewrite ffunE valPE//.
Qed.

Lemma not_in_deref_aux_V n s v: 
  v \notin domf s -> deref_aux n s (Tm_V v) = Tm_V v.
Proof. by elim: n => //= n IH H; rewrite not_fnd // IH. Qed.

Lemma not_in_deref_V s v: v \notin domf s -> deref s (Tm_V v) = Tm_V v.
Proof. apply: not_in_deref_aux_V. Qed.

Lemma ren_VE1 b v: exists x, ren b (Tm_V v) = Tm_V x /\ (x = v \/ x \in codomf b).
Proof. 
  rewrite/ren/deref; elim: #|`_| v => //=[|n IH] v; eauto.
  case: fndP => /= vb.
    rewrite ffunE/= valPE.
    have [x[H1[H2|H2]]] := IH (b.[vb]); subst; rewrite H1; eauto.
    repeat eexists; eauto.
    by right; apply/codomfP; exists v; rewrite in_fnd.
  by exists v; split; auto; rewrite not_in_deref_aux_V//.
Qed.

Lemma ren_isP b tm p:
  ren b tm = Tm_P p ->
  exists p', tm = Tm_P p'.
Proof.
  case: tm => //[p'|d|v|f a]; first by repeat eexists.
    by rewrite ren_D.
    by have [? ->] := ren_VE b v.
  rewrite ren_app//.
Qed.

Lemma ren_isApp b hd f2 a2:
  ren b hd = Tm_App f2 a2 ->
  exists f1 a1, hd = Tm_App f1 a1.
Proof.
  case: hd => //=[p|d|v|f1 a1]; rewrite?(ren_P,ren_D,ren_app)//; eauto.
  by have [? ->] := ren_VE b v.
Qed.

Lemma rename_isApp fv hd fv' f2 a2 m:
  rename fv hd m = (fv', Tm_App f2 a2) ->
  exists f1 a1, hd = Tm_App f1 a1.
Proof.
  rewrite/rename !push => -[?+]; subst.
  case: hd => //=[p|d|v|f1 a1]; rewrite ?(ren_P,ren_D,push,ren_app)//=; eauto.
  move: (if _ then _ else _) => -[_ y]/=.
  by have [? ->]:= ren_VE y v.
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

Definition codom_vars (s:Sigma) := 
  varsU (map vars_tm (codom s)).

Lemma codom0: codom empty = [::].
Proof. by rewrite /empty codomE/= enum_fset0. Qed.

Lemma codom_vars0: codom_vars empty = fset0.
Proof. by rewrite/codom_vars codom0. Qed.

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

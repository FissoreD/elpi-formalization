From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.

Declare Scope type2_scope.
Delimit Scope type2_scope with type2.

Notation "a /\ b" := (a%type2 * b%type2)%type : type2_scope.

Notation "'Texists' x .. y , p" := (Specif.sigT (fun x => .. (Specif.sigT (fun y => p%type2)) ..))
  (at level 200, x binder, right associativity)
  : type_scope .

Lemma orPT b1 b2 : (b1 || b2) -> (b1 + b2)%type.
by case: b1; case: b2; constructor.
Qed.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Inductive Det := Func | Pred.
Inductive B := Exp | d of Det.
Inductive mode := i | o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).

Definition D2o D : 'I_2 := match D with Func => @Ordinal 2 0 isT | Pred => @Ordinal 2 1 isT end.
Definition o2D (i : 'I_2) : option Det := match val i with 0 => Some Func | 1 => Some Pred | _ => None end.
Lemma D2oK : pcancel D2o o2D. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy Det (pcan_type D2oK).

Definition B2o B : GenTree.tree Det := match B with Exp => GenTree.Node 0 [::] | d D => GenTree.Leaf D end.
Definition o2B (i :  GenTree.tree Det) : option B := match i with GenTree.Node 0 [::] => Some Exp | GenTree.Leaf x => Some (d x) | _ => None end.
Lemma B2oK : pcancel B2o o2B. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy B (pcan_type B2oK).

Definition mode2o mode : 'I_2 := match mode with i => @Ordinal 2 0 isT | o => @Ordinal 2 1 isT end.
Definition o2mode (x : 'I_2) : option mode := match val x with 0 => Some i | 1 => Some o | _ => None end.
Lemma mode2oK : pcancel mode2o o2mode. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy mode (pcan_type mode2oK).

Fixpoint S2o S : GenTree.tree (B + mode) := match S with b x => GenTree.Leaf (inl x) | arr m x y => GenTree.Node 0 [:: GenTree.Leaf (inr m); S2o x; S2o y] end.
Fixpoint o2S (i :  GenTree.tree (B + mode)) : option S := match i with GenTree.Leaf (inl x) => Some (b x) | GenTree.Node 0 [:: GenTree.Leaf (inr m); x; y] => obind (fun x => obind (fun y => Some (arr m x y)) (o2S y) ) (o2S x)  | _ => None end.
Lemma S2oK : pcancel S2o o2S. Proof. by elim=> //= ?? -> ? ->. Qed.
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

(*SNIP: call_type*)
Inductive Callable := 
  | Callable_P   of P
  | Callable_App of Callable & Tm.
(*ENDSNIP: call_type*)

derive Tm.
derive Callable.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.
HB.instance Definition _ := hasDecEq.Build Callable Callable_eqb_OK.

(*SNIP: atom_type*)
Inductive A := cut | call : Callable -> A.
(*ENDSNIP: atom_type*)

(*SNIP: R_type*)
Record R := mkR { head : Callable; premises : list A }.
(*ENDSNIP: R_type*)

derive A.
derive R.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.
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

Notation index := (list R).
Definition mode_ctx := {fmap P -> (list mode)}.
Definition sigT := {fmap P -> S}.
Definition empty_sig : sigT := [fmap].

Definition is_mode_ctx (x : mode_ctx) := unit.
Lemma is_mode_ctx_inhab : forall x, is_mode_ctx x. Proof. exact (fun x => tt). Qed.
Definition mode_ctx_eqb (x y : mode_ctx) := x == y.
Lemma mode_ctx_eqb_correct : forall x, eqb_correct_on mode_ctx_eqb x. Proof. by move=>??/eqP. Qed.
Lemma mode_ctx_eqb_refl : forall x, eqb_refl_on mode_ctx_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx mode_ctx is_mode_ctx is_mode_ctx_inhab mode_ctx_eqb mode_ctx_eqb_correct mode_ctx_eqb_refl.
HB.instance Definition _ : hasDecEq mode_ctx := Equality.copy mode_ctx _.

Definition is_sigT (x : sigT) := unit.
Lemma is_sigT_inhab : forall x, is_sigT x. Proof. exact (fun x => tt). Qed.
Definition sigT_eqb (x y : sigT) := x == y.
Lemma sigT_eqb_correct : forall x, eqb_correct_on sigT_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigT_eqb_refl : forall x, eqb_refl_on sigT_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigT is_sigT is_sigT_inhab sigT_eqb sigT_eqb_correct sigT_eqb_refl.
HB.instance Definition _ : hasDecEq sigT := Equality.copy sigT _.

(*SNIP: program_type*)
Record program := { rules : index; sig : sigT }.
(*ENDSNIP: program_type*)
derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

Record Unif := {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  

Fixpoint get_tm_hd (tm: Tm) : (D + (P + V)) :=
    match tm with
    | Tm_D K => inl K
    | Tm_P K => inr (inl K)
    | Tm_V V => inr (inr V)
    | Tm_App h _ => get_tm_hd h
    end.

Fixpoint Callable2Tm (c : Callable) : Tm :=
  match c with
  | Callable_P p => Tm_P p
  | Callable_App h t => Tm_App (Callable2Tm h) t
  end.

Fixpoint tm2RC (t : Tm) : option (Callable * P) :=
  match t with
  | Tm_D _ => None
  | Tm_V _ => None
  | Tm_P p => Some (Callable_P p, p)
  | Tm_App t1 t2 => 
    match tm2RC t1 with
    | None => None
    | Some (x, p) => Some (Callable_App x t2, p)
    end
  end.

Fixpoint count_tm_ag t := 
    match t with
    | Tm_App L _ => 1 + count_tm_ag L
    | _ => 0
    end.

Fixpoint keep_sig n s :=
  match n with
  | 0 => [::]
  | n.+1 => 
    match s with
    | arr m l r => (m, l) :: keep_sig n r
    | _ => [::]
    end
  end.

Definition sigtm tm s :=
  let tm_ag := count_tm_ag tm in
  (keep_sig tm_ag s).
  
Definition sigtm_rev tm s := rev (sigtm tm s).

Definition get_modes_rev tm sig :=
  map fst (sigtm_rev (Callable2Tm tm) sig).

Open Scope fset_scope.

Fixpoint vars_tm t : {fset V} :=
  match t with
  | Tm_D _ => fset0
  | Tm_P _ => fset0
  | Tm_V v => fset1 v
  | Tm_App l r => vars_tm l `|` vars_tm r
  end.

Definition vars_atom A : {fset V} :=
  match A with cut => fset0 | call c => vars_tm (Callable2Tm c) end.

Definition varsU (l: seq {fset V}) :=
  foldr (fun a e => a `|` e) fset0 l.

Definition vars_atoms L := varsU (map vars_atom L).

Definition varsU_rprem r : {fset V} := vars_atoms r.(premises).
Definition varsU_rhead (r: R) : {fset V} := vars_tm (Callable2Tm r.(head)).
Definition varsU_rule r : {fset V} := varsU_rhead r `|` varsU_rprem r.

Lemma freshV (fv : {fset V}) :  exists v : V, v \notin fv.
Proof.
exists (IV (\sum_(i <- fv) let: (IV n) := i in n ).+1)%N.
case: in_fsetP => // -[[x] xP] /= [] /eq_leq.
by rewrite (big_fsetD1 _ xP) /= -ltn_subRL subnn ltn0.
Qed.

Definition fresh  (fv : {fset V}) : V := xchoose (freshV fv).
Definition freshP (fv : {fset V}) : (fresh fv) \in fv = false.
Proof. by apply: negbTE (xchooseP (freshV fv)). Qed.

Fixpoint fresh_tm fv t : {fset V} * Tm :=
  match t with
  | Tm_D _ => (fv, t)
  | Tm_P _ => (fv, t)
  | Tm_V v =>  let fv := fset1 v `|` fv in let v := fresh fv in (fset1 v `|` fv, Tm_V v)
  | Tm_App l r => let: (fv, l) := fresh_tm fv l in let: (fv, r) := fresh_tm fv r in (fv, Tm_App l r)
  end.

Fixpoint same_a_equiv seen t1 t2 : (bool * {fmap V -> V}) :=
  match t1, t2 with
  | Tm_D t1, Tm_D t2 | Tm_P t1, Tm_P t2 => (t1 == t2, seen)
  | Tm_V v1, Tm_V v2 => 
    if seen.[?v1] is Some v2' then ((v2 == v2'), seen)
    else (seen.[?v2] == None, seen.[v1 <- v2])
  | Tm_App f1 a1, Tm_App f2 a2 => 
    let: (b1, seen1) := same_a_equiv seen f1 f2 in
    if b1 then
      let: (b2, seen2) := same_a_equiv seen1 a1 a2 in
      (b2, seen2)
    else (false, seen)
  | _, _ => (false, seen)
  end.

Definition fmap_id {T:choiceType} (D: {fmap T -> T}) := [forall x : domf D, val x == D.[valP x]].
Definition fmap_comm {T:choiceType} (D1 D2: {fmap T -> T}) := 
  [forall x : domf D1, 
    if D2.[?val x] is Some x' then 
      if D1.[?x'] is Some x'' then val x == x''
      else false
    else false].

Lemma same_a_equiv_refl seen0 t b seen1: 
  fmap_id seen0 ->
  same_a_equiv seen0 t t = (b, seen1) -> b /\ fmap_id seen1.
Proof.
  elim: t seen0 b seen1 => //=.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> v seen0 b seen1 H; case: fndP => vP[<-<-].
      have /= := forallP H (Sub v vP).
      rewrite H valPE => ->; auto.
    repeat eexists.
    apply/forallP => /=-[k kP]/=; rewrite ffunE/=.
    move: kP; rewrite in_fset1U => /orP[/eqP->|]; first by rewrite eqxx.
    move=> ksP; case: ifP => ///eqP H2.
    have:= forallP H (Sub k ksP).
    rewrite valPE/= => /eqP Hx.
    by rewrite in_fnd//=-Hx.
  move=> f Hf a Ha seen0 b seenx H.
  case ef: same_a_equiv => [b1 seen1].
  have [+ H2] := Hf _ _ _ H ef.
  destruct b1 => //= _.
  case ea: same_a_equiv => [b2 seen2][<-<-].
  by apply: Ha ea.
Qed.

(* Lemma same_a_equiv_comm seen0 t1 t2 b1 b2 s1 s2: 
  fmap_id seen0 -> 
  same_a_equiv seen0 t1 t2 = (b1, s1) ->
  same_a_equiv seen0 t2 t1 = (b2, s2) ->
  b1 = b2 /\ fmap_comm s1 s2.
Proof.
  elim: t1 seen0 t2 b1 b2
  elim: t seen0 => //=.
    move=> k
  elim: t seen0 b seen1 => //=.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> v seen0 b seen1 H; case: fndP => vP[<-<-].
      have /= := forallP H (Sub v vP).
      rewrite H valPE => ->; auto.
    repeat eexists.
    apply/forallP => /=-[k kP]/=; rewrite ffunE/=.
    move: kP; rewrite in_fset1U => /orP[/eqP->|]; first by rewrite eqxx.
    move=> ksP; case: ifP => ///eqP H2.
    have:= forallP H (Sub k ksP).
    rewrite valPE/= => /eqP Hx.
    by rewrite in_fnd//=-Hx.
  move=> f Hf a Ha seen0 b seenx H.
  case ef: same_a_equiv => [b1 seen1].
  have [+ H2] := Hf _ _ _ H ef.
  destruct b1 => //= _.
  case ea: same_a_equiv => [b2 seen2][<-<-].
  by apply: Ha ea.
Qed. *)


Fixpoint fresh_callable fv c :=
  match c with
  | Callable_P _ => (fv, c)
  | Callable_App h t =>
      let: (fv, h) := fresh_callable fv h in
      let: (fv, t) := fresh_tm fv t in
      (fv, Callable_App h t)
  end.

(* Lemma fresh_tmP fv t : vars_tm (fresh_tm fv t).2 `&` (vars_tm t `|` fv) = fset0.

elim: t fv (fsubset_refl fv) => [?|?|v|l IHl r IHr] fv; rewrite /= ?fset0I //.
  apply/fsetP=> x; rewrite !in_fsetE -(freshP (v |` fv)).
  by case: eqP => [<- /[!in_fsetE]|_] //=; rewrite freshP.
  case: fresh_tm (IHl fv) => [fv' l'] /= {}IHl.
  case: fresh_tm (IHr fv')=> [fv'' r'] /= {}IHr.
  do [ set A := vars_tm _; set B := vars_tm _ ] in IHl *.
  do [ set A' := vars_tm _; set B' := vars_tm _ ] in IHr *.
  rewrite /= -fsetUA fsetIUr.
  rewrite [_ `&` (_ `|` _)]fsetIUl. IHr fsetU0.
  rewrite {2}(fsetUC A). [(A' `|` _) `&` _]fsetIUl.
Search fsetI fsetU.
  rewrite -fsetIA.
  fsetIUl .

have := fsetP.


Axiom fresh_rule : {fset V} -> R -> {fset V} * R. *)

Definition fresh_atom fv a :=
  match a with
  | cut => (fv, cut)
  | call t => let: (fv, t) := fresh_callable fv t in (fv, call t)
  end.

Definition fresh_atoms fv a :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_atom fv x in (fv,x::xs)) (fv,[::]) a.

Definition fresh_rule fv r :=
  let: (fv, head) := fresh_callable fv r.(head) in
  let: (fv, premises) := fresh_atoms fv r.(premises) in
  (fv, mkR head premises ).

Definition codom_vars (s:Sigma) := 
  varsU (map vars_tm (codom s)).


Definition vars_sigma (s: Sigma) := domf s `|` codom_vars s.

Definition fresh_rules fv rules :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_rule fv x in (fv,x::xs)) (fv,[::]) rules.

(* TODO: deref is too easy? Yes if sigma is a mapping from vars to lambdas in a future version *)
Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (deref s h) (deref s ag)
  end.

Fixpoint H u (ml : list mode) (q : Callable) (h: Callable) s : option Sigma :=
  match ml,q,h with
  | [::], Callable_P c, Callable_P c1 => if c == c1 then Some s else None
  | [:: i & ml], (Callable_App q a1), (Callable_App h a2) => obind (u.(matching) a1 a2) (H u ml q h s)
  | [:: o & ml], (Callable_App q a1), (Callable_App h a2) => obind (u.(unify) a1 a2) (H u ml q h s)
  | _, _, _ => None
  end.

Fixpoint select u fv (query : Callable) (modes:list mode) (rules: list R) sigma : ({fset V} * seq (Sigma * R)) :=
  match rules with
  | [::] => (fv, [::])
  | rule :: rules =>
    match H u modes query rule.(head) sigma with
    | None => select u fv query modes rules sigma
    | Some (sigma1) => 
      let: (fv, rs) := select u fv query modes rules sigma in
      (vars_sigma sigma1 `|` varsU_rule rule `|` fv, (sigma1, rule) :: rs)
    end
  end.

(* all_vars takes the set of used variables,
   when we "fresh the program" we need to takes variables
   outside this set
*)
Definition F u pr fv (query:Callable) s : {fset V} * seq (Sigma * R) :=
  match tm2RC (deref s (Callable2Tm query)) with
      | None => (fv, [::]) (*this is a call with flex head, in elpi it is an error! *)
      | Some (query, kp) =>
        match pr.(sig).[? kp] with 
          | Some sig => 
            let: (fv, rules) := fresh_rules fv (pr.(rules)) in
            select u fv query (get_modes_rev query sig) rules s
          | None => (fv, [::])
          end
      end.

(* Fixpoint varsD (l: seq {fset V}) :=
  match l with
  | [::] => true
  | x :: xs => ((x `&` varsU xs) == fset0) && varsD xs
  end.

Lemma varsD_rule_prem_aux {T:Type} r (rs: seq (T * _)):  
  varsU_rprem r
    `&` varsU [seq varsU_rhead x.2 `|` varsU_rprem x.2 | x <- rs] ==
    fset0 ->
    varsU_rprem r `&` varsU [seq varsU_rprem x.2 | x <- rs] == fset0.
Proof.
  elim: rs r => //=[[s r] rs] IH r1.
  rewrite !fsetIUr !fsetU_eq0 => /=/andP[/andP[H1 H2]] H3.
  by rewrite IH//=H2.
Qed.

Lemma varsD_rule_prem {T:Type} (r:seq (T * _)):
  varsD (map (fun x => varsU_rule x.2) r) ->
  varsD (map (fun x => varsU_rprem x.2) r).
Proof.
  elim: r => //=[[s r] rs] IH /andP[+ H2]; rewrite IH//andbT.
  rewrite/varsU_rule/= fsetIUl fsetU_eq0 => /andP[].
  move=> H3 H4.
  by rewrite varsD_rule_prem_aux//.
Qed. *)

(* Lemma backchain_fresh_prem u pr query s :
  varsD (map (fun x => varsU_rprem x.2) (F u pr query s)).
Proof.
  rewrite/F.
  case: tm2RC => // [[r p]].
  case: fndP => // kP.
  apply: varsD_rule_prem.
  apply: select_fresh.
Qed.

Lemma backchain_fresh_premE u pr query s l :
  (F u pr query s) = l ->
  varsD (map (fun x => varsU_rprem x.2) l).
Proof. by move=> <-; apply/backchain_fresh_prem. Qed. *)

Lemma push T1 T2 T3 (t : T1 * T2) (F : _ -> _ -> T3) : (let: (a, bx) := t in F a bx) = F t.1 t.2.
  by case: t => /=.
Qed.


Lemma select_in_rules u fv R modes rules s r:
  (select u fv R modes rules s) = r ->
    all (fun x => x.2 \in rules) r.2.
Proof.
  move=> <-{r}.
  apply/allP => /= x rs.
  elim: rules modes fv s rs => //= r rs IH m fv s.
  rewrite in_cons.
  case: H => [s'|/IH->]; last by rewrite orbT.
  rewrite !push/=.
  rewrite in_cons; case: eqP => /=; first by move=> ->; rewrite eqxx.
  by move=> _ /IH->; rewrite orbT.
Qed.

Lemma F_in u pr fv query s r:
  F u pr fv query s = r ->
    all (fun x => x.2 \in (fresh_rules fv pr.(rules)).2) r.2.
Proof.
  move=> <-{r}.
  rewrite/F/=.
  case: fresh_rules => [fv' pr'].
  case: tm2RC => //=[[r p]].
  case: fndP => //= kP.
  by apply: select_in_rules.
Qed.


(* Axiom deref_rigid: forall s t t',
  deref s t = t' ->
    get_tm_hd t' = 
      match get_tm_hd t with
      | inl K => inl K
      | inr (inl P) => inr (inl P)
      | inr (inr V) => 
        if s.[? V] is Some t then get_tm_hd t
        else inr (inr V)
      end. *)

Lemma tm2RC_get_tm_hd t c' p:
  tm2RC t = Some (c', p) ->
    ((get_tm_hd t = inr (inl p)) *
    (get_tm_hd (Callable2Tm c') = inr (inl p))).
Proof.
  elim: t c' p => //=.
    move=> k c' p [<-<-]//.
  move=> f Hf a _ c' p.
  case t: tm2RC => //=[[]][<-<-].
  apply: Hf t.
Qed.

(* Lemma tm2RC_deref s c c' p:
  tm2RC (deref s (Callable2Tm c)) = Some (c', p) ->
    match get_tm_hd (Callable2Tm c) with
    | inl K => False
    | inr (inl P) => P = p
    | inr (inr V) => 
      if s.[? V] is Some t then get_tm_hd (deref s t) = inr (inl p)
      else False
    end.
Proof.
  elim: c c' p => //=; first by congruence.
    move=> v c' p; case: fndP => //= vs H.
    remember (deref _ _) as df eqn:H1.
    have {}H1 := esym H1.
    rewrite (deref_rigid H1).
    have {}H := tm2RC_get_tm_hd H.
    by rewrite H.
  move=> f Hf t c' p.
  remember (deref _ _) as df eqn:H.
  have {}H := esym H.
  case X: tm2RC => //=[[RC P]][??]; subst.
  by apply: Hf X.
Qed. *)
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

Inductive D := Func | Pred.
Inductive B := Exp | d of D.
Inductive mode := i |o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).

Definition D2o D : 'I_2 := match D with Func => @Ordinal 2 0 isT | Pred => @Ordinal 2 1 isT end.
Definition o2D (i : 'I_2) : option D := match val i with 0 => Some Func | 1 => Some Pred | _ => None end.
Lemma D2oK : pcancel D2o o2D. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy D (pcan_type D2oK).

Definition B2o B : GenTree.tree D := match B with Exp => GenTree.Node 0 [::] | d D => GenTree.Leaf D end.
Definition o2B (i :  GenTree.tree D) : option B := match i with GenTree.Node 0 [::] => Some Exp | GenTree.Leaf x => Some (d x) | _ => None end.
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

Inductive Kp := IKp : nat -> Kp.
derive Kp.
HB.instance Definition _ := hasDecEq.Build Kp Kp_eqb_OK.
Definition Kp_of_nat x := IKp x.
Definition nat_of_Kp x := match x with IKp x => x end.
Lemma Kp_is_nat : cancel nat_of_Kp Kp_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy Kp (can_type Kp_is_nat).

Inductive Kd := IKd : nat -> Kd.
derive Kd.
HB.instance Definition _ := hasDecEq.Build Kd Kd_eqb_OK.

Inductive V := IV : nat -> V.
derive V.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.
Definition V_of_nat x := IV x.
Definition nat_of_V x := match x with IV x => x end.
Lemma V_is_nat : cancel nat_of_V V_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy V (can_type V_is_nat).
Inductive Tm := 
  | Tm_Kp    : Kp -> Tm
  | Tm_Kd    : Kd -> Tm
  | Tm_V     : V  -> Tm
  | Tm_Comb  : Tm -> Tm -> Tm.
derive Tm.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.

Inductive Callable := 
  | Callable_Kp   : Kp -> Callable
  | Callable_V    : V -> Callable
  | Callable_Comb : Callable -> Tm -> Callable.
derive Callable.
HB.instance Definition _ := hasDecEq.Build Callable Callable_eqb_OK.

(* Used for rules head *)
Inductive RCallable := 
  | RCallable_Kp   : Kp -> RCallable
  | RCallable_Comb : RCallable -> Tm -> RCallable.
derive RCallable.
HB.instance Definition _ := hasDecEq.Build RCallable RCallable_eqb_OK.

Record R_ {A} := mkR { head : RCallable; premises : list A }.
Arguments mkR {_} _ _.
derive R_.
Inductive A :=
  | ACut
  | ACall : Callable -> A.
derive A.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.

Notation R := (@R_ A).
HB.instance Definition _ := hasDecEq.Build R (R__eqb_OK _ _ A_eqb_OK).

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

Definition Sigma := (ctx V Tm).
Definition empty : Sigma := empty.

Definition is_Sigma (x : Sigma) := unit.
Lemma is_Sigma_inhab : forall x, is_Sigma x. Proof. exact (fun x => tt). Qed.
Definition Sigma_eqb (x y : Sigma) := x == y.
Lemma Sigma_eqb_correct : forall x, eqb_correct_on Sigma_eqb x. Proof. by move=>??/eqP. Qed.
Lemma Sigma_eqb_refl : forall x, eqb_refl_on Sigma_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
HB.instance Definition _ : hasDecEq Sigma := Equality.copy Sigma _.

Notation index := (list R).
Definition mode_ctx := {fmap Kp -> (list mode)}.
Definition sigT := {fmap Kp -> S}.
Definition empty_sig : sigT := [fmap].

(* 
  The program knows about the signature of all predicates, therefore,
  for each predicate we return a S (not an option S)
*)
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

Record program := { 
    (*depth : nat;*) 
    rules : index; 
    sig   : sigT
  }.
derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

Record Unif := {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  

Fixpoint get_tm_hd (tm: Tm) : (Kd + (Kp + V)) :=
    match tm with
    | Tm_Kd K => inl K
    | Tm_Kp K => inr (inl K) (*TODO: sP should be complete*)
    | Tm_V V => inr (inr V)
    | Tm_Comb h _ => get_tm_hd h
    end.

Fixpoint Callable2Tm (c : Callable) : Tm :=
  match c with
  | Callable_Kp p => Tm_Kp p
  | Callable_V v => Tm_V v
  | Callable_Comb h t => Tm_Comb (Callable2Tm h) t
  end.

Fixpoint RCallable2Callable rc := 
  match rc with
  | RCallable_Comb h bo => Callable_Comb (RCallable2Callable h) bo
  | RCallable_Kp k => Callable_Kp (k)
  end.

Definition get_rcallable_hd r :=
  get_tm_hd (Callable2Tm (RCallable2Callable r)).
    
Fixpoint H u (ml : list mode) (q : RCallable) (h: RCallable) s : option Sigma :=
  match ml,q,h with
  | [::], RCallable_Kp c, RCallable_Kp c1 => if c == c1 then Some s else None
  | [:: i & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(matching) a1 a2) (H u ml q h s)
  | [:: o & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(unify) a1 a2) (H u ml q h s)
  | _, _, _ => None
  end.

(* TODO: deref is too easy? Yes if sigma is a mapping from vars to lambdas in a future version *)
Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_Kp _ | Tm_Kd _ => tm
  | Tm_Comb h ag => Tm_Comb (deref s h) ag
  end.

Fixpoint select u (query : RCallable) (modes:list mode) (rules: list R) sigma : seq (Sigma * R) :=
  match rules with
  | [::] => [::]
  | rule :: rules =>
    match H u modes query rule.(head) sigma with
    | None => select u query modes rules sigma
    | Some sigma' => (sigma', rule) :: select u query modes rules sigma
    end
  end.

Fixpoint tm2RC (t : Tm) : option RCallable :=
  match t with
  | Tm_Kd _ => None
  | Tm_V _ => None
  | Tm_Kp p => Some (RCallable_Kp p)
  | Tm_Comb t1 t2 => omap (fun x => RCallable_Comb x t2) (tm2RC t1)
  end.

Fixpoint count_tm_ag t := 
    match t with
    | Tm_Comb L _ => 1 + count_tm_ag L
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
  map fst (sigtm_rev (Callable2Tm (RCallable2Callable tm)) sig).

Definition F u pr (query:Callable) s : seq (Sigma * R) :=
  let rules := pr.(rules) in
  match tm2RC (deref s (Callable2Tm query)) with
  | None => [::] (*this is a call with flex head, in elpi it is an error! *)
  | Some query =>
    match (get_rcallable_hd query) with
    | inr (inl kp) => 
      match pr.(sig).[? kp] with 
        | Some sig => select u query (get_modes_rev query sig) rules s
        | None => [::]
        end
      | _ => [::]
      end
  end.

Lemma select_in_rules u R modes rules s:
  all (fun x => x.2 \in rules) (select u R modes rules s).
Proof.
  elim: rules => //= x xs /allP IH.
  by case H => /=[_|]; rewrite?mem_head; apply/allP => -[s1 r1] /IH/=;
  rewrite in_cons => ->; rewrite orbT.
Qed.
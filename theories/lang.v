From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Inductive D := Func | Pred.
Inductive B := Exp | d of D.
Inductive mode := i |o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).
derive D.
Elpi derive.eqbOK.register_axiom D is_D is_nat_inhab D_eqb D_eqb_correct D_eqb_refl.
HB.instance Definition _ := hasDecEq.Build D D_eqb_OK.
derive B.
Elpi derive.eqbOK.register_axiom B is_B is_nat_inhab B_eqb B_eqb_correct B_eqb_refl.
HB.instance Definition _ := hasDecEq.Build B B_eqb_OK.
derive mode.
Elpi derive.eqbOK.register_axiom mode is_mode is_nat_inhab mode_eqb mode_eqb_correct mode_eqb_refl.
HB.instance Definition _ := hasDecEq.Build mode mode_eqb_OK.
derive S.
Elpi derive.eqbOK.register_axiom S is_S is_nat_inhab S_eqb S_eqb_correct S_eqb_refl.
HB.instance Definition _ := hasDecEq.Build S S_eqb_OK.

Inductive Kp := IKp : nat -> Kp.
derive Kp.
Elpi derive.eqbOK.register_axiom Kp is_Kp is_nat_inhab Kp_eqb Kp_eqb_correct Kp_eqb_refl.
HB.instance Definition _ := hasDecEq.Build Kp Kp_eqb_OK.

Inductive Kd := IKd : nat -> Kd.
derive Kd.
Elpi derive.eqbOK.register_axiom Kd is_Kd is_nat_inhab Kd_eqb Kd_eqb_correct Kd_eqb_refl.
HB.instance Definition _ := hasDecEq.Build Kd Kd_eqb_OK.

Inductive V := IV : nat -> V.
derive V.
Elpi derive.eqbOK.register_axiom V is_V is_nat_inhab V_eqb V_eqb_correct V_eqb_refl.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.


Inductive Tm := 
  | Tm_Kp    : Kp -> Tm
  | Tm_Kd    : Kd -> Tm
  | Tm_V     : V  -> Tm
  | Tm_Comb  : Tm -> Tm -> Tm.
derive Tm.
Elpi derive.eqbOK.register_axiom Tm is_Tm is_nat_inhab Tm_eqb Tm_eqb_correct Tm_eqb_refl.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.

Inductive Callable := 
  | Callable_Kp   : Kp -> Callable
  | Callable_V    : V -> Callable
  | Callable_Comb : Callable -> Tm -> Callable.
derive Callable.
Elpi derive.eqbOK.register_axiom Callable is_Callable is_nat_inhab Callable_eqb Callable_eqb_correct Callable_eqb_refl.
HB.instance Definition _ := hasDecEq.Build Callable Callable_eqb_OK.

(* Used for rules head *)
Inductive RCallable := 
  | RCallable_Kp   : Kp -> RCallable
  | RCallable_Comb : RCallable -> Tm -> RCallable.
derive RCallable.
Elpi derive.eqbOK.register_axiom RCallable is_RCallable is_nat_inhab RCallable_eqb RCallable_eqb_correct RCallable_eqb_refl.
HB.instance Definition _ := hasDecEq.Build RCallable RCallable_eqb_OK.

Record R_ {A} := mkR { head : RCallable; premises : list A }.
Arguments mkR {_} _ _.
derive R_.
Inductive A :=
  | ACut
  | ACall : Callable -> A.
derive A.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.


  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).
HB.instance Definition _ := hasDecEq.Build R (R__eqb_OK _ _ A_eqb_OK).

Record Sigma := { sigma : V -> option Tm }.
Definition empty : Sigma := {| sigma := fun _ => None |}.

Definition index := list R.
Definition mode_ctx := RCallable -> list mode.
Definition sigT := Kp -> S.
(* 
  The program knows about the signature of all predicates, therefore,
  for each predicate we return a S (not an option S)
*)
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx; sig : sigT }.

Parameter program_eqb : program -> program -> bool.
Parameter is_program : program -> Type.
Parameter is_program_inhab : forall p : program, is_program p.
Parameter program_eqb_correct : forall p1 p2, program_eqb p1 p2 -> p1 = p2.
Parameter program_eqb_refl : forall x, program_eqb x x.

Parameter Sigma_eqb : Sigma -> Sigma -> bool.
Parameter is_Sigma : Sigma -> Type.
Parameter is_Sigma_inhab : forall p : Sigma, is_Sigma p.
Parameter Sigma_eqb_correct : forall p1 p2, Sigma_eqb p1 p2 -> p1 = p2.
Parameter Sigma_eqb_refl : forall x, Sigma_eqb x x.



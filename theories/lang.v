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

Definition P := nat.
derive P.
Elpi derive.eqbOK.register_axiom P is_P is_nat_inhab P_eqb P_eqb_correct P_eqb_refl.

Definition K := nat.
derive K.
Elpi derive.eqbOK.register_axiom K is_K is_nat_inhab K_eqb K_eqb_correct K_eqb_refl.

Definition V := nat.
derive V.
Elpi derive.eqbOK.register_axiom V is_V is_nat_inhab V_eqb V_eqb_correct V_eqb_refl.

Inductive C := 
  | p of P 
  | v of V
  .
derive C.

Inductive Tm := 
  | Code : C -> Tm
  | Data : K -> Tm
  | Comb : Tm -> Tm -> Tm.
  (* | Lam  : V -> S -> Tm -> S -> Tm. *)
derive Tm.

Record R_ {A} := mkR { head : Tm; premises : list A }.
Arguments mkR {_} _ _.
derive R_.
Inductive A :=
  | Cut
  | Call : Tm -> A.
derive A.

  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).

HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.
HB.instance Definition _ := hasDecEq.Build C C_eqb_OK.
HB.instance Definition _ := hasDecEq.Build P P_eqb_OK.
HB.instance Definition _ := hasDecEq.Build K K_eqb_OK.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.
HB.instance Definition _ := hasDecEq.Build R (R__eqb_OK _ _ A_eqb_OK).

Record Sigma := { sigma : V -> option Tm }.
Definition empty : Sigma := {| sigma := fun _ => None |}.

Definition index := list R.
Definition mode_ctx := Tm -> list mode.
Definition sigT := P -> S.
(* 
  The predicate knows about the signature of all predicates, therefore,
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



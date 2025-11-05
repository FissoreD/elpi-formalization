From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

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
derive D.
HB.instance Definition _ := hasDecEq.Build D D_eqb_OK.
derive B.
HB.instance Definition _ := hasDecEq.Build B B_eqb_OK.
derive mode.
HB.instance Definition _ := hasDecEq.Build mode mode_eqb_OK.
derive S.
Elpi derive.eqbOK.register_axiom S is_S is_nat_inhab S_eqb S_eqb_correct S_eqb_refl.
HB.instance Definition _ := hasDecEq.Build S S_eqb_OK.

Goal b Exp == b Exp. by []. Qed.

Inductive Kp := IKp : nat -> Kp.
derive Kp.
HB.instance Definition _ := hasDecEq.Build Kp Kp_eqb_OK.

Inductive Kd := IKd : nat -> Kd.
derive Kd.
HB.instance Definition _ := hasDecEq.Build Kd Kd_eqb_OK.

Inductive V := IV : nat -> V.
derive V.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.


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



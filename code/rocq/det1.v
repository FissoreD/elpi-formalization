From mathcomp Require Import all_ssreflect.

Inductive D := Func | Pred.
Inductive B := Exp | d of D.
Inductive mode := i |o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).

Definition P := nat.
Definition K := nat.
Definition V := nat.
Inductive C := p of P | v of V.
Inductive Tm := 
  | Code : C -> Tm
  | Data : K -> Tm
  | Comb : Tm -> Tm -> Tm.
  (* | Lam  : V -> S -> Tm -> S -> Tm. *)
Record R_ {A} := { pred : P; args : list Tm; premises : list A }.
Inductive A :=
  (* | Cut *)
  (* | Call : C -> A *)
  | App : C -> list Tm -> A.
  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).

Definition Sigma := V -> option Tm.
Definition empty : Sigma := fun _ => None.

Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
Axiom matching : Tm -> Tm -> Sigma -> option Sigma.

Definition index := list R.
Definition mode_ctx := P -> list mode.
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx }.

(* Inductive goal := Goal of program & Sigma & A. *)

Axiom H : list mode -> list Tm -> list Tm -> Sigma -> option Sigma.
Fixpoint select argsI (modes:list mode) (rules: list R) sigma :=
  match rules with
  | [::] => [::]
  | rule :: rules =>
    match H modes argsI (rule.(args)) sigma with
    | None => select argsI modes rules sigma
    | Some sigma' => (sigma', rule) :: select argsI modes rules sigma
    end
  end.

Definition F pr pname args s :=
  let rules := pr.(rules) in
  let modes := pr.(modes) pname in
  let rules := select args modes rules s in
  rules.

Inductive state :=
  | KO : state
  | OK : Sigma -> state
  | Goal : program -> Sigma -> A -> state
  | Or  : state -> state -> state
  | And : state -> state -> state. 

Fixpoint big_and pr (s : Sigma) (a : list A) : state :=
  match a with
  | [::] => OK s
  | x :: xs => And (Goal pr s x) (big_and pr s xs)
  end.

Fixpoint big_or pr (s : seq (Sigma * R)) : state :=
  match s with 
  | [::] => KO
  | (s,r) :: xs => Or (big_and pr s r.(premises)) (big_or pr xs)
  end.

Inductive Res :=
  | ResY : Sigma -> state -> Res
  | ResN.

Fixpoint change_subst (st:state) (s:Sigma) :=
  match st with
  | KO => KO
  | OK _ => OK s
  | Goal pr _ a => Goal pr s a
  | Or l r => Or (change_subst l s) (change_subst r s)
  | And l r => And (change_subst l s) (change_subst r s)
end.

Inductive run : state -> Res -> Prop :=
  | run_top s : run (OK s) (ResY s KO)
  | run_fail : run KO ResN
  | run_or_ok S1 S2 s S1' : 
      run S1 (ResY s S1') ->
      (* =========Success or=========> *)
      run (Or S1 S2) (ResY s (Or S1' S2))
  | run_or_ko S1 S2 r : 
      run S1 ResN ->
      run S2 r ->
      (* ========Backtracking========> *)
      run (Or S1 S2) r
  | run_and x xs s st1 res:
      run x (ResY s st1) ->
      run (Or (change_subst xs s) (And st1 xs)) res ->
      (* ======And with success======> *)
      run (And x xs) res
  | run_call_pred pr pn args s res:
      run (big_or pr (F pr pn args s)) res ->
      (* =======Call with pred=======> *)
      run (Goal pr s (App (p pn) args)) res
  | run_call_var pr vn pn args s res:
      s vn = Some (Code (p pn)) -> (* TODO: Comb -> App *)
      run (Goal pr s (App (p pn) args)) res ->
      (* =======Call with var========> *)
      run (Goal pr s (App (v vn) args)) res.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Import Language.

Module Nur (U : Unif).

  Module Run := Run(U).
  Import Run U Language.

  Fixpoint H (ml : list mode) (q : Tm) (h: Tm) s : option Sigma :=
    match ml,q,h with
    | [::], Code c, Code c1 => if c == c1 then Some s else None
    | [:: i & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (U.matching a1 a2 s) 
    | [:: o & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (U.unify a1 a2 s) 
    | _, _, _ => None
    end.

  Fixpoint select (query : Tm) (modes:list mode) (rules: list R) sigma : seq (Sigma * R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      match H modes query rule.(head) sigma with
      | None => select query modes rules sigma
      | Some sigma' => (sigma', rule) :: select query modes rules sigma
      end
    end.

  Definition F pr query s : seq (Sigma * R) :=
    let rules := pr.(rules) in
    let modes := pr.(modes) query in
    let rules := select query modes rules s in
    rules.

  Inductive G := g : A -> list (list G) -> G.
  Definition alt := (list G).

  Definition next_alt {T:Type} a (k : list G -> list alt -> option  T) :=
    if a is [:: gl & a] then k gl a
    else None.

  Definition save_alt a (b: Sigma * R) gs := ([seq g x a | x <- (snd b).(premises)] ++ gs).
  Definition more_alt a bs gs := [seq (save_alt a b1 gs) | b1 <- bs] ++ a.


  Inductive nur (p: program) : list G ->  list alt -> list alt -> Prop :=
  | StopE a : nur [::] a a
  | CutE a ca r gl : nur gl ca r -> nur [:: g Cut ca & gl] a r
  | CallE a ca b bs gl r t s : 
    F p t s = [:: b & bs ] -> 
      nur (save_alt a b gl) (more_alt a bs gl) r -> 
        nur [::g (Call t) ca & gl] a r
  | FailE a g al r : nur a al r -> nur g (a :: al) r.

  Fixpoint state_to_list (A: state) : list alt :=
    match A with
    | OK | Top | Bot | KO | Dead => [::]
    | Goal _ A => [::[::g A [::]]]
    | Or A _ B => state_to_list A ++ state_to_list B
    | And A _ B => state_to_list A
    end.

  Lemma runElpi {s p A x xs r r1}:
    state_to_list A = x::xs ->
    run s A r -> nur p x xs r1 -> state_to_list (get_state_run r) = r1.
  Proof.
    move=> + [b H].
    elim: H p x xs r1; clear.
    + move=> s s' A B b H p x xs r1. (* Qui Stop *)
      admit.
    + move=> s A B b H H1 p x xs r1. (* Qui Fail*)
      admit.
    + move=> s s' r A B C b1 b2 b3 HA HB HC IH ?; subst.
      move=> p x xs r1.
      (* Qui backtracking: difficile da vedere facilmente nella nur? *)
      admit.
  Admitted.
End Nur.


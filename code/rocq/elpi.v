From mathcomp Require Import all_ssreflect.
From det Require Import lang.

Import Language.

Module Nur (U : Unif).

  Module Run := Run(U).
  Import Run U Language.

  Inductive G := 
    | call : Tm -> G
    | cut : list (list G) -> G.
  Definition alt := (list G).

  Definition next_alt {T:Type} a (k : list G -> list alt -> option  T) :=
    if a is [:: gl & a] then k gl a
    else None.

  Definition save_alt_ca (a : A) alts :=
    match a with
    | Cut => cut alts
    | Call t => call t
    end.

  Definition save_alt a (b: Sigma * R) gs := ([seq save_alt_ca x a | x <- (snd b).(premises)] ++ gs).
  Definition more_alt a bs gs := [seq (save_alt a b1 gs) | b1 <- bs] ++ a.


  Inductive nur (p: program) : list G ->  list alt -> list alt -> Prop :=
  | StopE a : nur [::] a a
  | CutE a ca r gl : nur gl ca r -> nur [:: cut ca & gl] a r
  | CallE a b bs gl r t s : 
    F p t s = [:: b & bs ] -> 
      nur (save_alt a b gl) (more_alt a bs gl) r -> 
        nur [::call t & gl] a r
  | FailE a g al r : nur a al r -> nur g (a :: al) r.

  Definition nur' p a r :=
    match a with
    | [::] => False
    | x :: xs => nur p x xs r
    end.

  Definition add_ca gl (l2 : list alt) : G :=
    match gl with
    | call t => call t
    | cut l1 => cut (l1 ++ l2) end.
  
  Definition add_cas lA lB : alt :=
    [seq add_ca gl lB | gl <- lA].

  Definition add_alt lA lB : list alt :=
    flatten [seq [seq la ++ lb | lb <- lB] | la <- lA].

  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
    | OK | Top => [::[::]]
    | Bot | KO | Dead => [::]
    | Goal _ Cut => [::[::cut [::]]]
    | Goal _ (Call t) => [::[::call t]]
    | Or A _ B => 
      let lB := state_to_list B bt in
      let lA := state_to_list A (lB ++ bt) in
      [seq add_cas la bt | la <- lA] ++ lB
    | And A _ B => 
      let lA := state_to_list A bt in
      let lB := state_to_list B bt in
      add_alt lA lB 
    end.

  Goal forall p b0 x y z w s1 s2, 
    state_to_list (
      And 
        (Or (Goal p (Call x)) s1 (Goal p (Call y))) b0 
        (Or (Goal p (Call z)) s2 (Goal p (Call w)))) [::] = 
      [:: [:: call x; call z];
      [:: call x; call w];
      [:: call y; call z];
      [:: call y; call w]].
  Proof. by []. Qed.

  Goal forall p a b s1 s2, 
    state_to_list (
      Or 
        (Or (Goal p Cut) s1 (Goal p (Call a))) s2
        (Goal p (Call b))) [::] = 
     [:: [:: cut [:: [:: call b]]]; [:: call a]; [:: call b]].
  Proof. by []. Qed.

  Goal forall b0 p a b c s1 s2, 
    state_to_list (
      Or 
        (Or (And (Goal p (Call c)) b0 (Goal p Cut)) s1 (Goal p (Call a))) s2
        (Goal p (Call b))) [::] = 
     [:: [:: call c; cut [:: [:: call b]]]; [:: call a]; [:: call b]].
  Proof. by []. Qed.

  Definition runElpi A :=
    forall s p r r1 b,
      runb s A r b -> nur' p (state_to_list A [::]) r1 -> state_to_list (get_state_run r) [::] = r1.
  
  Goal @runElpi OK.
  Proof.
    rewrite/runElpi => s p r r1 b/=.
    inversion 1; subst => //=.
    - inversion 1; subst.
      inversion H1; subst => //.
      case: H8 => _ <-/=.


  Lemma runExpandedb {s A s' B x xs}:
     expandedb s A (Done s' B) b ->
      state_to_list A [::] = x :: xs ->
        nur p x xs r1 ->
          state_to_list (get_state_run (Done s' B)) [::] = r1.

  Lemma runElpi {s p A x xs r r1}:
    state_to_list A [::] = x::xs ->
    run s A r -> nur p x xs r1 -> state_to_list (get_state_run r) [::] = r1.
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


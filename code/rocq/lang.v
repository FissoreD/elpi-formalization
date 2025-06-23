(* Require Import Coq.Program.Wf. *)
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

Module Type Unif.
  Parameter unify : Tm -> Tm -> Sigma -> option Sigma.
  Parameter matching : Tm -> Tm -> Sigma -> option Sigma.
End Unif.

Module Run (U : Unif).

  Definition unify := U.unify.
  Definition matching := U.matching.

  Definition index := list R.
  Definition mode_ctx := Tm -> list mode.
  Definition sigT := Tm -> S.
  Record program := { (*depth : nat;*) rules : index; modes : mode_ctx; sig : sigT }.

  (* Inductive goal := Goal of program & Sigma & A. *)

  (* Axiom H : list mode -> Tm -> Tm -> Sigma -> option Sigma. *)
  Fixpoint H (ml : list mode) (q : Tm) (h: Tm) s : option Sigma :=
    match ml,q,h with
    | [::], Code c, Code c1 => if c == c1 then Some s else None
    | [:: i & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (matching a1 a2 s) 
    | [:: o & ml], (Comb q a1), (Comb h a2) => obind (H ml q h) (unify a1 a2 s) 
    | _, _, _ => None
    end.

  Fixpoint select (query : Tm) (modes:list mode) (rules: list R) sigma :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      match H modes query rule.(head) sigma with
      | None => select query modes rules sigma
      | Some sigma' => (sigma', rule) :: select query modes rules sigma
      end
    end.

  Definition F pr query s :=
    let rules := pr.(rules) in
    let modes := pr.(modes) query in
    let rules := select query modes rules s in
    rules.

  Axiom program_eqb : program -> program -> bool.
  Axiom is_program : program -> Type.
  Axiom is_program_inhab : forall p : program, is_program p.
  Axiom program_eqb_correct : forall p1 p2, program_eqb p1 p2 -> p1 = p2.
  Axiom program_eqb_refl : forall x, program_eqb x x.

  Elpi derive.eqbOK.register_axiom program is_program is_program_inhab program_eqb program_eqb_correct program_eqb_refl.
  Lemma program_eqb_OK : Equality.axiom program_eqb.
  apply: iffP2 program_eqb_correct program_eqb_refl.
  Qed.
  HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

  Axiom Sigma_eqb : Sigma -> Sigma -> bool.
  Axiom is_Sigma : Sigma -> Type.
  Axiom is_Sigma_inhab : forall p : Sigma, is_Sigma p.
  Axiom Sigma_eqb_correct : forall p1 p2, Sigma_eqb p1 p2 -> p1 = p2.
  Axiom Sigma_eqb_refl : forall x, Sigma_eqb x x.

  Elpi derive.eqbOK.register_axiom Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
  Lemma Sigma_eqb_OK : Equality.axiom Sigma_eqb.
  apply: iffP2 Sigma_eqb_correct Sigma_eqb_refl.
  Qed.
  HB.instance Definition _ : hasDecEq Sigma := hasDecEq.Build Sigma Sigma_eqb_OK.

  Axiom same_subst : forall (s1 s2 : Sigma), s1 = s2.
  Axiom same_progr : forall (s1 s2 : program), s1 = s2.


  Inductive state :=
    | KO : state
    | OK : (*Sigma ->*) state
    | Top : state
    | Bot : state
    (* | CutOut : state *)
    | Goal : program  -> A -> state
    | Or  : state -> Sigma -> state -> state               (* Or A s B := A is lhs, B is rhs, s is the subst from which launch B *)
    | And : (*Sigma ->*) state -> state -> state -> state  (* And A B0 B := A is lhs, B is rhs, B0 to reset B for backtracking *)
    .
  derive state.
  HB.instance Definition _ := hasDecEq.Build state state_eqb_OK.

  (* Notation "A ∧ B" := (And A B) (at level 13000).
  Notation "A ∨ B" := (Or A B) (at level 13000). *)

  Inductive expand_res :=
    | Expanded    of state
    | CutBrothers of state
    | Failure     of state
    | Solved      of Sigma & state.
  derive expand_res.
  HB.instance Definition _ := hasDecEq.Build expand_res expand_res_eqb_OK.


  Definition mkAnd A B0 r :=
    match r with
    | Failure B     => Failure     (And A B0 B)
    | Expanded B    => Expanded    (And A B0 B)
    | CutBrothers B => CutBrothers (And A B0 B)
    | Solved s B    => Solved s    (And A B0 B)
    end.

  Definition mkOr A sB er :=
    match er with
    | Failure B     => Failure  (Or A sB B)
    | Expanded B    => Expanded (Or A sB B)
    | CutBrothers B => Expanded (Or A sB B) (* for now this is the rightmost brother *)
    | Solved s B    => Solved s (Or A sB B)
    end.

    (* Maybe replace all cutout with bot, and remove the cutout constructor *)
  Fixpoint cut A :=
    match A with
    | OK => KO
    | KO => KO
    | Bot => KO
    | Goal _ _ | Top => KO
    | And A B0 B => And (cut A) (cut B0) (cut B)
    | Or A s B => Or (cut A) s (cut B)
    end.

  Fixpoint big_and pr (a : list A) : state :=
    match a with
    | [::] => Top
    | x :: xs => And (Goal pr x)  (big_and pr xs) (big_and pr xs)
    end.

  Fixpoint big_or_aux pr (r : R) (l : seq (Sigma * R)) : state :=
    match l with 
    | [::] => big_and pr r.(premises)
    | (s,r1) :: xs => Or (big_and pr r.(premises)) s (big_or_aux pr r1 xs)
    end.

  Definition big_or pr s t :=
    let l := F pr t s in
    if l is (s,r) :: xs then (Or KO s (big_or_aux pr r xs))
    else KO.

  Fixpoint expand s (A :state) : expand_res :=
    match A with
    (* meta *)
    | OK => Solved s OK
    | KO => Failure KO
    
    (* lang *)
    | Top              => Expanded OK
    | Bot              => Expanded KO
    | Goal _ Cut       => CutBrothers OK
    | Goal pr (Call t) => Expanded (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        match expand s A with
        | Solved s A    => Solved s  (Or A sB B)
        | Expanded A    => Expanded  (Or A sB B)
        | CutBrothers A => Expanded  (Or A sB (cut B))
        | Failure A     => Failure   (Or A sB B)
        end
    | And A B0 B =>
        match expand s A with
        | Solved s1 A   => mkAnd A B0   (expand s1 B)
        | Expanded A    => Expanded     (And A B0 B)
        | CutBrothers A => CutBrothers  (And A B0 B)
        | Failure A     => Failure      (And A B0 B)
        end
    end
  .

  Fixpoint reset (A : state) :=
    match A with
    | KO | OK | Top | Bot | Goal _ _ => A
    | And A B0 B => And (reset A) B0 B0
    | Or A s B => Or (reset A) s (reset B)
    end.

  Fixpoint success (A : state) : bool :=
    match A with
    | OK => true
    | Top | Bot | Goal _ _ | KO => false
    | And A _ B => success A && success B
    | Or A _ B => success A (*|| (failed A && success B)*)
    end.

  Fixpoint failed (A : state) : bool :=
    match A with
    | KO => true
    | Top | Bot | Goal _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    | Or A _ B => failed A (*&& failed B*)
    end.

  Fixpoint next_alt_aux inAnd (s : Sigma) (A : state) : option (Sigma * state) :=
    match A with
    | KO | OK => None
    | Top | Bot | Goal _ _ => if inAnd then None else Some (s, A)
    | And A B0 B =>
      match next_alt_aux true s B, next_alt_aux true s A with
      | None, None => None
      | None, Some (s, A) => Some (s, And A B0 B0) (* B0 è un grande and di ATOMI *)
      | Some (s, B), _ => Some (s, And A B0 B)
      end
    | Or A sB B => (* NOTE: B is a BIG_OR of BIG_AND of ATOM | Top, i.e. it is never been explored *)
        match next_alt_aux false s A with
        | None => Some (sB, B)
        | Some (sA, A) => Some (sA, Or A sB B)
        end
    end.

  Inductive next_alt : Sigma -> state -> option (Sigma * state) -> Prop :=
    | next_alt0 {s A}: next_alt_aux false s A = None -> next_alt s A None
    | next_alt1 {s s1 A A1}: next_alt_aux false s A = Some (s1, A1) -> ~ failed A1 -> next_alt s A (Some (s1, A1))
    | next_alt2 {s s1 s2 A A1 A2}: next_alt_aux false s A = Some (s1, A1) -> failed A1 -> next_alt_aux false s1 A1 = Some (s2, A2) -> next_alt s A (Some (s2, A2)).

  (* Definition next_alt A := next_alt_aux false A. *)

  (* Lemma next_alt_failed_and {b A B0 B}:
    next_alt_aux b (And A B0 B) = None ->
      next_alt_aux true A = None /\ next_alt_aux true B = None.
  Proof.
    case: A; try by move=> //=; case: next_alt_aux.
    + move=> A s C //=.
      case NA: next_alt_aux => //.
      case F: next_alt_aux => //.
      case F1: next_alt_aux => //.
    + move=> A C D //=.
      case NE: next_alt_aux => //.
      case NC: next_alt_aux => //.
      case NA: next_alt_aux => //.
  Qed. *)

  Inductive run_res := Done of Sigma & state | Failed of state.
  derive run_res.
  HB.instance Definition _ := hasDecEq.Build run_res run_res_eqb_OK.


  Inductive expanded : Sigma -> state -> run_res -> Prop :=
    | expanded_done {s s' A alt}   : expand s A = Solved s' alt  -> expanded s A (Done s' alt)
    | expanded_fail {s A B}        : expand s A = Failure B -> expanded s A (Failed B)
    | expanded_cut {s s' A B}      : expand s A = CutBrothers B -> expanded s B s' -> expanded s A s'
    | expanded_step {s s' A B}     : expand s A = Expanded B  -> expanded s B s' -> expanded s A s'.

  Inductive run : Sigma -> state -> run_res -> Prop :=
    | run_done {s s' A B}        : expanded s A (Done s' B) -> run s A (Done s' B)
    | run_fail {s A B}           : expanded s A (Failed B) -> next_alt s B None -> run s A (Failed B)
    | run_backtrack {s s' s'' A B C} : expanded s A (Failed B) -> next_alt s B (Some (s', C)) ->  run s' C s'' -> run s A s''.


  Lemma simpl_expand_or_solved {s s1 s2 A B C} :
    expand s1 (Or A s B) = Solved s2 C ->
      (exists A', expand s1 A = Solved s2 A' /\ C = Or A' s B).
  Proof.
    move=> //=; case X: expand => //= -[] /[subst2].
    by eexists; split.
  Qed.

  Lemma simpl_expand_or_cut {s s1 A B C} :
    expand s1 (Or A s B) = CutBrothers C -> False.
  Proof. move=> /=; case X: expand => //=; case Y: expand => //=. Qed.

  Lemma simpl_expand_or_fail {s s1 A B C} :
    expand s1 (Or A s B) = Failure C -> 
      exists A', expand s1 A = Failure A' /\ C = Or A' s B.
  Proof. by move=> /=; case X: expand => //= -[] /[subst1]; do 2 eexists. Qed.

  Lemma simpl_expand_or_expanded {s s1 A B C} :
    expand s1 (Or A s B) = Expanded C ->
      (exists A', expand s1 A = Expanded A' /\ C = Or A' s B) \/ 
      (exists A', expand s1 A = CutBrothers A' /\ C = Or A' s (cut B)).
      (* (exists A' B', expand s1 A = Failure A' /\ expand s B = Expanded B' /\ Or A' s B' = C) \/
      (exists A' B', expand s1 A = Failure A' /\ expand s B = CutBrothers B' /\ Or A' s B' = C). *)
  Proof.
    move=> /=; case X: expand => //=.
    + by move=> [] ?; left; eexists.
    + by move=> [] /[subst1]; right; eexists.
    (* + case Y: expand => //=.
      + by move=> [] /[subst1]; right; right; left; do 2 eexists.
      + by move=> [] /[subst1]; right; right; right; do 2 eexists. *)
  Qed.

  Lemma simpl_expand_and_solved {s s2 A B0 B C} :
    expand s (And A B0 B) = Solved s2 C -> 
      exists s' A' B', 
        expand s A = Solved s' A' /\
          expand s' B = Solved s2 B' /\ And A' B0 B' = C.
  Proof.
    move=> //=; case X: expand => //= [s' A'].
    case Y: expand => //= [s'' B'].
    move=> [] /[subst1] /[subst1].
    by do 3 eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_fail {s A B B0 C} :
    expand s (And A B0 B) = Failure C ->
      (exists A', expand s A = Failure A' /\ C = And A' B0 B) \/ 
        (exists s' A' B', expand s A = Solved s' A' /\  expand s' B = Failure B' /\ C = And A' B0 B').
  Proof.
    move=> //=; case X: expand => //=; auto.
    - by move=> [] /[subst1]; left; eexists.
    - by case Y: expand => //= -[] /[subst1]; right; do 3 eexists => //=; repeat split.
  Qed.

  Lemma simpl_expand_and_cut {s A B B0 C}:
    expand s (And A B0 B) = CutBrothers C ->
    (exists A', expand s A = CutBrothers A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = CutBrothers B' /\ C = And A' B0 B').
  Proof.
    move=> //=; case X: expand => //=.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right.
      by do 3 eexists; repeat split => //=.
  Qed.

  Lemma simpl_expand_and_expanded {s A B B0 C}:
    expand s (And A B0 B) = Expanded C ->
    (exists A', expand s A = Expanded A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = Expanded B' /\ C = And A' B0 B').
  Proof.
    move=> /=; case X: expand => //=.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right.
      by do 3 eexists; repeat split => //=.
  Qed.

  (* Lemma expand_solved_ok {s1 s2 A}:
    expand s1 A = Solved s2 OK -> False.
  Proof.
    elim: A s1 s2 => //.
    + by move=> pr [] ?? //= ?; case: F => //= [[] xs] //=.
    + move=> A IHA s B IHB s1 s2 /simpl_expand_or_solved [].
      + by move=> [] A' [] B' [IHA' [IHB']].
      + by move=> [A' [H]].
    + by move=> A IHA B IHB s1 s2 /simpl_expand_and_solved [s' [A' [B' [H1 [H2]]]]].
  Qed. *)

  Lemma expand_cb_OK {s1 A}:
    expand s1 A = CutBrothers OK -> (exists p, A = Goal p Cut).
  Proof.
    elim: A s1 => //.
    + move=> p [].
      by eexists.
    + move=> ?? //=.
    + by move=> A IHA s B IHB s1 /simpl_expand_or_cut.
    + move=> A IHA B IHB C IHC s1 /simpl_expand_and_cut [].
      + by move=> [A' [H]] /[subst1].
      + by move=> [s'[A'[B' [HA[HB]]]]] /[subst1].
  Qed.

  Lemma cut_cut_same {a}: cut (cut a) = cut a.
  Proof. 
    elim: a => //=.
    + by move=> ? H => //= s A H1; rewrite H H1.
    + by move=> ? H ? H1 ? H2; rewrite H H1 H2.
  Qed.

End Run.


Module AxiomUnif <: Unif.
  Parameter unify : Tm -> Tm -> Sigma -> option Sigma.
  Parameter matching : Tm -> Tm -> Sigma -> option Sigma.
End AxiomUnif.

Module ARun := Run(AxiomUnif).
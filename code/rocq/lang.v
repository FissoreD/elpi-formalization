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
    | Dead : state
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
    | Expanded    of Sigma & state
    | CutBrothers of Sigma & state
    | Failure     of state
    | Solved      of Sigma & state.
  derive expand_res.
  HB.instance Definition _ := hasDecEq.Build expand_res expand_res_eqb_OK.


  Definition mkAnd (s: Sigma) A B0 r :=
    match r with
    | Failure B    => Failure       (if B == Dead then Dead else And A B0 B)
    | Expanded s B    => Expanded    s (And A B0 B)
    | CutBrothers s B => CutBrothers s (And A B0 B)
    | Solved s B      => Solved      s (And A B0 B)
    end.

  Definition mkOr sB er :=
    match er with
    | Failure B    => Failure     (if B == Dead then Dead else (Or Dead sB B))
    | Expanded s B    => Expanded s  (Or Dead sB B)
    | CutBrothers s B => Expanded s  (Or Dead sB B)
    | Solved s B      => Solved   s  (Or Dead sB B)
    end.

  (* Fixpoint const E A :=
    match A with
    | Dead => Dead
    | OK | KO | Bot | Goal _ _ | Top => E
    | And A B0 B => And (const E A) (const E B0) (const E B)
    | Or A s B => Or (const E A) s (const E B)
    end. *)

  Fixpoint dead A :=
    match A with
    | Dead => Dead
    | OK | KO | Bot | Goal _ _ | Top => Dead
    | And A B0 B => And (dead A) B0 B
    | Or A s B => Or (dead A) s (dead B)
    end.

    (* Maybe replace all cutout with bot, and remove the cutout constructor *)
  Fixpoint cut A :=
    (* if A == dead A then Dead else *)
    match A with
    | Dead => Dead
    | OK | KO | Bot | Goal _ _ | Top => KO
    | And A B0 B => And (cut A) B0 B
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

  Definition get_state r := match r with 
    | Failure A | Solved _ A | CutBrothers _ A | Expanded _ A => A 
  end.


  Fixpoint expand s (A :state) : expand_res :=
    match A with
    (* meta *)
    | OK => Solved s OK
    | KO => Failure KO

    (* meta *)
    | Dead => Failure Dead
    
    (* lang *)
    | Top              => Expanded s OK
    | Bot              => Expanded s KO
    | Goal _ Cut       => CutBrothers s OK
    | Goal pr (Call t) => Expanded s (big_or pr s t)

    (* recursive cases *)
    | Or A sB B =>
        match expand s A with
        | Solved s A    => Solved s      (Or A sB B)
        | Expanded s A    => Expanded s  (Or A sB B)
        | CutBrothers s A => Expanded s  (Or A sB (cut B))
        | Failure Dead  => mkOr sB        (expand s B)

        | Failure A     => Failure       (Or A sB B)
        end
    | And A B0 B =>
        match expand s A with
        | Solved s1 A   => mkAnd s1 A B0    (expand s1 B)
        | Expanded s A    => Expanded s     (And A B0 B)
        | CutBrothers s A => CutBrothers s  (And A B0 B)
        | Failure Dead => Failure Dead
        | Failure A     => Failure          (And A B0 B)
        end
    end
  .

  Fixpoint success (A : state) : bool :=
    match A with
    | OK => true
    | Top | Bot | Goal _ _ | KO | Dead => false
    | And A _ B => success A && success B
    | Or A _ B => if A == dead A  then success B else success A
    end.


  Fixpoint failed (A : state) : bool :=
    match A with
    | KO | Dead => true
    | Top | Bot | Goal _ _ | OK => false
    | And A _ B => failed A || (success A && failed B)
    | Or A _ B => if A == dead A then failed B else failed A (*&& failed B*)
    end.

  Lemma failed_success A: failed A -> success A = false.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; case: eqP => [_ /HB| _ /HA].
    + by move=> A HA B0 _ B HB /= /orP [/HA|/andP [-> /HB]] ->.
  Qed.

  Lemma success_failed A: success A -> failed A = false.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; case: eqP => [_ /HB| _ /HA].
    + by move=> A HA B0 _ B HB /= /andP[] /[dup] /HA -> ->/HB ->.
  Qed.

  Lemma dead_failed {A} : A = dead A -> failed A.
  Proof. elim: A => //.
    + by move=> A HA s B HB /= [] /HA -> /HB -> ; rewrite if_same.
    + by move=> A HA B0 HB0 B HB /= [] /HA ->.
  Qed.

  Lemma failed_dead {A} : failed A = false -> A <> dead A.
  Proof. elim: A => //.
    + move=> A HA s B HB /=; case: eqP.
      + move=> <- /HB H [] //.
      + move=> H _ [] //.
    + move=> A HA B0 HB0 B HB /= /orP H [] H1; apply H.
      by left; apply: dead_failed H1.
  Qed.


  Fixpoint next_alt_aux inAnd (s : Sigma) (A : state) : option (Sigma * state) :=
    match A with
    | KO | OK => None
    | Dead => None
    | Top | Bot | Goal _ _ => if inAnd then None else Some (s, A)
    | And A B0 B =>
      match next_alt_aux true s B, next_alt_aux true s A with
      | None, None => None
      | None, Some (s, A) => Some (s, And A B0 B0) (* B0 è un grande and di ATOMI *)
      | Some (s, B), _ => Some (s, And A B0 B)
      end
    | Or Dead sB B => 
          match next_alt_aux false s B with
          | None | Some (_, Dead) => None
          | Some (sB1, B) => Some (sB1, Or Dead sB B)
          end
    | Or A sB B => (* NOTE: B is a BIG_OR of BIG_AND of ATOM | Top, i.e. it is never been explored *)
        match next_alt_aux false s A with
        | None =>  Some (sB, Or Dead sB B)
        | Some (sA, A) => Some (sA, Or A sB B)
        end
    end.

  Inductive next_alt : Sigma -> state -> option (Sigma * state) -> Prop :=
    | next_alt_ko {s A}: next_alt_aux false s A = None -> next_alt s A None
    | next_alt_ok {s s1 A A1}: next_alt_aux false s A = Some (s1, A1) -> ~ failed A1 -> next_alt s A (Some (s1, A1))
    | next_alt_step {s s1 r A A1}: next_alt_aux false s A = Some (s1, A1) -> failed A1 -> next_alt s1 A1 r -> next_alt s A r.

  Inductive run_res := Done of Sigma & state | Failed of state.
  derive run_res.
  HB.instance Definition _ := hasDecEq.Build run_res run_res_eqb_OK.


  Inductive expandedb : Sigma -> state -> run_res -> bool -> Prop :=
    | expanded_done {s s' A alt}     : expand s A = Solved s' alt  -> expandedb s A (Done s' alt) false
    | expanded_fail {s A B}          : expand s A = Failure B -> expandedb s A (Failed B) false
    | expanded_cut {s s' r A B b}      : expand s A = CutBrothers s' B -> expandedb s' B r b -> expandedb s A r true
    | expanded_step {s s' r A B b}     : expand s A = Expanded s' B  -> expandedb s' B r b -> expandedb s A r b.

  Inductive runb : Sigma -> state -> run_res -> bool -> Prop :=
    | run_done {s s' A B b}        : expandedb s A (Done s' B) b -> runb s A (Done s' B) b
    | run_fail {s A B b}           : expandedb s A (Failed B) b -> next_alt s B None -> runb s A (Failed B) b
    | run_backtrack {s s' s'' A B C b1 b2 b3} : expandedb s A (Failed B) b1 -> next_alt s B (Some (s', C)) ->  runb s' C s'' b2 -> b3 = (b1 || b2) -> runb s A s'' b3.

  Definition expanded s A r := exists b, expandedb s A r b.
  Definition run s A r := exists b, runb s A r b.

  Definition run_classic s A r := runb s A r false. 
  Definition expanded_classic s A r := expandedb s A r false. 

  Lemma simpl_expand_or_solved {s s1 s2 A B C} :
    expand s1 (Or A s B) = Solved s2 C ->
      (exists A', expand s1 A = Solved s2 A' /\ C = Or A' s B) \/
      (exists B', expand s1 A = Failure Dead /\ expand s1 B = Solved s2 B' /\ C = Or Dead s B').
  Proof.
    move=> //= ; case X: expand => //= [x |].
    case: x X => //= => X ; case Y: (expand s1 B) => // -[].
      by move=> /[subst2]; right; eexists.
    by move=> -[] /[subst2]; left; eexists.
  Qed.

  Lemma simpl_expand_or_cut {s s1 s2 A B C} :
    expand s1 (Or A s B) = CutBrothers s2 C -> 
      exists s1 B', A = Dead /\ expand s B = CutBrothers s1 B' /\ C = Or Dead s1 B'.
  Proof. move=> /=; case X: expand => //= [[ ]] //; case Y: expand => //= [[ ]] //. Qed.

  Lemma simpl_expand_or_fail {s s1 A B C} :
    expand s1 (Or A s B) = Failure C -> 
      (exists A', expand s1 A = Failure A' /\ A' <> Dead /\ C = Or A' s B) \/
      (exists B', B' <> Dead /\ expand s1 A = Failure Dead /\ expand s1 B = Failure B' /\ C = Or Dead s B') \/
      (expand s1 A = Failure Dead /\ expand s1 B = Failure Dead /\ C = Dead).
  Proof. 
    move=> /=; case X: expand => //= [D] H.
    have {}H: D = Dead /\ mkOr s (expand s1 B) = Failure C \/ (D <> Dead /\ Failure (Or D s B) = Failure C).
      case: D H {X}; try by move=> [] /[subst1]; right => // .
      by move=> ->; left.
    move: H => []; subst.
      + move=> [/[subst1]]; case Y: expand => //= [D] H.
        have {H} [[] | []]: (D = Dead /\ C = Dead) \/ (D <> Dead /\ Or Dead s D = C).
          move: H; case: D {Y}; try by move=> [] /[subst1]; right => //.
          + move=> [] <-; left => //.
          + by move=> ?? [] <-; right.
          + by move=> ??? [] <-; right. 
          + by move=> ??? [] <-; right.
        + by move=> /[subst2]; right; right; eexists.
        + move=> H /[subst1]; right; left; eexists; repeat split; eassumption.
      + move=> [H [/[subst1]]]; left; eexists; repeat split => //.
  Qed.

  Lemma simpl_expand_or_expanded {s s1 s2 A B C} :
    expand s1 (Or A s B) = Expanded s2 C ->
      (exists A', expand s1 A = Expanded s2 A' /\ Or A' s B = C) \/ 
      (exists A', expand s1 A = CutBrothers s2 A' /\ C = Or A' s (cut B)) \/
      (expand s1 A = Failure Dead /\ (exists B', C = Or Dead s B' /\ (expand s1 B = Expanded s2 B' \/ expand s1 B = CutBrothers s2 B'))).
  Proof.
    move=> /=; case X: expand => //= [||[ ]] //.
    + move=> [] ?; left; eexists; split; subst; reflexivity.
    + by move=> [] /[subst1]; right; left; eexists.
    + case Y: expand => // -[] /[subst2] ; right; right ; repeat split;  eexists ; repeat split ; [left|right] => //.
  Qed.

  Lemma simpl_expand_and_solved {s s2 A B0 B C} :
    expand s (And A B0 B) = Solved s2 C -> 
      exists s' A' B', 
        expand s A = Solved s' A' /\
          expand s' B = Solved s2 B' /\ And A' B0 B' = C.
  Proof.
    move=> //=; case X: expand => //= [[]|s' A'] //.
    case Y: expand => // [s'' B'].
    move=> [] /[subst1] /[subst1].
    by do 3 eexists; repeat split.
  Qed.

  Lemma simpl_expand_and_fail {s A B B0 C} :
    expand s (And A B0 B) = Failure C ->
      (expand s A = Failure Dead /\ C = Dead) \/ 
      (exists A', A' <> Dead /\ expand s A = Failure A' /\ C = And A' B0 B) \/ 
        (exists s' A' B', expand s A = Solved s' A' /\  
          expand s' B = Failure B' /\ C = if B' == Dead then Dead else And A' B0 B').
  Proof.
    move=> //=; case X: expand => //= [D|s' D].
    - move=> H.
      have {H} : (((D != Dead) && (Failure C == Failure (And D B0 B)) || (D == Dead) && (Failed C == Failed Dead))).
        case: D H {X} => //=; try by move=> [] <-; rewrite eq_refl.
        + by move=> ?? [] <-; rewrite eq_refl.
        + by move=> ??? [] <-; rewrite eq_refl.
        + by move=> ??? [] <-; rewrite eq_refl.
      move=> /orP [/andP|/andP] [] /eqP H /eqP [] ->.
      + by right;left; exists D; auto.
      + by move=> /[subst]; auto.
    - case Y: expand => //= [[ ]]-[]<-; right; right; do 3 eexists; erewrite Y => //.
  Qed.

  Lemma simpl_expand_and_cut {s s2 A B B0 C}:
    expand s (And A B0 B) = CutBrothers s2 C ->
    (exists A', expand s A = CutBrothers s2 A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = CutBrothers s2 B' /\ C = And A' B0 B').
  Proof.
    move=> //=; case X: expand => //= [|[]|] //.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right; subst.
       do 3 eexists; repeat split => //=.
       apply Y.
  Qed.

  Lemma simpl_expand_and_expanded {s s2 A B B0 C}:
    expand s (And A B0 B) = Expanded s2 C ->
    (exists A', expand s A = Expanded s2 A' /\ C = And A' B0 B ) \/
      (exists s' A' B', expand s A = Solved s' A' /\ expand s' B = Expanded s2 B' /\ C = And A' B0 B').
  Proof.
    move=> /=; case X: expand => //= [|[]|] //.
    + by move=> [] /[subst1]; left; eexists.
    + case Y: expand => //= -[] /[subst1]; right; subst.
      do 3 eexists; repeat split => //=; eassumption.
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

  Lemma expand_cb_OK {s1 s2 A}:
    expand s1 A = CutBrothers s2 OK -> (exists p, A = Goal p Cut).
  Proof.
    elim: A s1 => //.
    + move=> p [].
      by eexists.
    + move=> ?? //=.
    + move=> A IHA s B IHB s1 /simpl_expand_or_cut => -[s3[B'[?[]]]] //.
    + move=> A IHA B IHB C IHC s1 /simpl_expand_and_cut [].
      + by move=> [A' [H]] /[subst1].
      + by move=> [s'[A'[B' [HA[HB]]]]] /[subst1].
  Qed.

  Lemma dead_dead_same {A}: dead (dead A) = dead A.
  Proof.
    elim: A => //.
    by move=> A HA s B HB /=; rewrite HA HB.
    by move=> A HA B0 HB0 B HB /=; rewrite HA.
  Qed.

  (* Lemma cut_dead {A}: cut A = dead (cut A) -> dead A = A.
  Proof.
    elim: A=> //.
    + move=> A HA s B HB /=; case X: eq_op => /=.
      + by move: X => /eqP [] -> -> _; rewrite !dead_dead_same.
      + move=> [] /HA {}HA /HB {}HB; congruence.
    + move=> A HA B0 HB0 B HB /=; case X: eq_op => /=.
      + by move: X => /eqP [] <-.
      + by move=> [] /HA ->.
  Qed. *)

  Lemma cut_cut_same {a}: cut (cut a) = cut a.
  Proof.
    elim: a => //=.
    + move=> A HA s B HB.
      (* case X: eq_op => //=. *)
      by move=> /=; rewrite HA HB.
      (* case Y: eq_op => //=.
      exfalso.
      move: Y X => /eqP [] Y1 Y2 /eqP X; apply: X.
      by rewrite (cut_dead Y1) (cut_dead Y2). *)
    + move=> A HA B0 HB0 B HB.
      (* case X: eq_op => //=. *)
      by move=> /=; rewrite HA.
      (* case Y: eq_op => //=.
      exfalso.
      by move: Y X => /eqP [] /cut_dead ->; rewrite eq_refl. *)
  Qed.

  Lemma cut_dead_is_dead {A}: cut(dead A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA.
  Qed.

  Lemma dead_cut_is_dead {A}: dead(cut A) = dead A.
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA.
  Qed.

  Definition is_meta X := match X with OK | KO | Dead => true | _ => false end.
  Definition is_base X := match X with Top | Bot | Goal _ _ => true | _ => false end.

  (* Lemma simpl_next_alt_aux_false {s1 s2 A B r}: 
    next_alt_aux false s1 (Or A s2 B) = Some r -> 
      (is_meta A /\ r = (s2, Or Dead s2 B)) \/ (is_base A /\ r = (s1, Or A s2 B)) \/
      (A = And X Y0 Y /\).
  Proof.
    case X: A ; try by move=> // [] /[subst1]; left.
    + move=> [] ?/[subst]; right => //. 
    + move=> [] ?/[subst]; right => //.
    + move=> [] ?/[subst]; right => //.
    + move=> /=; case Y: next_alt_aux; admit.
    + move=> /=; case Y: next_alt_aux => [[ ]|].
      + move=> [] ?.  *)

  Lemma next_alt_aux_dead {b s1 s3 A}: 
    next_alt_aux b s1 A = Some (s3, Dead) -> False.
  Proof.
    elim: A b s1 s3 => //; try by move=> [] => //.
    + move=> ?? [] //.
    + move=> A HA s B HB b s1 s3 + => /=.
      case NA: next_alt_aux => // [[s2 C]|].
      + case: A HA NA => //.
      + case: A HA NA => // HA HA'; case NB: next_alt_aux => [[s2 []]|] //.
    + move=> A HA B0 _ B HB s1 s3 + => /=.
      case NB: next_alt_aux => // [[s2 C]|].
      + move=> [] //.
      + case NA: next_alt_aux => // [[s2 C]] [] //.
  Qed. 

  Lemma next_alt_aux_none {s1 s2 A b}:
    next_alt_aux b s1 A = None ->
      next_alt_aux b s2 A = None.
  Proof.
    elim: A b s1 s2 => //; try by move=> []//.
    + move=> ?? [] //.
    + move=> A HA s B HB b s1 s2 /=.
      case X: next_alt_aux => [[s3 C]|].
      + by case: A X HA => //.
      + rewrite (HA _ _ s2 X); case A => //.
        case NB: next_alt_aux => [[? []]|] // _.
        + by have:= next_alt_aux_dead NB.
        + by rewrite (HB _ _ _ NB).
    + move=> A HA B0 _ B HB b s1 s2 /=.
      case NB: next_alt_aux => [[ ]|] //.
      case NA: next_alt_aux => [[ ]|] // _.
      by rewrite (HA _ _ _ NA) (HB _ _ _ NB).
  Qed.

  Lemma next_alt_aux_some {s1 s2 A B b}:
    next_alt_aux b s1 A = Some (s2, B) ->
      (forall s3, exists s4, next_alt_aux b s3 A = Some (s4, B)).
  Proof.
    elim: A b s1 s2 B => //.
    + by move=> [] => //= ??? [] /[subst2]; eexists.
    + by move=> [] => //= ??? [] /[subst2]; eexists.
    + by move=> ??[] // ??? [] /[subst2]; eexists.
    + move=> A HA s B HB b s1 s2 C; simpl next_alt_aux at 1 => H.
      have {H}: (
        (A = Dead /\
          match next_alt_aux false s1 B with
            | Some (sB1, Dead) => None
            | Some (sB1, KO as B) | Some (sB1, OK as B) | Some (sB1, Top as B) |
                Some (sB1, Bot as B) | Some (sB1, Goal _ _ as B) |
                Some (sB1, Or _ _ _ as B) | Some (sB1, And _ _ _ as B) =>
                Some (sB1, Or Dead s B)
            | None => None
            end = Some (s2, C)) \/ 
      (A <> Dead /\ 
        match next_alt_aux false s1 A with
          | Some (sA, A) => Some (sA, Or A s B)
          | None => Some (s, Or Dead s B) 
          end = Some (s2, C))).
      by case: A H {HA} => //=; auto; try by right.
      move=> [].
      + move=> [] /[subst1].
        case NB: next_alt_aux => // [[s3 D]] // H.
        have {H}: Some (s3, Or Dead s D) = Some (s2, C).
           by case: D H {NB} => //.
        move=> []/[subst2] s3 /=.
        have [s4 {}HB]:= HB _ _ _ _ NB s3.
        rewrite HB.
        by eexists; destruct D => //; have:= next_alt_aux_dead NB.
      + move=> [] HD; case NA: next_alt_aux => // [[s3 D]|] [] /[subst2] s5 /=.
        + have [s4 {}HB] := HA _ _ _ _ NA s5; rewrite HB; eexists; destruct A => //=.
        + rewrite (next_alt_aux_none NA); eexists; destruct A => //.
    + move=> A HA B0 _ B HB b s1 s2 C /= + s3.
      case NB: next_alt_aux =>  [[ ]|].
      + by move=> [] /[subst2]; have [? {}HB]:= HB _ _ _ _ NB s3; rewrite HB; eexists.
      + case NA': next_alt_aux => [[ ]|] // [] /[subst2].
        by have [? {}HA]:= HA _ _ _ _ NA' s3; rewrite HA (next_alt_aux_none NB); eexists.
  Qed.

  Lemma next_alt_none {s1 s2 D}:
    next_alt s1 D None -> next_alt s2 D None.
  Proof.
    remember None as RN eqn:HRN => H.
    elim: H s2 HRN => //; clear.
    + move=> s A NA s1 _; apply: next_alt_ko.
      apply: next_alt_aux_none NA.
    + move=> s1 s2 r A B NA FB NB + s3 ? /[subst] => /(_ _ erefl) H.
      have [? {}H1] := next_alt_aux_some NA s3.
      apply: next_alt_step H1 FB (H _).
  Qed.

  Lemma simpl_next_alt_aux_and_none {s A B0 B}:
    next_alt_aux true s (And A B0 B) = None -> next_alt_aux true s B = None /\  next_alt_aux true s A = None.
  Proof. 
    rewrite /next_alt //=. 
    case X: next_alt_aux => [x|].
    + by case x.
    + by case Y: next_alt_aux => [x|] //; case x.
  Qed.

  Lemma simpl_next_alt_aux_some {b s s1 s2 A B C}: next_alt_aux b s1 (Or A s B) = Some (s2, C) -> 
    (exists B', A = Dead /\ next_alt_aux false s1 B = Some (s2, B') /\ C = Or Dead s B') \/
    (exists A', A <> Dead /\ next_alt_aux false s1 A = Some (s2, A') /\ C = Or A' s B) \/
    (A <> Dead /\  next_alt_aux false s1 A = None /\ C = Or Dead s B).
  Proof.
    move=> //=.
    case X: (A == Dead).
    + move: X; move=> /eqP /[subst1].
      case X: next_alt_aux => // [[s3 D]].
      by destruct D => // -[] /[subst2]; left; eexists => //.
    + case Y: (next_alt_aux false s1 A) => // [[ ] |] H.
      + right; left; case: A Y X H; try by move=> // -[]/[subst2] _ []/[subst2]; eexists => //.
        + move=> ?? [] /[subst2] _ []/[subst2]; eexists => //.
        + move=> ??? _ _ []/[subst2]; eexists => //.
        + move=> ??? _ _ []/[subst2]; eexists => //.
      + right; right.
        destruct A => //; move: H => [] /[subst2] //.
  Qed.

End Run.


Module AxiomUnif <: Unif.
  Parameter unify : Tm -> Tm -> Sigma -> option Sigma.
  Parameter matching : Tm -> Tm -> Sigma -> option Sigma.
End AxiomUnif.

Module ARun := Run(AxiomUnif).  
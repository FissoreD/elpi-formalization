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
Elpi derive.eqb P.

Definition K := nat.
Elpi derive.eqb K.

Definition V := nat.
Elpi derive.eqb V.

Inductive C := 
  | p of P 
  | v of V
  .
Elpi derive.eqb option.
Elpi derive.eqb list.

Inductive Tm := 
  | Code : C -> Tm
  | Data : K -> Tm
  | Comb : Tm -> Tm -> Tm.
  (* | Lam  : V -> S -> Tm -> S -> Tm. *)
Record R_ {A} := { head : Tm; premises : list A }.
Inductive A :=
  | Cut
  | Call : Tm -> A.
  (* | PiImpl : V -> R_ A -> A -> A. *)
Notation R := (@R_ A).

Axiom Tm_eqb : Tm -> Tm -> bool.
Axiom Tm_eqb_ok : Equality.axiom Tm_eqb.
HB.instance Definition _ : hasDecEq Tm := hasDecEq.Build Tm Tm_eqb_ok.

Definition A_eqb (a b : A) :=
  match a,b with
  | Cut, Cut => true
  | Call t1, Call t2 => t1 == t2
  | _, _ => false
  end.
Lemma A_eqb_ok : Equality.axiom A_eqb.
Proof.
move=> [|t1] [|t2] => //=; try by constructor.
by apply: iffP eqP _ _; [ move-> | move=> [] ].
Qed.
HB.instance Definition _ : hasDecEq A := hasDecEq.Build A A_eqb_ok.

Definition Sigma := V -> option Tm.
Definition empty : Sigma := fun _ => None.

Axiom eqb_C : Sigma -> C -> C -> bool.

Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
Axiom matching : Tm -> Tm -> Sigma -> option Sigma.

Definition index := list R.
Definition mode_ctx := Tm -> list mode.
Definition sigT := Tm -> S.
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx; sig : sigT }.

(* Inductive goal := Goal of program & Sigma & A. *)

(* Axiom H : list mode -> Tm -> Tm -> Sigma -> option Sigma. *)
Fixpoint H (ml : list mode) (q : Tm) (h: Tm) s : option Sigma :=
  match ml,q,h with
  | [::], Code c, Code c1 => if eqb_C s c c1 then Some s else None
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

Inductive state :=
  | KO : state
  | OK : (*Sigma ->*) state
  | Goal : program  -> A -> state
  | Or  : state -> Sigma -> state -> state
  | And : (*Sigma ->*) state -> state -> state
  | CutOut : state
  .

Fixpoint state_eqb A B :=
  match A, B with
  | KO, KO | CutOut, CutOut | OK, OK => true
  | Goal _p1 a1, Goal _p2 a2 => A_eqb a1 a2  (* should also compare _p1 and _p2 *)
  | Or A1 sr1 B1, Or A2 sr2 B2 => state_eqb A1 A2 && state_eqb B1 B2 (* should also compare sr1 and sr2 *)
  | And A1 B1, And A2 B2 => state_eqb A1 A2 && state_eqb B1 B2
  | _, _ => false
  end.
Theorem state_eqb_ok : Equality.axiom state_eqb.
Proof.
  move=> s1; elim: s1; move=> [] //=; try by constructor.
Admitted.

HB.instance Definition _ : hasDecEq state := hasDecEq.Build state state_eqb_ok.

(* Notation "A ∧ B" := (And A B) (at level 13000).
Notation "A ∨ B" := (Or A B) (at level 13000). *)

Inductive expand_res :=
  | Expanded of state
  | CutBrothers of state
  | Failure
  | Solved of Sigma & state.

Definition mkAnd alt left r :=
  match r with
  | Failure => Failure
  | Expanded st => Expanded (And left st)
  | CutBrothers st => CutBrothers (And left st)
  | Solved s A => Solved s (And alt A)
  end.

(* alternative: mkOr always builds an Or *)
Definition mkOr left sr r :=
  match r with
  | Failure => Failure
  | Expanded st => Expanded (Or left sr st)
  | CutBrothers st => Expanded (Or left sr st) (* for now this is the rightmost brother *)
  | Solved s A => Solved s A
  end.

Fixpoint cut st :=
  match st with
  | Goal _ _ => CutOut
  | And x y => And (cut x) (cut y)
  | Or x s y => Or (cut x) s (cut y)
  | OK => CutOut
  | KO => KO
  | CutOut => CutOut
  end.


Lemma cut_cut_same {a}: cut (cut a) = cut a.
Proof. 
  elim: a => //=.
  + by move=> ? H => //= s A H1; rewrite H H1.
  + by move=> ? H ? H1; rewrite H H1.
Qed.

Fixpoint big_and_aux pr h (a : list A) : state :=
  match a with
  | [::] => Goal pr h
  | x :: xs => And (Goal pr h) (big_and_aux pr x xs)
  end.

(* A rule with premises is considered to fail *)
Definition big_and pr l :=
  match l with
  | [::] => KO
  | x::xs => big_and_aux pr x xs
  end. 

Fixpoint big_or pr (r : R) (l : seq (Sigma * R)) : state :=
  match l with 
  | [::] => big_and pr r.(premises)
  | (s,r1) :: xs => Or (big_and pr r.(premises)) s (big_or pr r1 xs)
  end.

Fixpoint expand s (A :state) : expand_res :=
  match A with
  | KO => Failure
  | OK => Solved s KO
  | CutOut => Failure
  | Goal _ Cut  => CutBrothers OK
  | Goal pr (Call t) =>
      let l := F pr t s in
      if l is (s,r) :: _ then Expanded (Or KO s (big_or pr r l))
      else Expanded KO
  | Or L sr R =>
      match expand s L with
      | Solved s A => Solved s (Or A sr R)
      | Expanded L => Expanded (Or L sr R)
      | CutBrothers L => Expanded (Or L sr (cut R))
      | Failure => mkOr L sr (expand sr R)
      end
  | And L R =>
      match expand s L with
      | Solved s1 r => mkAnd r L (expand s1 R)
      | Expanded L => Expanded (And L R)
      | CutBrothers L => CutBrothers (And L R)
      | Failure => Failure
      end
  end
.

Inductive run_res := Done of Sigma & state | Failed.

Inductive run : Sigma -> state -> run_res -> Prop :=
  | run_done {s s' A alt} : expand s A = Solved s' alt  -> run s A (Done s' alt)
  | run_fail {s A}  : expand s A = Failure   -> run s A Failed
  | run_cut {s s' A B} : expand s A = CutBrothers B -> run s B s' -> run s A s'
  | run_step {s s' A B} : expand s A = Expanded B  -> run s B s' -> run s A s'.

Inductive run_classic : Sigma -> state -> run_res -> Prop :=
  | run_classic_solved {s' s A alt} : expand s A = Solved s' alt -> run_classic s A (Done s' alt)
  | run_classic_fail {s A}  : expand s A = Failure   -> run_classic s A Failed
  | run_classic_step {s A B b}: expand s A = Expanded B -> run_classic s B b -> run_classic s A b.

Lemma simpl_expand_or_solved {s s1 s2 A B C} :
  expand s1 (Or A s B) = Solved s2 C ->
    (expand s1 A = Failure /\ expand s B = Solved s2 C) \/ (exists X, expand s1 A = Solved s2 X /\ C = Or X s B).
Proof.
  move=> //=; case X: expand => //=.
  + case Y: expand => //=; move=> [] /[subst2]; auto.
  + move=> [] /[subst2]; right; by eexists.
Qed.

Lemma simpl_expand_or_cut {s s1 A B C} :
  expand s1 (Or A s B) = CutBrothers C -> False.
Proof. move=> /=; case X: expand => //=; case Y: expand => //=. Qed.

Lemma simpl_expand_or_fail {s s1 A B} :
  expand s1 (Or A s B) = Failure -> expand s1 A = Failure /\ expand s B = Failure.
Proof. move=> /=; case X: expand => //=; case Y: expand => //=. Qed.

Lemma simpl_expand_or_expanded {s s1 A B C} :
  expand s1 (Or A s B) = Expanded C ->
    (exists A', expand s1 A = Expanded A' /\ C = Or A' s B) \/ 
    (exists A', expand s1 A = CutBrothers A' /\ C = Or A' s (cut B)) \/ 
    (exists B', expand s1 A = Failure /\ expand s B = Expanded B' /\ Or A s B' = C) \/
    (exists B', expand s1 A = Failure /\ expand s B = CutBrothers B' /\ Or A s B' = C).
Proof.
  move=> /=; case X: expand => //=.
  + by move=> [] ?; left; eexists.
  + by move=> [] /[subst1]; right; left; eexists.
  + case Y: expand => //=.
    + by move=> [] /[subst1]; right; right; left; eexists.
    + by move=> [] /[subst1]; right; right; right; eexists.
Qed.

Lemma simpl_expand_and_solved {s s2 L R K} :
  expand s (And L R) = Solved s2 K -> 
    exists s' L' R', 
      expand s L = Solved s' L' /\
        expand s' R = Solved s2 R' /\ And L' R' = K.
Proof.
  move=> //=; case X: expand => //=.
  case Y: expand => //=.
  move=> [] /[subst2].
  by do 3 eexists; repeat split.
Qed.

Lemma simpl_expand_and_fail {s L R} :
  expand s (And L R) = Failure ->
    expand s L = Failure \/ 
      (exists s' L', expand s L = Solved s' L' /\  expand s' R = Failure).
Proof.
  move=> //=; case X: expand => //=; auto.
  by case Y: expand => //=; right; do 2 eexists => //=.
Qed.

Lemma simpl_expand_and_cut {s A A' B}:
  expand s (And A B) = CutBrothers A' ->
  (exists A'', expand s A = CutBrothers A'' /\ A' = And A'' B ) \/
    (exists s' A'' B', expand s A = Solved s' A'' /\ expand s' B = CutBrothers B' /\ A' = And A B').
Proof.
  move=> //=; case X: expand => //=.
  + by move=> [] /[subst1]; left; eexists.
  + case Y: expand => //= -[] /[subst1]; right.
    by do 3 eexists; repeat split => //=.
Qed.

Lemma simpl_expand_and_expanded {s A B A'}:
  expand s (And A B) = Expanded A' ->
  (exists A'', expand s A = Expanded A'' /\ A' = And A'' B ) \/
    (exists s' A'' B', expand s A = Solved s' A'' /\ expand s' B = Expanded B' /\ A' = And A B').
Proof.
  move=> /=; case X: expand => //=.
  + by move=> [] /[subst1]; left; eexists.
  + case Y: expand => //= -[] /[subst1]; right.
    by do 3 eexists; repeat split => //=.
Qed.

Lemma expand_solve_ok {s1 s2 A}:
  expand s1 A = Solved s2 OK -> False.
Proof.
  elim: A s1 s2 => //.
  + by move=> pr [] ?? //= ?; case: F => //= [[] xs] //=.
  + move=> A IHA s B IHB s1 s2 /simpl_expand_or_solved [].
    + by move=> [] _; apply IHB.
    + by move=> [A' [H]].
  + by move=> A IHA B IHB s1 s2 /simpl_expand_and_solved [s' [A' [B' [H1 [H2]]]]].
Qed.

Goal expand empty (Or OK empty OK) = Solved empty (Or KO empty OK) . by []. Qed.
Goal forall p, run empty (Or (Goal p Cut) empty OK) (Done empty (Or KO empty CutOut)).
  move=> pr //=. apply: run_step => //=. by apply: run_done. Qed.
Goal forall p, 
  run empty (Or (Goal p Cut) empty (Or OK empty OK)) (Done empty (Or KO empty (cut ((Or OK empty OK))))).
  move=> p.
  apply: run_step => //=.
  apply: run_done => //=.
Qed.

Goal run empty (Or OK empty (Or OK empty OK)) (Done empty (Or KO empty (((Or OK empty OK))))).
Proof. apply: run_done => //=. Qed.

Lemma run_classic_run {s A r}:
  run_classic s A r -> run s A r.
Proof.
  move=> H; elim: H.
  + move=> ???? H; apply: run_done H.
  + move=> ?? H; apply: run_fail H.
  + move=> ???? H1 _ H3; apply: run_step H1 H3.
Qed.

Lemma run_classic_cut {s A B b}:
  run_classic s A b -> expand s A = CutBrothers B -> False.
Proof. by move=> H; elim: H B; congruence. Qed.


Lemma run_Solved_id {s s1 A r alt}:
    expand s A = Solved s1 alt -> run s A r -> r = Done s1 alt.
Proof.
  move=> + H; by case: H => //=; clear; congruence.
Qed.

Lemma run_Failure_and_Done {s s' A alt}:
  expand s A = Failure -> run s A (Done s' alt) -> False.
Proof. by inversion 2; subst; congruence. Qed.

Lemma run_consistent: forall {s0 A s1 s2},
  run s0 A s1 -> run s0 A s2 -> s1 = s2.
Proof.
  move=> s0 A s1 + H.
  elim:H; clear.
  + move=> s s' A alt H B H1.
    by move: (run_Solved_id H H1).
  + move=> s st st1 H H0.
    by inversion H0; congruence.
  + move=> s st st1 st2 + H1 IH H H2.
    inversion H2; subst; try congruence => //; rewrite H0 => -[]?; subst; by auto.
  + move=> s st st1 st2 + H1 IH B H2.
    inversion H2; subst; clear H2; try congruence; rewrite H0 => -[]?; subst; by auto.
Qed.

Lemma run_cut_simpl {pr s2 s3 alt}:
  run s3 (Goal pr Cut) (Done s2 alt) -> alt = KO.
Proof. by inversion 1; move: H1 => //= [] ?; subst; inversion H2; subst => //; move: H5 => [? ->]. Qed.

Lemma run_and_complete {s s' altAB A B} :
  run s (And A B) (Done s' altAB) ->
    (exists s'' altA altB, altAB = And altA altB /\ run s A (Done s'' altA) /\ run s'' B (Done s' altB)).
Proof.
  remember (And _ _) as g0 eqn:Hg0.
  remember (Done _ _) as s1 eqn:Hs1 => H.
  elim: H A B altAB Hg0 s' Hs1; clear => //=.
  - move=> s s' AB alt + A B alt' ? s'' [] ??; subst => //=.
    move=> /simpl_expand_and_solved. 
    move => [s' [A' [B']]] => -[H1 [H2 H3]]; subst.
    do 3 eexists; repeat constructor; eassumption.
  - move=> s s' ? B + H1 + A B' alt ? s'' ?; subst => //=.
    move=> /simpl_expand_and_cut [].
    - move=> [A'' [H H2]] /[subst].
      move=> /(_ _ _ _ erefl _ erefl) [s'[altA[altB[?[IHl IHr]]]]]; subst.
      do 3 eexists; repeat split => //=.
      by apply: run_cut H IHl.
      by apply: IHr.
    - move=> [s' [A' [B'' [H2 [H3 ?]]]]] /[subst].
      move=> /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [? [IHl IHr]]]]]; subst.
      move: (run_Solved_id H2 IHl) => [] /[subst2].
      do 3 eexists; repeat split => //=.
      - by apply: IHl.
      - apply: run_cut H3 IHr.
  - move=> s ? A' C + H1 + A B ? s' ??; subst => //=.
    move=> /simpl_expand_and_expanded [].
    - move=> [A' [H2]] /[subst1].
      move => /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [? [IHl IHr]]]]]; subst.
      do 3 eexists; repeat split => //=.
      by apply: run_step H2 IHl.
      by assumption.
    - move=> [s' [A' [B' [H2 [H3]]]]] /[subst1].
      move=> /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [?[IHl IHr]]]]]; subst.
      move: (run_Solved_id H2 IHl) => []??; subst.
      do 3 eexists; repeat split => //=.
      eassumption.
      by apply: run_step H3 IHr.
Qed.

Lemma run_and_correct {s0 s1 s2 A B altA altB} :
    run s0 A (Done s1 altA) -> run s1 B (Done s2 altB) ->
      run s0 (And A B) (Done s2 (And altA altB)).
Proof.
  remember (Done _ _) as D eqn:HD => H.
  elim: H altA s1 s2 B altB HD => //=; clear.
  + move=> + + + + + + s1' s2 B altB + H1.
    remember (Done s2 _) as D eqn:HD.
    elim: H1 s2 altB HD => //=; clear.
    + move=> s s' A altA H altB s2 [] ?? s0 s1 A' altA' H1 altA'' []??; subst.
      apply: run_done => //=; rewrite H1 H => //=.
    + move=> s s' A B H H1 IH s2 altB ? s0 s1 A' altA' H2 altA []??; subst.
      apply: run_cut => //=.
      + rewrite H2 H => //=.
      + apply: IH => //=.
      + eassumption.
    + move=> s ? A B H H1 IH s' ? s'' A' H2 A0 altA0 H3 altA'' [] ??; subst.
      apply: run_step => //=.
      + by rewrite H3 H.
      + by apply: IH erefl.
  + move=> s s' A CA H H1 IH altA s1 s2 B altB ? H2; subst.
    apply: run_cut => //=.
    + by rewrite H.
    + by apply: IH _ H2.
  + move=> s s' A AE H H1 IH altA s1 s2 B altB ? H2; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by apply: IH erefl H2.
Qed.

Lemma run_and_fail {s A B}:
  run s (And A B) Failed ->
    run s A Failed \/ (exists s' altA, run s A (Done s' altA) /\ run s' B Failed).
Proof.
  move=> H.
  remember (And _ _) as R eqn:HR.
  remember Failed as F eqn:HF.
  elim: H A B HR HF => //=; clear.
  + move=> s A + A1 B2 ? _; subst => /simpl_expand_and_fail [].
    + by move=> H; left; apply: run_fail.
    + move=> [s' [L' [H1 H2]]]; right.
      do 2 eexists; split.
      - apply: run_done H1.
      - by apply run_fail.
  + move=> s s' A B + H1 IH A1 B1 ? ?; subst => /simpl_expand_and_cut [].
    - move=> [A'' [H2]] /[subst1].
      move: (IH _ _ erefl erefl) => [].
      + by left; apply: run_cut H2 _.
      + move=> [] s' [] altA [] H4 H5.
        right; do 2 eexists; split; [|eassumption]; apply: run_cut H2 H4.
    - move=> [s' [A2 [B' [H2 [H3]]]]] /[subst1].
      move: (IH _ _ erefl erefl) => []; [by auto|].
      move=> [] s'' [] altA [] H4 H5.
      move: (run_Solved_id H2 H4) => []?; subst.
      right; repeat eexists; [eassumption|apply: run_cut H3 H5].
  + move=> s s' A B + H1 IH A1 B1 ??; subst => //=.
    move=> /simpl_expand_and_expanded [].
    + move=> [A'' [H]] /[subst1].
      move: (IH _ _ erefl erefl) => [] {IH}.
      + by left; apply: run_step H _.
      + move=> [] ? [] altA [] H2 H3.
        by right; repeat eexists; [apply: run_step H H2|].
    + move=> [s' [A2 [B' [H2 [H3]]]]] /[subst1].
      move: (IH _ _ erefl erefl) => [] {IH}; [by auto|].
      move=> [] ? [] altA [] H4 H5.
      move: (run_Solved_id H2 H4) => []?; subst.
      right; repeat eexists; [by eassumption|].
      by apply: run_step H3 H5.
Qed.

Lemma run_and_fail_left {s A}:
  run s A Failed ->
    forall B, run s (And A B) Failed.
Proof.
  move=> H.
  remember Failed as F eqn:HF.
  elim: H HF => //=; clear.
  + move=> s A H _ B2.
    by apply: run_fail => //=; rewrite H.
  + move=> s s' A B H H1 IH B1 ?; subst => //=.
    apply: run_cut => //=.
    + by rewrite H.
    + by auto.
  + move=> s s' A B H H1 IH B1 ?; subst => //=.
    apply: run_step => //=.
    + by rewrite H.
    + by auto.
Qed.

Lemma run_and_fail_both {s s' A B alt}:
  run s A (Done s' alt) -> run s' B Failed ->
    run s (And A B) Failed.
Proof.
  move=> H.
  remember (Done _ _) as D eqn:HD.
  elim: H B s' alt HD => //=; clear.
  + move=> + + + + + B s + + H.
    remember Failed as F eqn:HF.
    elim: H HF => //=; clear.
    + move=> s A H _ s1 s2 A1 alt H1 alt1 [] ??;subst.
      by apply: run_fail => //=; rewrite H1 H.
    + move=> s s' A B H H1 IH ? s1 s2 a1 alt H3 alt1 []??; subst.
      apply: run_cut => //=.
      + rewrite H3 H => //=.
      + apply: IH => //=.
        apply: H3.
    + move=> s s' A B H H1 IH ? s1 s2 a1 alt H3 alt1 []??; subst.
      apply: run_step => //=.
      + by rewrite H3 H.
      + apply: IH => //=.
        apply: H3.
  + move=> s s' A B H H1 IH B1 s1 alt ? H2; subst => //=.
    apply: run_cut => //=.
    + by rewrite H.
    + apply: IH => //=.
  + move=> s s' A B H H1 IH B1 s1 alt ? H2; subst => //=.
    apply: run_step => //=.
    + by rewrite H.
    + apply: IH => //=.
Qed.

Lemma run_classic_expandedR {s1 A B b}:
  expand s1 A = Expanded B -> 
    run_classic s1 A b ->
        run_classic s1 B b.
Proof.
  move=> + H.
  elim: H B => //=; [congruence | congruence | ]; clear.
  by move=> s A B b H H1 IH B1 +; rewrite H => -[] ?; subst.
Qed.

Lemma expand_cut_failure {s A}: expand s (cut A) = Failure.
Proof.
  elim: A s => //=; clear.
  - by move => A IHl s1 B IHr s2; rewrite IHl IHr.
  - by move => A IHl B IHr s2; rewrite IHl.
Qed.

Axiom classic : forall P : Prop, P \/ ~ P.

Lemma run_cut_fail {s s' A altA} :
  run s (cut A) (Done s' altA) -> False.
Proof.
  inversion 1; subst.
  + by rewrite expand_cut_failure in H4. 
  + by rewrite expand_cut_failure in  H1.
  + by rewrite expand_cut_failure in  H1.
Qed.

Lemma run_classic_failure_split {s A B}: 
  run_classic s (And A B) Failed ->
    (run_classic s A Failed) \/ 
      (exists s' altA, run s A (Done s' altA) /\ run_classic s' B Failed).
Proof.
  remember (And A B) as And eqn:HAnd.
  remember Failed as F eqn:HF.
  move=> H; elim: H A B HAnd HF; clear => //=.
  + move=> s A + A1 B /[subst1] /simpl_expand_and_fail [].
    + by left; apply: run_classic_fail.
    + move=> [s' [L' [H1 H2]]]; right; repeat eexists.
      + apply: run_done H1.
      + by apply: run_classic_fail.
  + move=> s st st1 b + H1 + A B /[subst2] /simpl_expand_and_expanded [].
    + move=> [A' [H2]] /[subst1].
      move=> /(_ _ _ erefl erefl) => -[].
      + move=> H; left; apply: run_classic_step H2 H.
      + move=> [X1 [altA [H3 H4]]]; right.
        repeat eexists.
        + apply: run_step H2 H3.
        + apply: H4.
    + move=> [s' [A' [B' [HA [HB]]]]] /[subst1].
      move=> /(_ _ _ erefl erefl) [].
      + by left.
      + move=> [s'' [altA [H2 H3]]]; right.
        repeat eexists; try eassumption.
        inversion H2; subst; try congruence; clear H2.
        move: H6; rewrite HA => -[]??; subst.
        by apply: run_classic_step HB H3.
Qed.

Lemma run_or_done_cut {s1 s2 SOL A B altA}:
  run s1 A (Done SOL altA) ->
  run s1 (Or A s2 (cut B)) (Done SOL (Or altA s2 (cut B))).
Proof.
  remember (Done _ _) as D eqn:HD.
  move=> H.
  elim: H altA s2 SOL B HD; clear => //=.
  + move=> s st s' alt H altA s2 SOL B [] ??; subst.
    by apply: run_done => //=; rewrite H.
  + move=> s st st1 st2 H H1 IH s2 SOL B H2 ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by rewrite cut_cut_same; apply: IH erefl.
  + move=> s st st1 st2 H H1 IH s2 SOL B0 ??; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by apply: IH.
Qed.

Lemma run_or_correct_left {s s' A altA}:
  run s A (Done s' altA) ->
    forall s2 B, exists altB, run s (Or A s2 B) (Done s' (Or altA s2 altB)).
Proof.
  remember (Done _ _) as D eqn:HD => H.
  elim: H s' altA HD => //=; clear.
  + move=> s st s' alt H s'' altA [] ?? s2 B; subst.
    by eexists; apply: run_done => //=; rewrite H.
  + move=> s A st1 st2 H H1 IH s' altA ? s2 B; subst.
    eexists; apply: run_step => //=.
    + by rewrite H.
    + by apply: run_or_done_cut H1.
  + move=> s st st1 st2 H H1 IH s' altA ? s2 B; subst.
    move: (IH s' altA erefl s2 B) => [altB H2].
    eexists; apply: run_step _ H2 => //=.
    by rewrite H.
Qed. 

Lemma run_or_correct_right {s1 s2 s3 A B altB}:
  run_classic s1 A Failed -> run s2 B (Done s3 altB) ->
    (run s1 (Or A s2 B) (Done s3 altB)).
Proof.
  remember Failed as F eqn:HF.
  move=> H.
  elim: H HF s2 B altB s3; clear => //=.
  + move=> + + + _ s2 B altB s3 H1.
    remember (Done s3 _) as DS eqn:HDS.
    elim: H1 altB s3 HDS => //=; clear.
    + move=> s2 s3 B altB H s3' s4 [] ?? s1 A H1; subst.
      by apply: run_done =>//=; rewrite H1 H.
    + move=> s2 s' B BC H H1 + s3 A ? s1 A' H2; subst.
      move=> /(_ _ _ erefl _ _ H2) IH.
      apply: run_step _ IH => //=.
      by rewrite H2 H.
    + move=> s2 s' B BE H H1 + altB s3 ? s1 A H2; subst.
      move=> /(_ _ _ erefl _ _ H2) IH.
      apply: run_step _ IH => //=.
      by rewrite H2 H.
  + move=> s1 A EA ? H H1 + ? s2 B altB B' H2; subst.
    move=> /(_ erefl _ _ _ _ H2) => IH.
    apply: run_step _ IH => //=.
    by rewrite H.
Qed.

Lemma run_or_correct {s1 s2 A B SOL altA altB}:
  (run s1 A (Done SOL altA)) \/ 
    (run_classic s1 A Failed /\ run s2 B (Done SOL altB)) ->
      exists altAB, run s1 (Or A s2 B) (Done SOL altAB).
Proof.
  move=> [].
  + move=> H; move: (run_or_correct_left H s2 B) => [altB1 H1]; eexists; apply H1.
  + by move=> [] H1 H2; move: (run_or_correct_right H1 H2); exists altB.
Qed.

Lemma run_and_done {s A B SOL r}:
  run s (And A B) (Done SOL r) -> exists x y, r = And x y.
Proof.
  remember (And _ _) as O eqn:HO.
  remember (Done _ _) as D eqn:HD.
  move=> H.
  elim: H A B SOL HO HD; clear => //=.
  + move=> s s' A altA + A' B H SOL [] ??; subst => //=.
    move=> /simpl_expand_and_solved [s' [L [R [H1 [H2]]]]] /[subst1].
    by do 2 eexists.
  + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
    move=> /simpl_expand_and_cut [].
    + by move=> [? [?]] /[subst1]; apply: IH erefl erefl.
    + by move=> [?[?[?[?[?]]]]] /[subst1]; apply: IH erefl erefl.
  + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
    move=> /simpl_expand_and_expanded [].
    + by move=> [?[?]] /[subst1]; apply: IH erefl erefl.
    + by move=> [?[?[?[?[?]]]]] /[subst1]; apply: IH erefl erefl.
Qed.

Lemma run_or_complete {s1 s2 A B SOL altAB}:
  run s1 (Or A s2 B) (Done SOL altAB) ->
    (exists altA, run s1 A (Done SOL altA)) \/ 
      (exists altB, run_classic s1 A Failed /\ run s2 B (Done SOL altB)).
Proof.
  remember (Or _ _ _) as O1 eqn:HO1.
  remember (Done _ _) as D eqn:HD.
  move=> H.
  elim: H s2 A B altAB SOL HO1 HD; clear => //=.
  + move=> s st s' alt + s2 A B altAB SOL ? [] /[subst2] /simpl_expand_or_solved [].
    + move=> [HA HB].
      right; eexists; repeat split.
      + apply: run_classic_fail HA.
      + apply: run_done HB.
    + move=> [X [HA HB]]; left.
      eexists; apply: run_done HA.
  + by move=> s ? st1 st2 + H1 IH s2 A B altAB SOL /[subst2] /simpl_expand_or_cut.
  + move=> s ? st1 st2 + H1 IH s2 A B altAB SOL /[subst2] /simpl_expand_or_expanded [|[|[|]]].
    + move=> [A' [HA]] /[subst1].
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[altA[HL HR]]].
      - left; eexists; apply: run_step HA H.
      - right; eexists; split; [apply: run_classic_step HA HL|apply: HR].
    + move=> [A' [HA]] /[subst1].
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[?[HL HR]]].
      - by left; eexists; apply: run_cut HA H.
      - by move: (run_cut_fail HR).
    + move=> [B' [HA [HB]]] /[subst1].
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[?[HL HR]]].
      by destruct (run_Failure_and_Done HA H).
      right; eexists; split; auto; apply: run_step HB HR.
    + move=> [B' [HA [HB]]] /[subst1].
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[? [HL HR]]].
      by destruct (run_Failure_and_Done HA H).
      right; eexists; split; auto; apply: run_cut HB HR.
Qed.

Lemma run_run_classic_failure {s A} : 
  run_classic s A Failed -> 
    run s A Failed.
Proof.
  remember Failed as F eqn:HF.
  move=> H; elim: H HF; clear => //=.
  + move=> ?? H _; by apply: run_fail H.
  + by move=> ???? H H1 H2 ?; subst; apply: run_step H (H2 _).
Qed.

Lemma run_or_fail {s1 s2 A B b}:
  run s1 (Or A s2 B) Failed ->
    run s1 A Failed /\ (run_classic s1 A b -> run s2 B Failed).
Proof.
  move=> H.
  remember (Or _ _ _) as O eqn:HO.
  remember Failed as F eqn:HF.
  move: b s2 A B HO HF.
  elim: H; clear => //=.
  + move=> s s' + b s2 A B /[subst1] /simpl_expand_or_fail [] H1 H2 _.
    by split; intros; apply run_fail.
  + by move=> s st1 st2 ? + H1 IH b s2 A B /[subst2] /simpl_expand_or_cut.
  + move=> s st1 st2 ? + H1 IH b s2 A B /[subst2] /simpl_expand_or_expanded [|[|[|]]].
    + move=> [A' [HA]] /[subst1].
      move: (IH b _ _ _ erefl erefl) => [] HL HR {IH}.
      split; [by apply: run_step HA _|] => H.
      inversion H1; subst; clear H1; move: H0.
      + move=> /simpl_expand_or_fail [HA' HB].
        apply: HR; inversion H; subst; try congruence.
      + by move=> /simpl_expand_or_cut.
      + by epose proof (run_classic_expandedR HA H); auto.
    + move=> [A' [HA]] /[subst1].
      move: (IH b _ _ _ erefl erefl) => [] HL HR.
      split; [by apply: run_cut HA HL|] => H.
      by inversion H; clear H; subst; rewrite HA in H0 => //=.
    + move=> [B' [HA [HB]]] /[subst1].
      move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
      by apply: run_step HB (HR HH).
    + move=> [B' [HA [HB]]] /[subst1].
      move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
      by apply: run_cut HB (HR HH).
Qed.

Lemma run_Failed_cut {s s2 A B}:
   run s A Failed ->
    run s (Or A s2 (cut B)) Failed.
Proof.
  remember Failed as F eqn:HF.
  move=> H.
  elim: H s2 B HF; clear => //=.
  + move=> s A H s2 B _.
    by apply: run_fail; rewrite /= H /= expand_cut_failure.
  + move=> s s' st1 st2 H H1 IH s2 B ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + apply: IH erefl.
  + move=> s s' st1 st2 H H1 IH s2 B ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + apply: IH erefl.
Qed.

Lemma run_or_fail1 {s1 s2 g1 g2}:
    run s1 g1 Failed -> (run_classic s1 g1 Failed -> run s2 g2 Failed) ->
      run s1 (Or g1 s2 g2) Failed.
Proof.
  move: (classic (run_classic s1 g1 Failed)) => [].
  + move=> H + /(_ H) => H1; move: H.  
    remember Failed as F eqn:HF.
    elim: H1 s2 g2 HF; clear => //=.
    + move=> s A H s2 B _ H1 H2; subst.
      remember Failed as F eqn:HF.
      elim: H2 s A H H1 HF; clear => //=.
      + by intros; apply run_fail => //=; rewrite H0 H1.
      + intros; subst. 
        apply: run_step => //=.
        rewrite H3 H0 => //=.
        by apply H2 => //=.
      + intros.
        apply: run_step => //=.
        rewrite H3 H0 => //=.
        by auto.
    + intros; subst.
      by move: (run_classic_cut H3 H0).
    + intros; subst.
      apply: run_step=> //=.
      + by rewrite H0 => //=.
      + by apply: H2 => //=; apply: run_classic_expandedR H0 H3.
  + remember Failed as F eqn:HF.
    move=> + H _.
    elim: H s2 g2 HF; clear => //=.
    + by move=> s st1 H ?? _ []; apply run_classic_fail.
    + move=> s st1 st2 r H H1 IH s2 g2 ? H2; subst.
      apply: run_step => //=.
      + rewrite H => //=.
      + apply: run_Failed_cut H1.
    + move=> s s' A B H H1 IH s2 C ? H2; subst.
      apply: run_step => //=.
      + by rewrite H.
      + apply: IH erefl _.
        move=> H3.
        apply: H2.
        apply: run_classic_step H H3.
Qed.

Lemma run_or_fail2 {s1 s2 g1 g2 g3}:
    run s1 g1 Failed -> expand s1 g1 = CutBrothers g3 -> (* g1 coulbe not an immediate cut, but expand... to a cut *)
      run s1 (Or g1 s2 g2) Failed.
Proof.
  move=> H H1; apply: run_or_fail1 H _ => H2.
  inversion H2; subst; congruence.
Qed.

Module check.
  Definition Gamma := V -> S.

  Fixpoint eat r1 r2 :=
    match r1, r2 with
    | arr _ _ r1, arr _ _ r2 => eat r1 r2
    | arr _ _ r1, _ => r1
    | _, _ => r1
    end.

  Fixpoint incl d1 d2 :=
    match d1, d2 with
    | b Exp, b Exp => true
    | b (d Func), b (d Func) => true
    | b (d Func), b (d Pred) => true
    | arr i l1 r1, arr i l2 r2 => incl l1 l2 && incl r1 r2
    | arr i l1 _, x => incl l1 x
    | arr o l1 r1, arr o l2 r2 => incl r1 r2
    | _, _ => false
  end.

  Fixpoint min m1 m2 :=
    match m1, m2 with
    | b Exp, b Exp => b Exp
    | b (d Func), _ => m1
    | b (d Pred), _ => m2
    | arr i l1 r1, arr i l2 r2 => arr i (max l1 l2) (min r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (min l1 l2) (min r1 r2)
    | _, _ => m1
  end
  with max m1 m2 := match m1, m2 with
    | b Exp, b Exp => b Exp
    | b (d Func), _ => m1
    | b (d Pred), _ => m2
    | arr i l1 r1, arr i l2 r2 => arr i (min l1 l2) (max r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (max l1 l2) (max r1 r2)
    | _, _ => m1
  end.

  Fixpoint infer_input (G: Gamma) tm : S * bool :=
    match tm with
    | Code (v V) => (G V, true)
    | Code (p P) => (G P, true)
    | Data _ => (b Exp, true)
    | Comb t1 t2 => 
      match infer_input G t1 with
      | (r, false) => (r, false)
      | (arr o _ x, true) => (x, true)
      | (arr i l r, true) => 
        match infer_input G t2 with
        | (_, false) => (r, false)
        | (d1, true) => (r, incl d1 l)
        end
      | (r, _) => (r, false)
      end
    end.

  Fixpoint infer_output (G: Gamma) tm : S * bool :=
    match tm with
    | Code (v V) => (G V, true)
    | Code (p P) => (G P, true)
    | Data _ => (b Exp, true)
    | Comb t1 t2 => 
      match infer_output G t1 with
      | (r, false) => (r, false)
      | (arr i _ x, true) => (x, true)
      | (arr o l r, true) => 
        match infer_input G t2 with
        | (_, false) => (r, false)
        | (d1, true) => (r, incl d1 l)
        end
      | (r, _) => (r, false)
      end
    end.

  Definition update_gamma (g:Gamma) (v : V) s : Gamma := 
    fun x => if eqn x v then s else g v.

  Fixpoint assume_input D tm (G : Gamma) : (S * Gamma) :=
  match tm with
  | Code (v V) => (D, update_gamma G V (min (G V) D))
  | Code (p P) => (G P, G)
  | Data _ => (b Exp, G)
  | Comb l r => 
    match assume_input D l G with
    | (arr i dl dr, G) => 
      if incl dr D then assume_input dl r G
      else (D, G)
    | _ => (D, G)
    end
  end.

  Fixpoint assume_output D tm (G : Gamma) : (S * Gamma) :=
  match tm with
  | Code (v V) => (D, update_gamma G V (min (G V) D))
  | Code (p P) => (G P, G)
  | Data _ => (b Exp, G)
  | Comb l r => 
    match assume_output D l G with
    | (arr o dl dr, G) => 
      if incl dr D then assume_input dl r G
      else (D, G)
    | _ => (D, G)
    end
  end.

  Definition check_atom (prog:program) atom '(g, s) :=
    match atom with
    | Cut => (g, b (d Func))
    | Call t => 
      if infer_input g t is (s',true) then 
        (snd (assume_output s' t g), max s s') (* not sure about the s' passed to assume_output *)
      else (g, b (d Pred))
    end.

  Definition check_entails (prog:program) (G:Gamma) (r:R) : bool :=
    let premises := r.(premises) in
    let: (expected_det, G) := assume_input (prog.(sig) r.(head)) r.(head) G in
    let: (G, body_det) := foldr (check_atom prog) (G,b (d (Func))) premises in
    if infer_output G r.(head) is (_, true) then incl body_det expected_det else false .


  Definition is_det g := forall s s' alt,
    run s g (Done s' alt) ->
      expand s alt = Failure.

  Lemma cut_is_det pr : is_det (Goal pr Cut).
  Proof. by move=> s s1 A /run_cut_simpl ->. Qed.

  Definition det_rule_cut (r : R) :=
    last Cut r.(premises) == Cut.

  Axiom same_subst : forall (s1 s2 : Sigma), s1 = s2.

    (* ------------------------------- *)

  Inductive runP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
  | runP_done {s s' A alt} : F A -> F alt -> expand s A = Solved s' alt  -> runP s A (Done s' alt)
  | runP_fail {s A}  : F A -> expand s A = Failure   -> runP s A Failed
  | runP_cut {s s' A B} : F A -> F B -> expand s A = CutBrothers B -> runP s B s' -> runP s A s'
  | runP_step {s s' A B} : F A -> F B -> expand s A = Expanded B  -> runP s B s' -> runP s A s'.

  Fixpoint expand_valid (A :state) : bool :=
  match A with
  | OK => false
  | KO | CutOut | Goal _ _ => true
  | Or OK sr R => R == cut R
  | Or L sr R => expand_valid L && expand_valid R
  | And L R => expand_valid L && expand_valid R
  end.

  Fixpoint expand_valid1 (A : state) : bool :=
    match A with
    | OK | KO | CutOut | Goal _ _ => true
    | Or _ _ _ => expand_valid A
    | And L R => expand_valid1 L && expand_valid1 R
    end.

  Lemma simpl_expand_valid1_or {A s B}:
    expand_valid1 (Or A s B) -> (A = OK /\ B == cut B) \/ (expand_valid A && expand_valid B).
  Proof. by case: A => //=; auto. Qed.

  Lemma simpl_expand_B_cut {A B}:
    match A with
    | OK => B == cut B
    | _ => expand_valid A && expand_valid B
    end -> (A = OK /\ B = cut B) \/ (A <> OK /\ expand_valid A /\ expand_valid B).
  Proof.
    case: A => //=.
    + by move=> H; right; rewrite H.
    + by move=> /eqP H; left; rewrite <-H.
    + by move=> ?? H; rewrite H; right.
    + by move=>??? /andP []??; right.
    + by move=>?? /andP []??; right.
    + by move=>?; right.
  Qed.

  Lemma expand_valid_bool {B}: expand_valid B -> expand_valid1 B.
  Proof. by elim: B => //=; move=> A IHA B IHB /andP [] HA HB; rewrite (IHA HA) (IHB HB). Qed.

  Lemma expand_valid_cut_cut B:
    expand_valid (cut B).
  Proof. elim: B => //= [A HA _ B HB|A HA B HB]; rewrite HA HB => //=; by elim:A {HA HB} => //=. Qed.

  Lemma expand_valid_solved {s s' A A'}:
     expand s A = Solved s' A' -> expand_valid1 A -> expand_valid A'.
  Proof.
    elim: A s s' A' => //.
    + by move=> s s' A [] /[subst2].
    + by move=> pr [] => //= t s s' A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 s2 C.
      move=> /simpl_expand_or_solved []. 
      + move=> [] HA HB // /simpl_expand_valid1_or [].
        + move=> [] /[subst1] /eqP H.
          rewrite H in HB.
          by rewrite expand_cut_failure in HB.
        + move=> /andP [] EA EB; apply: IHB HB (expand_valid_bool EB).
      + move=> [D [HA]] /[subst1] /simpl_expand_valid1_or [].
        + move=> [] /[subst1] /eqP H //=.
          move: HA => [] /[subst2]; rewrite H.
          by rewrite (expand_valid_cut_cut).
        + move=> /andP [] EA EB //=.
          rewrite EB (IHA _ _ _ HA (expand_valid_bool EA)).
          destruct D => //=.
          by move: (expand_solve_ok HA).
    + move=> A IHA B IHB s1 s2 C //=.
      move=> /simpl_expand_and_solved [s' [L [R [HA [HB]]]]] /[subst1] /andP [] EA EB => //=.
      by rewrite (IHA _ _ _ HA EA) (IHB _ _ _ HB EB).
  Qed.

  Lemma expand_valid_cut {s A B}:
     expand s A = CutBrothers B -> expand_valid1 A -> expand_valid1 B.
  Proof.
    elim: A s B => //.
    + move=> pr [] => //=.
      + move=> ?? [] /[subst1] _ //=.
      + by move=> t s B ; case X: F => //= [[] a].
    + by move=> A IHA s B IHB s1 C // /simpl_expand_or_cut.
    + move=> A IHA B IHB s1 C //.
      move=> /simpl_expand_and_cut [].
      + move=> [A' [H]] /[subst1] //= /andP [] HA HB.
        by rewrite HB (IHA _ _ H HA).
      + move=> [s' [A' [B' [EA [EB]]]]] /[subst1] //= /andP [] HA HB.
        by rewrite HA (IHB _ _ EB HB).
  Qed.

  Lemma expand_valid_mk_and_aux {pr a l}:
    expand_valid (big_and_aux pr a l).
  Proof. elim: l a => //=. Qed.

  Lemma expand_valid_mk_and {pr p}:
    expand_valid (big_and pr (premises p)).
  Proof. case p=> //= _ [] //= a l; apply expand_valid_mk_and_aux. Qed.

  Lemma expand_valid_mk_and_true {pr prem}:
    expand_valid (big_and pr (premises prem)).
  Proof. case prem=> //= _ [] //= a l; apply expand_valid_mk_and_aux. Qed.

  Lemma big_and_aux_OK_false {pr x l}: big_and_aux pr x l <> OK.
  Proof. by elim: l. Qed.

  Lemma simpl_match_big_and {pr b xs r}:
    match big_and pr (premises b) with
    | OK => big_or pr b xs == cut (big_or pr b xs)
    | _ => r
    end = r.
  Proof. case: premises => //= => a [] //=. Qed.

  Lemma big_and_OK_false {pr l}: big_and pr l <> OK.
  Proof. case l => //=; move=> ?? H; apply: big_and_aux_OK_false H. Qed.

  Lemma expand_valid_mk_or {pr r xs}:
    expand_valid (big_or pr r xs).
  Proof.
    elim: xs r => //=; clear.
    + move=> ?; apply expand_valid_mk_and.
    + move=> [] s {}r l H r1//=.
      case X: premises => //= [x xs].
      case Y: xs => //=.
      by rewrite H expand_valid_mk_and_aux.
  Qed.


End check.
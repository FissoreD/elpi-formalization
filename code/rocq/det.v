(* Require Import Coq.Program.Wf. *)
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
Inductive C := 
  | p of P 
  | v of V
  .
Inductive Tm := 
  | Code : C -> Tm
  | Data : K -> Tm
  | Comb : Tm -> Tm -> Tm.
  (* | Lam  : V -> S -> Tm -> S -> Tm. *)
Record R_ {A} := { pred : P; args : list Tm; premises : list A }.
Inductive A :=
  | Cut
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
Definition sigT := nat -> S.
Record program := { (*depth : nat;*) rules : index; modes : mode_ctx; sig : sigT }.

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
  | OK : (*Sigma ->*) state
  | Goal : program  -> A -> state
  | Or  : state -> Sigma -> state -> state
  | And : (*Sigma ->*) state -> state -> state
  | CutOut : state
  .

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

Fixpoint big_and pr (a : list A) : state :=
  match a with
  | [::] => OK
  | x :: xs => And (Goal pr x) (big_and pr xs)
  end.

Fixpoint big_or pr (s : seq (Sigma * R)) : state :=
  match s with 
  | [::] => KO
  | [:: (_,r)] => big_and pr r.(premises)
  | (_,r) :: ((s,_) :: _ as xs) => Or (big_and pr r.(premises)) s (big_or pr xs)
  end.

Fixpoint expand s (st :state) : expand_res :=
  match st with
  | KO => Failure
  | OK => Solved s KO
  | CutOut => Failure
  | Goal _ Cut  => CutBrothers OK
  | Goal pr (App (v _) _) => Failure
  | Goal pr (App (p pn) args) =>
      let l := F pr pn args s in
      if l is [:: (s1,_) & _] then Expanded (big_or pr l)
      else Expanded KO
  | Or st1 sr st2 =>
      match expand s st1 with
      | Solved s A => Solved s (Or A sr st2)
      | Expanded st1 => Expanded (Or st1 sr st2)
      | CutBrothers st1 => Expanded (Or st1 sr (cut st2))
      | Failure => mkOr st1 sr (expand sr st2)
      end
  | And st1 st2 =>
      match expand s st1 with
      | Solved s1 r => mkAnd r st1 (expand s1 st2)
      | Expanded st1 => Expanded (And st1 st2)
      | CutBrothers st1 => CutBrothers (And st1 st2)
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


Goal expand empty (Or OK empty OK) = Solved empty (Or KO empty OK). by []. Qed.
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
    case L: expand => [|||x] //; case R: expand => //= -[]??; subst.
    do 3 eexists; repeat constructor.
    + apply L.
    + apply R. 
  - move=> s s' ? B + H1 + A B' alt ? s'' ?; subst => //=.
    case L: expand => [|AC||s'] // => [[?]|]; subst.
    - move=> /(_ _ _ _ erefl _ erefl) [s'[altA[altB[?[IHl IHr]]]]]; subst.
      do 3 eexists; repeat split => //=.
      by apply: run_cut L IHl.
      by apply: IHr.
    - case R: expand => //= -[?]; subst.
      move=> /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [? [IHl IHr]]]]]; subst.
      move: (run_Solved_id L IHl) => [] ?; subst.
      do 3 eexists; repeat split => //=.
      - by apply: IHl.
      - apply: run_cut R IHr.
  - move=> s ? A' C + H1 + A B ? s' ??; subst => //=.
    case E1: expand => //= [|s1].
    - move=> []?; subst.
      move => /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [? [IHl IHr]]]]]; subst.
      do 3 eexists; repeat split => //=.
      by apply: run_step E1 IHl.
      by assumption.
    - case E2: expand => //= [st] [] ?; subst.
      move=> /(_ _ _ _ erefl _ erefl) [s''' [altA [altB [?[IHl IHr]]]]]; subst.
      move: (run_Solved_id E1 IHl) => []??; subst.
      do 3 eexists; repeat split => //=.
      eassumption.
      apply: run_step E2 IHr.
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
  + move=> s A + A1 B2 ? _; subst => //=.
    case E: expand => [|||s'] //=.
    + by move=> _; left; apply: run_fail.
    + case F: expand => //= _; right.
      do 2 eexists; split.
      - apply: run_done E.
      - by apply run_fail.
  + move=> s s' A B + H1 IH A1 B1 ? ?; subst => //=.
    case E: expand => //=.
    - move=> [] ?; subst.
      move: (IH _ _ erefl erefl) => [].
      + by left; apply: run_cut E _.
      + move=> [] s' [] altA [] H2 H3.
        right; do 2 eexists; split; [|eassumption]; apply: run_cut E H2.
    - case F: expand => //= -[] ?; subst.
      move: (IH _ _ erefl erefl) => []; [by auto|].
      move=> [] s' [] altA [] H2 H3.
      move: (run_Solved_id E H2) => []?; subst.
      right; repeat eexists; [eassumption|apply: run_cut F H3].
  + move=> s s' A B + H1 IH A1 B1 ??; subst => //=.
    case E: expand => //=.
    + move=> [] ?; subst.
      move: (IH _ _ erefl erefl) => [] {IH}.
      + by left; apply: run_step E _.
      + move=> [] ? [] altA [] H2 H3.
        by right; repeat eexists; [apply: run_step E H2|].
    + case F: expand => //= -[] ?; subst.
      move: (IH _ _ erefl erefl) => [] {IH}; [by auto|].
      move=> [] ? [] altA [] H2 H3.
      move: (run_Solved_id E H2) => []?; subst.
      right; repeat eexists; [by eassumption|].
      by apply: run_step F H3.
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

(* Lemma expand_cut_solved {s s' A altA}:
  expand s (cut A) = Solved s' altA -> False.
Proof.
  elim: A s s' altA => //=.
  + move=> A H1 s B H2 s1 s2 altA.
    case E: expand => //=.
    + case F: expand => //= -[] ??; subst.
      apply: H2 F.
    + by move=> [] ??; subst; apply: H1 E.
  + move=> A IH1 B IH2 s s' altA.
    case E: expand => //=.
    case F: expand => //= -[] ??; subst.
    apply: IH2 F.
Qed.

Lemma expand_cut_CB {s A B}:
  expand s (cut A) = CutBrothers B -> False.
Proof.
  elim: A s B => //=.
  + move=> AL IH s' AR H s B => //=.
    case X: expand => //=.
    case Y: expand => //=.
  + move=> A IHA B IHB s C.
    case X: expand => //=.
    + move=> [] ?; subst; apply: IHA X.
    + case: expand => //=? -[]?; subst.
      apply: expand_cut_solved X.
Qed.

Lemma expand_cut_expanded {s A B}: expand s (cut A) = Expanded B -> False.
Proof.
  elim: A s B => //=; clear.
  + move=> s IH s' A H s'' B //=; case E: expand => //=.
    + by move=> [] ?; subst; f_equal; apply: IH E.
    + by move: (expand_cut_CB E).
    + case F: expand => //=.
      - move=> [] ?; subst.
        by move: (H _ _ F) => ?; subst.
      - by move: (expand_cut_CB F).
  + move=> s0 IH0 s1 IH1 s A; case E: expand => //=.
    + by move=> [] ?; subst; move: (IH0 _ _ E) => ?; subst.
    + case F: expand => //= -[] ?; subst.
      by move: (IH1 _ _ F) => ?; subst.
Qed. *)

Lemma expand_cut_failure {s A}: expand s (cut A) = Failure.
Proof.
  elim: A s => //=; clear.
  - by move => A IHl s1 B IHr s2; rewrite IHl IHr.
  - by move => A IHl B IHr s2; rewrite IHl.
Qed.

Axiom classic : forall P : Prop, P \/ ~ P.

(* Lemma expand_cut_result1 s A:
  expand s (cut A) = Failure \/ exists x, expand s (cut A) = (Expanded x).
Proof.
  case X: (expand s (cut A)).
  + by right; eexists.
  + by move: (expand_cut_CB X).
  + by left.
  + by move: (expand_cut_solved X).
Qed. *)

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
  + move=> s A + A1 B ?; subst => //=.
    case X: expand => //=.
    + by left; apply: run_classic_fail.
    + case Y: expand => //=  _; right; repeat eexists.
      + apply: run_done X.
      + by apply: run_classic_fail.
  + move=> s st st1 b + H1 + A B ??; subst => //=.
    case X: expand => //=.
    + move=> []?;subst.
      move=> /(_ _ _ erefl erefl) => -[].
      + move=> H; left; apply: run_classic_step X H.
      + move=> [X1 [altA [H2 H3]]]; right.
        repeat eexists.
        + apply: run_step X H2.
        + apply: H3.
    + case Y: expand => //= [A'] [] ?; subst.
      move=> /(_ _ _ erefl erefl) [].
      + by left.
      + move=> [s' [altA [H2 H3]]]; right.
        repeat eexists; try eassumption.
        inversion H2; subst; try congruence; clear H2.
        move: H6; rewrite X => -[]??; subst.
        by apply: run_classic_step Y H3.
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
    case X: expand => //=.
    case Y: expand => //= -[] ??; subst.
    by do 2 eexists.
  + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
    case E: expand => //=.
    + by move=> []?; subst; apply: IH erefl erefl.
    + by case F: expand => //= -[]?; subst; apply: IH erefl erefl.
  + move=> s st st1 st2 + H1 IH A B SOL ??; subst => //=.
    case E: expand => //= [A'|A'].
    + by move=> [] ?; subst; apply: IH erefl erefl.
    + by case F: expand => //= -[]?; subst; apply: IH erefl erefl.
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
  + move=> s st s' alt + s2 A B altAB SOL ? []??; subst => //=.
    case E: expand => //=.
    + case F: expand => //= -[] ??; subst.
      right; eexists; repeat split.
      + apply: run_classic_fail E.
      + apply: run_done F.
    + move=> [] ??; subst; left.
      eexists; apply: run_done E.
  + move=> s ? st1 st2 + H1 IH s2 A B altAB SOL ??; subst => /=.
    case E: expand => //=.
    by case F: expand => //=.
  + move=> s ? st1 st2 + H1 IH s2 A B altAB SOL ?? ; subst => //=.
    case E: expand => [s4|||s4] //=.
    + move=> [] ?; subst.
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[altA[HL HR]]].
      - left; eexists; apply: run_step E H.
      - right; eexists; split; [apply: run_classic_step E HL|apply: HR].
    + move=> [] ?; subst.
      move: IH => /(_ _ _ _ _ _ erefl erefl) [[altA H]|[?[HL HR]]].
      - by left; eexists; apply: run_cut E H.
      - by move: (run_cut_fail HR).
    + case F: expand => [ss|ss||] //=.
      - move=> [] ?; subst.
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[?[HL HR]]].
        by destruct (run_Failure_and_Done E H).
        right; eexists; split; auto; apply: run_step F HR.
      - move=> [] ?; subst.
        move: IH => /(_ _ _ _ _ _ erefl erefl) [[? H]|[? [HL HR]]].
        by destruct (run_Failure_and_Done E H).
        right; eexists; split; auto; apply: run_cut F HR.
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

Lemma run_or_fail {s1 s2 g1 g2 b}:
  run s1 (Or g1 s2 g2) Failed ->
    run s1 g1 Failed /\ (run_classic s1 g1 b -> run s2 g2 Failed).
Proof.
  move=> H.
  remember (Or _ _ _) as O eqn:HO.
  remember Failed as F eqn:HF.
  move: b s2 g1 g2 HO HF.
  elim: H; clear => //=.
  + move=> s s' + b s2 g1 g2 HO _; subst => /=.
    case E: expand => //=.
    case F: expand => //=.
    by move=> _; split; intros; apply run_fail.
  + move=> s st1 st2 ? + H1 IH b s2 g1 g2 ? ?; subst => /=.
    case E: expand => //=.
    by case F: expand => //=.
  + move=> s st1 st2 ? + H1 IH b s2 g1 g2 ?? ; subst => //=.
    case E: expand => [s4|||s4] //=.
    + move=> [] ?; subst.
      move: (IH b _ _ _ erefl erefl) => [] HL HR {IH}.
      split; [by apply: run_step E _|] => H.
      inversion H1; subst; clear H1; move: H0 => //=.
      + case F: expand => //=; case: expand => //= _.
        apply: HR.
        inversion H; try congruence.
      + by case F: expand => //=; case G: expand => //=.
      + by epose proof (run_classic_expandedR E H); auto.
    + move=> [] ?; subst.
      move: (IH b _ _ _ erefl erefl) => [] HL HR.
      split; [by apply: run_cut E HL|] => H.
      inversion H; clear H; subst; rewrite E in H0 => //=.
    + case F: expand => //= -[] ?; subst.
      - move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_step F (HR HH).
      - move: (IH b _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_cut F (HR HH).
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

  Fixpoint infer (G: Gamma) tm :=
    match tm with
    | Code (v V) => (G V, true)
    | Code (p P) => (G P, true)
    | Data _ => (b Exp, true)
    | Comb t1 t2 => 
      match infer G t1 with
      | (r, false) => (r, false)
      | (r, _) => 
        match infer G t2 with
        | (r, false) => (r, false)
        | (d1, true) => (eat r d1, incl r d1)
        end
      end
    end.

  Definition update_gamma (g:Gamma) (v : V) s : Gamma := 
    fun x => if eqn x v then s else g v.

  Fixpoint assume D tm (G : Gamma) : (S * Gamma) :=
  match tm with
  | Code (v V) => (D, update_gamma G V (min (G V) D))
  | Code (p P) => (G P, G)
  | Data _ => (b Exp, G)
  | Comb l r => 
    match assume D l G with
    | (arr i dl dr, G) => 
      if incl dr D then assume dl r G
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
      if incl dr D then assume dl r G
      else (D, G)
    | _ => (D, G)
    end
  end.

  Axiom infer_inputs : (seq Tm) -> S -> bool.
  Axiom assume_outputs : (seq Tm) -> S -> Gamma * S.  
  Axiom assume_inputs : (seq Tm) -> S -> Gamma * S.  

  Axiom base_sig : program -> nat -> S.

  Definition check (prog:program) atom (g:Gamma) (s:S) :=
    match atom with
    | Cut => (g, s)
    | App (v V) args => 
      let b := infer_inputs args s in
      if b then assume_outputs args s
      else (g, s)
    | App (p P) args => 
      let b := infer_inputs args s in
      if b then assume_outputs args s
      else (g, s)
    end.

  Axiom checks : program -> list A -> Gamma -> bool.

  Definition check_entails (prog:program) (G:Gamma) (r:R) : bool :=
    let pred := r.(pred) in
    let args := r.(args) in
    let premises := r.(premises) in
    let (G', s) := assume_inputs args (prog.(sig) pred) in
    checks prog premises G'.


End check.
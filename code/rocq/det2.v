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
  | OK : state
  | Goal : program  -> A -> state
  | Or  : state -> Sigma * state -> state
  | And : state -> state -> state
  | CutOut : state
  .

(* Notation "A ∧ B" := (And A B) (at level 13000).
Notation "A ∨ B" := (Or A B) (at level 13000). *)

Inductive expand_res :=
  | Expanded of state
  | CutBrothers of state
  | Failure
  | Solved of Sigma.

Definition mkAnd left r :=
  match r with
  | Failure => Failure
  | Expanded st => Expanded (And left st)
  | CutBrothers st => CutBrothers (And left st)
  | Solved s => Solved s
  end.

Definition mkOr left sr r :=
  match r with
  | Failure => Failure
  | Expanded st => Expanded (Or left (sr,st))
  | CutBrothers st => Expanded (Or left (sr,st)) (* for now this is the rightmost brother *)
  | Solved s => Solved s
  end.

Fixpoint cut st :=
  match st with
  | Goal _ _ => CutOut
  | And x y => And (cut x) (cut y)
  | Or x (s,y) => Or (cut x) (s,cut y)
  | OK => CutOut
  | KO => KO
  | CutOut => CutOut
  end.


Lemma cut_cut_same {a}: cut (cut a) = cut a.
Proof. 
  elim: a => //=.
  move=> ? H [] => //=; rewrite H.
  move => s A; f_equal.
  admit. (* enrico *)
  move=> ? H ? H1.
  by rewrite H H1.
Admitted.

Fixpoint big_and pr (a : list A) : state :=
  match a with
  | [::] => OK
  | x :: xs => And (Goal pr x) (big_and pr xs)
  end.

Fixpoint big_or pr (s : seq (Sigma * R)) : state :=
  match s with 
  | [::] => KO
  | [:: (_,r)] => big_and pr r.(premises)
  | (_,r) :: ((s,_) :: _ as xs) => Or (big_and pr r.(premises)) (s,big_or pr xs)
  end.

Fixpoint expand s (st :state) : expand_res :=
  match st with
  | KO => Failure
  | OK => Solved s
  | CutOut => Failure
  | Goal _ Cut  => CutBrothers OK
  | Goal pr (App (v _) _) => Failure
  | Goal pr (App (p pn) args) =>
      let l := F pr pn args s in
      if l is [:: (s1,_) & _] then Expanded (big_or pr l)
      else Expanded KO
  | Or st1 (sr,st2) =>
      match expand s st1 with
      | Solved s => Solved s
      | Expanded st1 => Expanded (Or st1 (sr,st2))
      | CutBrothers st1 => Expanded (Or st1 (sr,cut st2))
      | Failure => mkOr st1 sr (expand sr st2)
      end
  | And st1 st2 =>
      match expand s st1 with
      | Solved s1 => mkAnd st1 (expand s1 st2)
      | Expanded st1 => Expanded (And st1 st2)
      | CutBrothers st1 => CutBrothers (And st1 st2)
      | Failure => Failure
      end
  end
.

Lemma expand_And st1 st2 s : expand s (And st1 st2) =
      match expand s st1 with
      | Solved s1 => mkAnd st1 (expand s1 st2)
      | Expanded st1 => Expanded (And st1 st2)
      | CutBrothers st1 => CutBrothers (And st1 st2)
      | Failure => Failure
      end.
by [].
Qed.


Inductive run_res := Done of Sigma | Failed.

Inductive run : Sigma -> state -> run_res -> state -> Prop :=
  | run_done {s st s'} :
      expand s st = Solved s' ->
      run s st (Done s') st
  (* | run_done1 {s s' A B} :
    expand s A = Solved s' -> run s B (Done s') B -> run s A (Done s') B *)
  | run_fail {s st st1} :
      expand s st = Failure ->
      run s st Failed st1
  | run_cut {s st st1 st2 r} :
      expand s st = CutBrothers st1 ->
      run s st1 r st2 ->
      run s st r st2 
  | run_step {s st st1 st2 r} :
      expand s st = Expanded st1  ->
      run s st1 r st2 ->
      run s st r st2
  (* | run_or_fail {s1 s2 st1 st2 st3 r} :
    expand s1 st1 = Failure ->
    run s2 st2 r st3 ->
    run s1 (Or st1 (s2, st2)) r st3 *)
.

Lemma run_Solved_id:
  forall {s s1 s2 st1 st2},
    expand s st1 = Solved s1 -> run s st1 (Done s2) st2 -> s2 = s1 /\ st1 = st2.
Proof.
  move=> s s1 s2 st1 st2 + H.
  remember (Done s2).
  move: Heqr.
  case: H => //=; clear.
  by move=> s st1 s3 H1 [] ?; rewrite H1=> -[] ?; subst.
  (* move=> s s' A B H1 H2 [] ?; rewrite H1 => -[] ?; subst. *)
  by move=> s st st1 st2 r H H1 ?; rewrite H.
  by move=> s st st1 st2 ? H ; rewrite H.
Qed.

Lemma run_Failure_and_Done {s A sol A'}:
  expand s A = Failure -> run s A (Done sol) A' -> False.
Proof. by inversion 2; subst; congruence. Qed.

Lemma run_Solved_and_Failed {s A sol A'}:
  expand s A = Solved sol -> run s A Failed A' -> False.
Proof. inversion 2; subst; congruence. Qed.

(* Lemma run_CutBrothers_same_subst:
  run s' C (Done sD) ir ->
    run s' _s1_ (Done sD) ir1 ->
      expand _s_ C = CutBrothers _s1_ *)

Lemma run_consistent: forall {a b c1 c2 r1 r2},
  run a b c1 r1 -> run a b c2 r2 -> c1 = c2 /\ (c1 <> Failed -> r1 = r2).
Proof.
  move=> a b c1 + r1  + H.
  elim:H; clear.
  + move=> s st s' H r1 r2 H1. {
    inversion H1; subst; clear H1 => //=; rewrite H in H0.
      by move: H0 => -[] <-.
      all: by []. }
  + move=> s st st1 H r1 r2 H0.
    inversion H0; subst; clear H0 => //=; by rewrite H in H1.
  + move=> s st st1 st2 r H H1 IH r1 r2 H2.
    inversion H2; subst => //; rewrite H in H0; try by [].
    by move: H0 => -[] ?; subst; auto.
  + move=> s st st1 st2 r H H1 IH r1 r2 H2.
    inversion H2; subst; clear H2; rewrite H in H0; try by [].
    by move: H0 => [] ?; subst; auto.
Qed.

Lemma run_consistent_res {a b c1 c2 r1 r2}:
    run a b c1 r1 -> run a b c2 r2 -> c1 = c2.
Proof. by move=> H H1; apply (proj1 (run_consistent H H1)). Qed.

Lemma run_consistent_state {a b c1 c2 r1 r2}:
    run a b c1 r1 -> run a b c2 r2 -> (c1 <> Failed ->  r1 = r2).
Proof. by move=> H H1; apply (proj2 (run_consistent H H1)). Qed.

Lemma run_cut_simpl pr s3 s4 s2:
  run s3 (Goal pr Cut) (Done s2) s4 -> expand s3 OK = Solved s2 /\ s4 = OK.
  (* expand (Goal pr Cut) s3 = CutBrothers st1 /\  run s3 st1 (Done s2) s4. *)
Proof.
  inversion 1; subst => //=.
  move: H1 => //= [] ?; subst.
  inversion H2; subst => //.
Qed.

Lemma run_CutBrothers_id {s2 s3 st1 st2 ir1 ir2}:
  expand s3 st1 = CutBrothers st2 -> 
  run s3 st2 (Done s2) ir1 -> 
  run s3 st1 (Done s2) ir2 ->
  ir1 = ir2.
Proof.
  move: s2 s3 st2 ir1 ir2.
  case: st1 => //=.
  + move=> pr [] //=.
    - move=> ????? [] <- H H1.
      apply run_cut_simpl in H1 as []; subst; by inversion H.
    - move=> [] pn args s2 s3 st2 ir1 ir2 => //=; by case F: F => [|[]] //=.
  + move=> st0  [] s st1 s2 s3 st2 ir1 ir2; by case: expand; case: expand => //.
  + move=> st0 st1 s2 s3 st2 ir1 ir2.
    case E: expand => //.
    + move=> [] <- H1 H2.
      { 
        inversion H2; subst; clear H2 => //=.
          + move: H5 => //=.
            case F: expand => //.
            by rewrite E in F.
          + move: H0 => //=.
            case F: expand => //=.
            - rewrite E in F.
              move: F => [] <- [] ?; subst.
              by apply (run_consistent H1 H3).
            - case G: expand => //= -[] ?; subst.
              by rewrite E in F.
          + move: H0 => /=; case F: expand => //. 
            - move => [] ?; subst.
              by rewrite E in F.
            - by rewrite E in F.
      }
    + case F: expand => //= -[] ?; subst => H H1.
      inversion H1; subst; clear H1; subst.
        + move: H4 => //=.
          case G: expand => //.
          rewrite E in G.
          move: G => [] <-.
          case G: expand => //=.
          by rewrite F in G.
        + move: H0 => //=.
          case G: expand => //.
            by rewrite E in G.
          case G1: expand => //= -[] ?; subst.
          rewrite E in G; move: G => [] ?; subst.
          rewrite F in G1; move: G1 => [] ?; subst.
          by apply (run_consistent H H2).
        + move: H0 => //=.
          case G: expand => //=.
          - by rewrite E in G.
          - case D: expand => //= -[] ? ; subst.
            rewrite E in G.
            move: G => [] ?; subst.
            by rewrite F in D.
Qed.

Lemma run_solved_same_subst {st_l s s' s''' il}:
   expand s st_l = Solved s' ->
    run s st_l (Done s''') il ->
      s' = s'''.
Proof.
  move: s s' s''' il.
  elim: st_l => //=.
  by move=> s s' s''' il [] <-; inversion 1; subst => //=; move: H4 => /= [].
  by move=> pr [] // [v args | p args] s s' s''' il => //=; case: F => // -[] //.
  move=> s IH [] s1 st s2 s3 s4 il //.
    case E: expand => //.
      case F: expand => //= -[] <- H.
      { 
        inversion H; subst; clear H => //=.
        + by move: H3 => /=; rewrite E F => -[].
        + by move: H0 => /=; rewrite E F.
        + by move: H0 => /=; rewrite E F.
      }
    move=> [] <- H.
      {
       inversion H; subst; clear H.
       + by move: H3 => /=; rewrite E => -[].
       + by move: H0 => /=; rewrite E.
       + by move: H0 => /=; rewrite E.
      }
  move=> s IH1 s0 IH2 s1 s' s''' il.
    case E: expand => //.
    case F: expand => //= - [] <- H.
    {
      inversion H; subst; clear H.
      + by move: H3 => /=; rewrite E F => -[].
      + by move: H0 => /=; rewrite E F.
      + by move: H0 => /=; rewrite E F.
    }
Qed.

Lemma run_and_succeed {s g1 g2 s' st} :
  run s (And g1 g2) (Done s') st ->
    (exists il ir s'', st = And il ir /\ run s g1 (Done s'') il /\ run s'' g2 (Done s') ir).
Proof.
  remember (And _ _) as g0 eqn:Hg0.
  remember (Done _) as s1 eqn:Hs1.
  move => H.
  move: g1 g2 Hg0 s' Hs1.
  elim: H => {st s s1 g0} /= [s st s'|s st|s st st1 st2 r|] => //=.
  - move=> + st_l st_r ? r [?]; subst.
    rewrite expand_And; case L: expand => [|||x] //; case R: expand => //= -[?]; subst.
    by exists st_l, st_r, x; repeat split; constructor.
  - move=> + Hr + st_l st_r ? s'' ?; subst => //=.
    case L: expand => [|st0||s'] // => [[?]|]; subst.
    - move=> /(_ _ _ erefl _ erefl) [il [ir [s']]] [-> [ IHl IHr]].
      exists il, ir, s'; split=> //; split.
      by apply: run_cut L IHl.
      by apply: IHr.
    - case R: expand => //= -[?]; subst.
      move=> /(_ _ _ erefl _ erefl) [il [ir [s''']]] [-> [ IHl IHr]].
      exists il, ir, s'''; split=> //; split.
      - by apply: IHl.
      - move: (run_solved_same_subst L IHl) => ?; subst.
        apply: run_cut R IHr.
  - move=> s ? A' C ? + H1 + A B ? s' ?; subst => //=.
    case E1: expand => //= [|s1].
    - move=> [?]; subst.
      move => /(_ _ _ erefl _ erefl) [il [ir [s''']]] [-> [ IHl IHr]].
      exists il, ir, s'''; repeat split => //=.
      by apply: run_step E1 IHl.
    - case E2: expand => //= [st] [] ?; subst.
      move=> /(_ _ _ erefl _ erefl) [il [ir [s''']]] [? [ IHl IHr]]; subst.
      move: (run_Solved_id E1 IHl) => [] ??; subst.
      exists il, ir, s1; repeat split => //=.
      apply: run_step E2 IHr.
Qed.

Lemma run_and_succeed1 {s0 s1 s2 g1 g2 il ir} :
    run s0 g1 (Done s1) il -> run s1 g2 (Done s2) ir ->
      run s0 (And g1 g2) (Done s2) (And il ir).
Proof.
  remember (Done _) as ds1 eqn:Hds1.
  move => H.
  move: s1 s2 g2 ir Hds1.
  elim: H => //=; clear.
  + move=> + + s' + s1 s2 g2 ir [] ? H1; subst.
    remember (Done s2).
    move: s2 Heqr.
    elim: H1 => //=; clear.
    + move=> s st s' H s2 [] ? s0 g1 H1; subst.
      apply: run_done => //=; rewrite H1 H => //=.
    + move=> s g2 st1 st2 r H H1 IH s2 ? s0 g1 H2; subst.
      apply: run_cut => //=.
      + rewrite H2 H => //=.
      + apply: IH => //=.
    + move=> s g2 st1 st2 r H H1 IH s2 ? s0 g1 H2; subst.
      apply: run_step => //=.
      + by rewrite H2 H.
      + by apply: IH _ H2.
  + move=> s0 g1 st1 il r H H1 IH s3 s2 g2 ir ? H2; subst.
    apply: run_cut => //=.
    + by rewrite H.
    + by apply: IH _ H2.
  + move=> s0 g1 st1 il ? H H1 IH s1 s2 g2 ir ? H2; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by apply: IH erefl H2.
Qed.
 

Lemma run_and_fail {s g1 g2 st}:
  run s (And g1 g2) Failed st ->
    run s g1 Failed st \/ (exists s' st', run s g1 (Done s') st' /\ run s' g2 Failed st).
Proof.
  move=> H.
  remember (And _ _) as A eqn:HA.
  remember Failed as F eqn:HF.
  move: g1 g2 HA HF.
  elim: H => //=; clear.
  + move=> s st st1 + g1 g2 ? ?; subst => //=.
    case E: expand => [|||s2] //=.
    + by move=> _; left; apply: run_fail.
    + case F: expand => //=.
      move=> _; right.
      exists s2, g1; split.
        - by apply run_done.
        - by apply run_fail.
  + move=> s ? st1 st2 ? + H IH g1 g2 ? ?; subst => //=.
    case E: expand => //=.
    - move=> [] ?; subst.
      move: (IH _ _ erefl erefl) => [].
      + by left; apply: run_cut E _.
      + move=> [? [? []]] H1 H2.
        by right; do 2 eexists; split; [|eassumption]; apply: run_cut E H1.
    - case F: expand => //= -[] ?; subst.
      move: (IH _ _ erefl erefl) => []; [by auto|].
      move=> [? [? []]] H1 H2.
      epose proof (run_Solved_id E H1) as []; subst.
      by right; do 2 eexists; split; [eassumption|apply: run_cut F H2].
  + move=> s ? st1 st2 ? + H1 IH g1 g2 ??; subst => //=.
    case E: expand => //=.
    + move=> [] ?; subst.
      move: (IH _ _ erefl erefl) => [] {IH}.
      + by left; apply: run_step E _.
      + move=> [? [? []]] H2 H3.
        by right; do 2 eexists; split; [apply: run_step E H2|].
    + case F: expand => //= -[] ?; subst.
      move: (IH _ _ erefl erefl) => [] {IH}; [by auto|].
      move=> [? [? []]] H2 H3.
      epose proof (run_Solved_id E H2) as []; subst.
      right; do 2 eexists; split; [by eassumption|].
      by apply: run_step F H3.
Qed.

Inductive not_cut_brothers : Sigma -> state -> Prop :=
  | not_cut_brothers_solved {s' s g} : expand s g = Solved s' -> not_cut_brothers s g
  | not_cut_brothers_failure {s g}    : expand s g = Failure   -> not_cut_brothers s g
  | not_cut_brothers_expanded {s g g'} : 
    expand s g = Expanded g' -> not_cut_brothers s g' -> not_cut_brothers s g.

Lemma not_cut_brothersP {s1 g1 g2 g3}:
  expand s1 g1 = Expanded g2 -> 
    not_cut_brothers s1 g1 ->
      run s1 g2 Failed g3 ->
        not_cut_brothers s1 g2.
Proof.
  move=> + H.
  move: g2 g3.
  elim: H => //=.
  move=> s' s g H g2 g3 H1 H2.
    inversion H2; subst; clear H2 => //=; rewrite H1 in H; try by [].
  move=> s g H g2 g3 H1 H2.
    remember Failed.
    move: s1 g1 g H H1 Heqr => _ _.
    elim: H2 => //=; clear.
    by move=> s st _ H g H1 H2 _; apply: not_cut_brothers_failure H.
    by move=> s st st1 st2 r H H1 IH g H2 H3 H4; subst; rewrite H2 in H3.
    by move=> s st st1 st2 r H H1 IH g H2 H3 H4; subst; rewrite H2 in H3.
  by move=> s g g' H H1 IH g2 g3 + H3; rewrite H => -[] ?; subst.
Qed.

Lemma not_cut_brothers_cut {s A B}:
  not_cut_brothers s A -> expand s A = CutBrothers B -> False.
Proof. by move=> H; elim: H B; congruence. Qed.

Lemma not_cut_brothers_split {s A B sol st}:
  not_cut_brothers s (And A B) ->
    not_cut_brothers s A /\ (run s A (Done sol) st -> not_cut_brothers sol B).
Proof.
  remember (And _ _) as NA eqn:HNA.
  move=> H.
  move: A B sol st HNA.
  elim: H; clear.
  + move=> sol s ? H A B sol1 A' ?; subst.
    move: H => //=.
    case E: expand => //=.
    case F: expand => //= -[] ?; subst.
    split.
      - by apply: not_cut_brothers_solved E.
      - by move=> H1; destruct (run_Solved_id E H1); subst; apply: not_cut_brothers_solved F.
  + move=> s g + A B sol A' ?; subst => //=.
    case E: expand => //=.
    - move=> _; split.
      by apply: not_cut_brothers_failure.
      by move=> H; destruct (run_Failure_and_Done E H).
    - case F: expand => //=.
      move=> _; split.
      by apply: not_cut_brothers_solved E.
      move=> H; destruct (run_Solved_id E H); subst.
      by apply: not_cut_brothers_failure.
  + move=> s g g' + H1 IH A B sol A' ?; subst => //=.
    case E: expand => [|||sol'] //=.
    - move=> [] ?; subst.
      move: IH => /(_ _ _ sol A' erefl) [] H2 H3; split.
      - by apply: not_cut_brothers_expanded E H2.
      - by move=> H; apply H3; inversion H; subst; clear H; congruence.
    - case F: expand => [A''|||] //= -[] ?; subst.
      split.
      - by apply: not_cut_brothers_solved E.
      - move=> H.
        destruct (run_Solved_id E H); subst.
        move: IH => /(_ _ _ sol' A' erefl) => -[] H2 H3. 
        by apply: not_cut_brothers_expanded F (H3 H).
Qed.

Lemma expand_cut_cut {s A B}: expand s (cut A) = CutBrothers B -> B = cut A.
Proof.
  move: s B.
  elim: A => //=.
    by move=> s IH [] s' A s'' B //=; case E: expand => //=; case F: expand.
  move=> s0 IH0 s1 IH1 s A; case E: expand => //=.
    by move=> [] ?; subst; move: (IH0 _ _ E) => ?; subst.
  case F: expand => //= -[] ?; subst.
  by move: (IH1 _ _ F) => ?; subst.
Qed.

Lemma expand_cut_expanded {s A B}: expand s (cut A) = Expanded B -> B = cut A.
Proof.
  move: s B.
  elim: A => //=.
    move=> s IH [] s' A s'' B //=; case E: expand => //=.
    + by move=> [] ?; subst; f_equal; apply: IH E.
    + by move=> [] ?; subst; apply expand_cut_cut in E; subst; rewrite cut_cut_same.
    + case F: expand => //=.
      - move=> [] ?; subst. admit. (* enrico *)
      - by move=> [] ?; subst; apply expand_cut_cut in F; subst.
  move=> s0 IH0 s1 IH1 s A; case E: expand => //=.
    by move=> [] ?; subst; move: (IH0 _ _ E) => ?; subst.
  case F: expand => //= -[] ?; subst.
  by move: (IH1 _ _ F) => ?; subst.
Admitted.

Lemma run_cut_cut s B SOL X:
  run s (cut B) (Done SOL) X ->
    exists Y, run s B (Done SOL) Y.
Proof.
  remember (cut _) as CUT eqn:HCUT.
  remember (Done _) as D eqn:HD.
  move=> H.
  move: B SOL HCUT HD.
  elim: H; clear => //=.
  + move=> A ? ? H B SOL ? [] ?; subst.
    move: A SOL H.
Abort.

Lemma expand_cut_fail {s A SOL}:
  expand s (cut A) = Solved SOL -> False.
Proof.
  move: s SOL.
  elim: A => //=; clear.
  + move=> s IH [] //= s' A s'' SOL.
    case E: expand => //=.
    + case F: expand => //= -[] ?; subst.
      admit. (* enrico *)
    + by move=> [] ?; subst; apply: IH E.
  + move=> s IH1 A IH2 s' SOL.
    case E: expand => //=.
    case F: expand => //= -[] ?; subst.
    apply: IH2 F.
Admitted.

Lemma run_cut_fail {s A SOL X} :
  run s (cut A) (Done SOL) X -> False.
Proof.
  remember (cut A) as C eqn:HC.
  remember (Done SOL) as D eqn:HD.
  move=> H.
  move: A SOL HC HD.
  elim: H; clear => //=.
  + by move=> ??? H ?? ? [] ?; subst; apply: expand_cut_fail H.
  + move=> s st st1 st2 r H H1 IH A SOL ??; subst.
    by apply expand_cut_cut in H; subst; apply: IH erefl erefl.
  + move=> s st st1 st2 r H H1 IH A SOL ??; subst.
    by apply expand_cut_expanded in H; subst; apply: IH erefl erefl.
Qed.

Inductive chooseB : Sigma -> state -> state -> state -> Prop :=
  | chooseB_CB s A cb B : expand s A = CutBrothers cb -> chooseB s A B (cut B)
  | chooseB_Fail s A B : expand s A = Failure -> chooseB s A B B
  | chooseB_Done s s' A B : expand s A = Solved s' -> chooseB s A B B
  | chooseB_Exp s A A' B B' : expand s A = Expanded A' -> chooseB s A' B B' -> chooseB s A B B'
  .

Lemma chooseBP {s A B C} :
  chooseB s A (cut B) C -> cut B = C.
Proof.
  remember (cut _) as CC eqn:HCC.
  move=> H; move: B HCC.
  elim: H; clear => //=.
  by intros; subst; rewrite cut_cut_same.
Qed.

Lemma chooseBP1 {s A X}:
  not_cut_brothers s A ->
    chooseB s A X X.
Proof.
  move=> H.
  elim: H X; clear.
  by move=> ??? H ?; apply: chooseB_Done H.
  by move=> ?? H ?; apply: chooseB_Fail H.
  by move=> ??? H H1 IH ?; apply: chooseB_Exp H (IH _).
Qed.


Lemma run_or_success {s1 s2 A B SOL E}:
  run s1 (Or A (s2, B)) (Done SOL) E ->
    (exists A' B', chooseB s1 A B B' /\ E = Or A' (s2, B') /\ run s1 A (Done SOL) A') \/ 
      exists A' B', run s1 A Failed A' /\ E = (Or A' (s2, B')) /\ run s2 B (Done SOL) B'.
Proof.
  move=> H.
  remember (Or _ _) as O eqn:HO.
  remember (Done _) as D eqn:HD.
  move: s2 A B SOL HO HD.
  elim: H; clear => //=.
  + move=> s st s' + s2 A B SOL ? [] ?; subst => //=.
    case E: expand => //=.
      case F: expand => //= -[] ?; subst.
      by right; exists A, B; repeat split; auto; [apply: run_fail E| apply: run_done].
    move=> [] ?; subst; left.
    exists A; eexists.
    split.
    apply: chooseB_Done E.
    by split; auto; apply run_done.
  + move=> s ? st1 st2 ? + H1 IH s2 A B SOL ? ?; subst => /=.
    case E: expand => //=.
    by case F: expand => //=.
  + move=> s ? st1 st2 ? + H1 IH s2 A B SOL ?? ; subst => //=.
    case E: expand => [s4|||s4] //=.
    + move=> [] ?; subst.
      move: (IH _ _ _ _ erefl erefl) => [H|[A' [B' [H [? H0]]]]] {IH}; subst.
      - move: H => [A' [B' [H [H0 H2]]]]; subst.
        left; do 2 eexists.
        split.
        apply: chooseB_Exp E H.
        split; [reflexivity | apply: run_step E H2 ].
      - by right; exists A', B'; repeat split; auto; apply: run_step E H.
    + move=> [] ?; subst.
      {
      move: (IH _ _ _ _ erefl erefl) => [H|[A' [B' [H [? H0]]]]] {IH}; subst.
      - move: H => [A' [B' [H [H0 H2]]]]; subst.
        left; do 2 eexists.
        apply chooseBP in H; split; subst.
        apply: chooseB_CB E.
        split; [reflexivity|apply: run_cut E H2].
      - by right; exists A', B'; split; auto; apply run_cut_fail in H0.
      }
    + case F: expand => [ss|ss||] //=.
      - move=> [] ?; subst.
        move: (IH _ _ _ _ erefl erefl) => [H|[A' [B' [H [? H0]]]]] {IH}; subst.
        move: H => [A' [B' [H [H0 H2]]]]; subst.
        by destruct (run_Failure_and_Done E H2).
        right; exists A', B'; repeat split; auto; apply: run_step F H0.
      - move=> [] ?; subst.
        move: (IH _ _ _ _ erefl erefl) => [H|[A' [B' [H [? H0]]]]] {IH}; subst.
        move: H => [A' [B' [H [H0 H2]]]]; subst.
        by destruct (run_Failure_and_Done E H2).
        by right; exists A', B'; repeat split; auto; apply: run_cut F H0.
Qed. 

Lemma run_or_fail {s1 s2 g1 g2 st}:
  run s1 (Or g1 (s2,g2)) Failed st ->
    run s1 g1 Failed st /\ (not_cut_brothers s1 g1 -> run s2 g2 Failed st).
Proof.
  move=> H.
  remember (Or _ _) as O eqn:HO.
  remember Failed as F eqn:HF.
  move: s2 g1 g2 HO HF.
  elim: H; clear => //=.
  + move=> s st s' + s2 g1 g2 HO _; subst => /=.
    case E: expand => //=.
    case F: expand => //=.
    by move=> _; split; intros; apply run_fail.
  + move=> s ? st1 st2 ? + H1 IH s2 g1 g2 ? ?; subst => /=.
    case E: expand => //=.
    by case F: expand => //=.
  + move=> s ? st1 st2 ? + H1 IH s2 g1 g2 ?? ; subst => //=.
    case E: expand => [s4|||s4] //=.
    + move=> [] ?; subst.
      move: (IH _ _ _ erefl erefl) => [] HL HR {IH}.
      split; [by apply: run_step E _|] => H.
      inversion H1; subst; clear H1; move: H0 => //=.
      + case F: expand => //=; case: expand => //= _.
        apply: HR (not_cut_brothers_failure F).
      + by case F: expand => //=; case G: expand => //=.
      + by epose proof (not_cut_brothersP E H HL); auto.
    + move=> [] ?; subst.
      move: (IH _ _ _ erefl erefl) => [] HL HR.
      split; [by apply: run_cut E HL|] => H.
      inversion H; clear H; subst; rewrite E in H0 => //=.
    + case F: expand => //= -[] ?; subst.
      - move: (IH _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_step F (HR HH).
      - move: (IH _ _ _ erefl erefl) => [] HL HR; split; [by []|] => HH.
        by apply: run_cut F (HR HH).
Qed. 

Corollary run_or_fail1 s1 g1 g2 st:
  run s1 (Or g1 (s1,g2)) Failed st ->
    run s1 g1 Failed st /\ (not_cut_brothers s1 g1 -> run s1 g2 Failed st).
Proof. move=> H. apply: run_or_fail H. Qed. 

Lemma not_cut_brothers_choosB {s A B C}:
  chooseB s A B C ->
    not_cut_brothers s A ->
      C = B.
Proof.
  move=> H.
  elim: H => //=; clear.
  by move=> s A C B + H; inversion H; subst => //=; congruence.
  move=> s A A' B B' + H IH H1.
  inversion H1; subst; clear H1; try congruence.
  rewrite H0 => -[] ?; subst.
  auto.
Qed.

Lemma chooseB_expanded_and_left {s A B X Y ss}:
  chooseB s (And A B) X Y ->
    expand s A = Expanded ss ->
      chooseB s (And ss B) X Y.
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss.
  elim: H; clear => //=.
  by move=> s A B C + A1 B1 ?? H; subst => //=; rewrite H.
  by move=> ??? + ???? H; subst => //=; rewrite H.
  by move=> ???? + ???? H; subst => //=; rewrite H.
  by move=> s A A' B B' + HC IH A0 B0 ? ? H; subst => //=; rewrite H => -[] ?; subst.
Qed.

Lemma chooseB_expanded_and_right {s A B B2 X Y ss}:
  chooseB s (And A B) X Y ->
    expand s A = Solved ss ->
      expand ss B = Expanded B2 ->
        chooseB s (And A B2) X Y.
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B B2 HAnd ss.
  case: H; clear => //=.
  by move=> s A B C + ????? H H1; subst => //=; rewrite H H1.
  by move=> ??? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ???? + ????? H H1; subst => //=; rewrite H H1.
  by move=> s A A' B B' + HC ????? H H1; subst => //=; rewrite H H1 => -[] ?; subst.
Qed.

Lemma not_cut_borothers_expanded_and_left {s A B ss}:
  not_cut_brothers s (And A B) ->
    expand s A = Expanded ss ->
      not_cut_brothers s (And ss B).
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss.
  case: H; clear => //=.
  by move=> ??? + ???? H; subst => //=; rewrite H.
  by move=> ?? + ???? H; subst => //=; rewrite H.
  by move=> ??? + H1 ???? H2; subst => //=; rewrite H2 => -[] ?; subst; auto.
Qed.

Lemma not_cut_borothers_expanded_and_right {s A B B'' ss}:
  not_cut_brothers s (And A B) ->
    expand s A = Solved ss ->
    expand ss B = Expanded B'' ->
      not_cut_brothers s (And A B'').
Proof.
  remember (And _ _) as And eqn:HAnd.
  move=> H.
  move: A B HAnd ss B''.
  case: H; clear => //=.
  by move=> ??? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ?? + ????? H H1; subst => //=; rewrite H H1.
  by move=> ??? + H1 H2 ???? H3 H4; subst => //=; rewrite H3 H4 => -[] ?; subst; auto.
Qed.

Inductive will_fail : Sigma -> state -> Prop :=
  | will_fail1 {s st} : expand s st = Failure -> will_fail s st
  | will_fail2 {s st st'} : expand s st = Expanded st' -> will_fail s st' -> will_fail s st.

(* ((A ∧ B) ∨ (A ∧ C)) -> (A ∧ (B ∨ C)) *)
Lemma or_is_distributive {A B C s sol E}:
    run s (Or (And A B) (s, (And A C))) (Done sol) E ->
      not_cut_brothers s (And A B) ->
        exists E' s' IGN, run s A (Done s') IGN /\
          run s (And A (Or B (s', C))) (Done sol) E' 
          (* /\ (forall x s r, run x E s r <-> run x E' s r) *)
            .
Proof.
  move=> H H1.
  apply run_or_success in H as [[A' [B' [H [? H0]]]]|[A' [C' [H [? H0]]]]]; subst.
  (* left succeeds *)
  + remember (And A B) as AB eqn:HAB.
    remember (And A C) as AC eqn:HAC.
    remember (Done sol) as SOL eqn:HSOL.
    move: A B C sol B' AC HSOL HAC HAB H H1.
    {
      elim: H0 => //=; clear.
      + move=> s0 st s' + A B C sol B' ? [] ??? H1 H2; subst => //=.
        case E: expand => //=.
        case F: expand => //= -[] ?; subst.
        do 3 eexists; repeat split; [by apply: run_done E|]; by apply: run_done => //=; rewrite E F.
      + move=> s st st1 st2 r H H1 IH A B C sol B' ? ??? H2 H3; subst.
        by destruct (not_cut_brothers_cut H3 H).
      + move=> s st st1 st2 r + H1 IH A B C sol B' ???? H2 H3; subst => //=.
        case E: expand => [ss|||ss] //=.
        + move=> []?; subst.
          move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl).
          assert (chooseB s (And ss B) (And ss C) (And ss C)) by
            apply: chooseB_expanded_and_left (chooseBP1 H3) E.
          assert (not_cut_brothers s (And ss B)) by
            apply: not_cut_borothers_expanded_and_left H3 E.
          move=> /(_ _ _ H0 H4) [A1 [A2 [A3 [A4 A5]]]].
          do 3 eexists; split.
          apply: run_step E A4.
          apply: run_step => //=; [by rewrite E|]; apply A5.
        + case F: expand => [B''|||] //= -[] ?; subst.
          assert (chooseB s (And A B'') (And A C) (And A C)) as H0 by
            apply: chooseB_expanded_and_right (chooseBP1 H3) E F.
          assert (not_cut_brothers s (And A B'')) as H00 by
            apply: not_cut_borothers_expanded_and_right H3 E F.
          move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl H0 H00) [A1 [A2 [A3 [A4 A5]]]].
          do 3 eexists; split.
          eassumption.
          by apply: run_step A5 => //=; rewrite E F.
    }
  (* left fails *)
  + remember (And A B) as AB eqn:HAB.
    remember Failed as fail eqn:Hfail.
    move: C' sol A B C Hfail HAB H0 H1.
    elim: H; clear => //=.
    + move=> s st _ + C' sol A B C _ ? H1 H2; subst => //=.
      { case E: expand => //=.
        { inversion H1; subst => //=.
          by move: H5 => //=; rewrite E.
          by move: H0 => //=; rewrite E.
          by move: H0 => //=; rewrite E. }
        case F: expand => //=.
        do 3 eexists; split; [apply: run_done E|].
        + inversion H1; subst; clear H1 => //=.
          move: H6 => //=; rewrite E.
          case G: expand => //=.
          move=> []?; subst.
          { apply: run_done => //=.
            rewrite E.
            rewrite F.
            rewrite G => //=.
          }
        + move: H3 => //=; rewrite E.
        admit.
        admit.
        }
    + move=> s st st1 st2 r H H1 IH C sol A B C' ?? H2 H3; subst.
      by destruct (not_cut_brothers_cut H3 H).
    + move=> s st st1 st2 r + H1 IH C' sol A B C ?? H2 H3; subst => //=.
      inversion H2; subst; clear H2.
      {
        move: H6 => //=; case E: expand => //= [s'].
        case F: expand => //= -[]? ; subst.
        case G: expand => //= [WRONG] -[]?; subst.
        epose proof (not_cut_borothers_expanded_and_right H3 E G).
        assert (exists x, run s (And A (Or B (s', C))) (Done sol) x).
        { eexists.
          apply: run_step => //=.
          rewrite E G => //=.
          assert (expand s' WRONG = Failure).
          {
            inversion H1; subst; move : H2 => //=; rewrite E; case GG: expand => //=.
            - eapply not_cut_brothers_split in H0 as [].
              pose proof (run_done E).
              apply H2 in H5.
              by epose proof (not_cut_brothers_cut H5 GG).
            - move=> -[] ?; subst; inversion H4; subst; clear H4; move: H2 => //=; rewrite E; case EE: expand => //=.
            all: admit.

          }
Abort.

Print expand.
Lemma done_fail {s}: Done s <> Failed. by []. Qed.

Lemma p_aorb_andc {sA sB sD A B C D E}:
  run sA (And (Or A (sB, B)) C) (Done sD) D ->
    run sA (And A C) Failed E ->
      exists D', run sB (And B C) (Done sD) D'.
Proof.
  move=> H H1.
  move: (run_and_succeed H) => [il[ir[s'' [?[HAORB HC]]]]] {H}; subst.
  move: (run_or_success HAORB) => [] {HAORB}.
    + move=> [A' [B' [HChA [? HA]]]]; subst.
      move: (run_and_fail H1) => {H1} [HA'|].
      + by move: (run_consistent HA HA') => [].
      + move=> [s [st [HA' HC']]].
        move: (run_consistent HA HA') => [[?]] /(_ done_fail) ?; subst.
        by move: (run_consistent HC HC') => [].
    + move=> [A' [B' [HA [? HB]]]]; subst.
      exists (And B' ir).
      apply: run_and_succeed1 HB HC.
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

  (* Inductive infer : Gamma -> Tm -> S -> bool -> Prop :=
    | infer_var  {G V}: infer G (Code (v V)) (G V) true
    | infer_pred {G C}: infer G (Code (p C)) (G C) true
    | infer_app_hd_false {G t1 t2 r} : 
      infer G t1 r false ->
      infer G (Comb t1 t2) r false
    | infer_app_bo_false {G t1 t2 r} : 
      infer G t2 r false ->
      infer G (Comb t1 t2) r false
    | infer_app {G t1 t2 r1 r2} :
      infer G t1 r1 true ->
        infer G t2 r2 true ->
          infer G (Comb t1 t2) (eat r1 r2) (incl r1 r2). *)

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

  (* Inductive assume : S -> Tm -> Gamma -> Gamma -> Prop :=
  | assume_var {D G1 V}: assume D (Code (v V)) G1 (update_gamma G1 V (min (G1 V) D))
  | assume_app {D G1 G2 l r dl dr} :
    infer G1 l (arr i dl dr) true -> incl dr D ->
      assume dl r G1 G2 ->
        assume D (Comb l r) G1 G2
  | assume_pred {D G P}: assume D (Code (p P)) G G. *)

  (* Inductive assume_output : S -> Tm -> Gamma -> Gamma -> Prop :=
  | assume_var {D G1 V}: assume D (Code (v V)) G1 (update_gamma G1 V (min (G1 V) D))
  | assume_app {D G1 G2 l r dl dr} :
    infer G1 l (arr i dl dr) true -> incl dr D ->
      assume dl r G1 G2 ->
        assume D (Comb l r) G1 G2
  | assume_pred {D G P}: assume D (Code (p P)) G G. *)

Inductive check : program -> A -> Gamma -> S -> Gamma -> S -> Prop :=
  | check_cut {P G _Ign} : check P Cut G _Ign G (b (d Func))
  | check_comb : 
    


Inductive D : Set :=   Func : D | Pred : D.
Inductive S : Set :=   b : B -> S | arr : mode -> S -> S -> S.
Inductive B : Set :=   Exp : B | d : D -> B.
  Inductive Tm : Set :=   
    | Code : C -> Tm 
    | Data : K -> Tm 
    | Comb : Tm -> Tm -> Tm.
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
  (* | v of V *)
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
  | OK => OK
  | KO => KO
  | CutOut => CutOut
  end.

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
  (* | Goal pr (App (v _) _) => Failure *)
  | Goal pr (App (p pn) args) =>
      let l := F pr pn args s in
      if l is [:: (s1,_) & _] then Expanded (big_or pr l)
      else Failure
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
  by move=> s st st1 st2 r H H1 ?; rewrite H.
  by move=> s st st1 st2 ? H ; rewrite H.
Qed.

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
    - move=> [] pn args s2 s3 st2 ir1 ir2; by case: F => [|[]] //=.
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
  by move=> pr [] // [p args] s s' s''' il; case: F => // -[] //.
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

Lemma test_and_succeed s g1 g2 s' st :
  run s (And g1 g2) (Done s') st ->
    exists il ir s'',  st = And il ir /\ run s g1 (Done s'') il /\ run s'' g2 (Done s') ir.
Proof.
  remember (And _ _) as g0 eqn:Hg0.
  remember (Done _) as s1 eqn:Hs1.
  move => H.
  move: g1 g2 Hg0 s' Hs1.
  elim: H => {st s s1 g0} /= [s st s'|s st|s st st1 st2 r|].
  - move=> + st_l st_r ? r [?]; subst.
    rewrite expand_And. case L: expand => [|||x] //. case R: expand => //.
    move=> /= [?]; subst.
    by exists st_l, st_r, x; split => //; split; constructor.
  - by [].
  - move=> + Hr IH st_l st_r ? s'' ?; subst.
    rewrite expand_And. 
    {
      case L: expand => [|st0||s'] // => [[?]|]; subst.
    - move: (IH _ _ erefl _ erefl) => [il [ir [s']]] [-> [ IHl IHr]] {IH}.
      exists il, ir, s'; split=> //; split.
      by apply: run_cut L IHl.
      by apply: IHr.
    - case R: expand => //= -[?]; subst.
      move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [-> [ IHl IHr]] {IH}.
      exists il, ir, s'''; split=> //; split.
        by apply: IHl.
      {
        pose proof (run_solved_same_subst L IHl).
        subst.
        apply: run_cut.
        apply R.
        auto.
      }
    }
    move=> s ? A' C ? + H1 IH A B ? s' ?; subst => //=.
    case E1: expand => [|||s1] //=.
      - move=> [?]; subst.
        move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [-> [ IHl IHr]] {IH}.
        exists il, ir, s'''; split => //; split=>//.
        by apply: run_step E1 IHl.
      - case E2: expand => [st|||] //= [] ?; subst.
        move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [? [ IHl IHr]] {IH}; subst.
        exists il, ir.
        pose proof (run_Solved_id E1 IHl) as []; subst.
        exists s1; repeat split; auto.
        apply: run_step E2 IHr.
Qed.

Lemma test_and_fail s g1 g2 st:
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

Lemma run_or_fail s1 s2 g1 g2 st:
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





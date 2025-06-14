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
  | OK : state
  | Goal : program  -> A -> state
  | Or  : state -> Sigma -> state -> state
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
  | Expanded st => Expanded (Or left sr st)
  | CutBrothers st => Expanded (Or left sr st) (* for now this is the rightmost brother *)
  | Solved s => Solved s
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
  | OK => Solved s
  | CutOut => Failure
  | Goal _ Cut  => CutBrothers OK
  | Goal pr (App (v _) _) => Failure
  | Goal pr (App (p pn) args) =>
      let l := F pr pn args s in
      if l is [:: (s1,_) & _] then Expanded (big_or pr l)
      else Expanded KO
  | Or st1 sr st2 =>
      match expand s st1 with
      | Solved s => Solved s
      | Expanded st1 => Expanded (Or st1 sr st2)
      | CutBrothers st1 => Expanded (Or st1 sr (cut st2))
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
  remember (Done s2) as D eqn:HD.
  case: H HD => //=; clear.
  by move=> s st1 s3 H1 [] ?; rewrite H1=> -[] ?; subst.
  by move=> s st st1 st2 r H H1 ?; rewrite H.
  by move=> s st st1 st2 ? H ; rewrite H.
Qed.

Lemma run_Failure_and_Done {s A sol A'}:
  expand s A = Failure -> run s A (Done sol) A' -> False.
Proof. by inversion 2; subst; congruence. Qed.

Lemma run_Solved_and_Failed {s A sol A'}:
  expand s A = Solved sol -> run s A Failed A' -> False.
Proof. inversion 2; subst; congruence. Qed.

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

Lemma run_cut_simpl pr s3 s4 s2:
  run s3 (Goal pr Cut) (Done s2) s4 -> expand s3 OK = Solved s2 /\ s4 = OK.
Proof.
  inversion 1; subst => //=.
  move: H1 => //= [] ?; subst.
  inversion H2; subst => //.
Qed.

Lemma run_solved_same_subst {A s1 s2 s3 B}:
   expand s1 A = Solved s2 ->
    run s1 A (Done s3) B ->
      s2 = s3.
Proof.
  remember (Done _) as D eqn:HD.
  move=> + H.
  elim: H s2 s3 HD; clear.
  + by move=> s1 A s2 H s3 ? [] <-; rewrite H => -[].
  + by congruence.
  + by congruence.
  + by congruence.
Qed.

Lemma run_and_complete {s g1 g2 s' st} :
  run s (And g1 g2) (Done s') st ->
    (exists il ir s'', st = And il ir /\ run s g1 (Done s'') il /\ run s'' g2 (Done s') ir).
Proof.
  remember (And _ _) as g0 eqn:Hg0.
  remember (Done _) as s1 eqn:Hs1.
  move => H.
  move: g1 g2 Hg0 s' Hs1.
  elim: H => {st s s1 g0} /= [s st s'|s st|s st st1 st2 r|] => //=.
  - move=> + st_l st_r ? r [?]; subst => //=.
    case L: expand => [|||x] //; case R: expand => //= -[?]; subst.
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

Lemma run_and_correct {s0 s1 s2 g1 g2 il ir} :
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

Inductive expand_no_cut_failure : Sigma -> state -> state -> Prop :=
  | expand_no_cut_failure_fail {s st} :
      expand s st = Failure ->
      expand_no_cut_failure s st st
  | expand_no_cut_failure_step {s st st1 st2} :
      expand s st = Expanded st1  ->
      expand_no_cut_failure s st1 st2 ->
      expand_no_cut_failure s st st2
.

Inductive expand_no_cut : Sigma -> state -> Prop :=
  | expand_no_cut_solved {s' s g} : expand s g = Solved s' -> expand_no_cut s g
  | expand_no_cut_failure1 {s g}    : expand s g = Failure   -> expand_no_cut s g
  | expand_no_cut_expanded {s g g'} : 
    expand s g = Expanded g' -> expand_no_cut s g' -> expand_no_cut s g.

Lemma expand_no_cutP {s1 g1 g2 g3}:
  expand s1 g1 = Expanded g2 -> 
    expand_no_cut s1 g1 ->
      run s1 g2 Failed g3 ->
        expand_no_cut s1 g2.
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
    by move=> s st _ H g H1 H2 _; apply: expand_no_cut_failure1 H.
    by move=> s st st1 st2 r H H1 IH g H2 H3 H4; subst; rewrite H2 in H3.
    by move=> s st st1 st2 r H H1 IH g H2 H3 H4; subst; rewrite H2 in H3.
  by move=> s g g' H H1 IH g2 g3 + H3; rewrite H => -[] ?; subst.
Qed.

Lemma expand_cut_fail {s A SOL}:
  expand s (cut A) = Solved SOL -> False.
Proof.
  elim: A s SOL => //=.
  + move=> s IH s' A H s'' SOL //=.
    case E: expand => //=.
    + case F: expand => //= -[] ?; subst.
      apply: H F.
    + by move=> [] ?; subst; apply: IH E.
  + move=> s IH1 A IH2 s' SOL.
    case E: expand => //=.
    case F: expand => //= -[] ?; subst.
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
      apply: expand_cut_fail X.
Qed.

Lemma expand_cut_expanded {s A B}: expand s (cut A) = Expanded B -> False.
Proof.
  elim: A s B => //=; clear.
    move=> s IH s' A H s'' B //=; case E: expand => //=.
    + by move=> [] ?; subst; f_equal; apply: IH E.
    + by move: (expand_cut_CB E).
    + case F: expand => //=.
      - move=> [] ?; subst.
        by move: (H _ _ F) => ?; subst.
      - by move: (expand_cut_CB F).
  move=> s0 IH0 s1 IH1 s A; case E: expand => //=.
    by move=> [] ?; subst; move: (IH0 _ _ E) => ?; subst.
  case F: expand => //= -[] ?; subst.
  by move: (IH1 _ _ F) => ?; subst.
Qed.

Axiom classic : forall P : Prop, P \/ ~ P.

Lemma expand_cut_result {s A r}:
  expand s (cut A) = r -> (exists B, r = Expanded B) \/ r = Failure.
Proof.
  elim: A s r => //=; auto.
  + move=> A IH a A' HA' s r //=.
    case H: expand => //=.
    + by move=>?; subst; left; eexists.
    + by move=>?; subst; left; eexists.
    + case X: expand => //=?; subst; auto.
      + by left; eexists.
      + by left; eexists.
      + apply: HA' X.
    + apply IH in H as [[]|?] => //=.
  + move=> s1 IH1 s2 IH2 s3 r.
    case H: expand => ?; subst; auto.
    + by left; eexists.
    + apply IH1 in H as [[]|?] => //=.
    + apply IH1 in H as [[]|?] => //=.
Qed.

Lemma expand_cut_result1 s A:
  expand s (cut A) = Failure \/ exists x, expand s (cut A) = (Expanded x).
Proof.
  case X: (expand s (cut A)).
  + by right; eexists.
  + by move: (expand_cut_CB X).
  + by left.
  + by move: (expand_cut_fail X).
Qed.

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
    by move: (expand_cut_CB H).
  + move=> s st st1 st2 r H H1 IH A SOL ??; subst.
    by apply expand_cut_expanded in H.
Qed.

Inductive expand_all: Sigma -> state -> expand_res -> Prop :=
  | expand_all_done {s st r} : expand s st = (Solved r) -> expand_all s st (Solved r)
  | expand_all_fail {s st} : expand s st = Failure -> expand_all s st Failure
  | expand_all_cut {s st st1 r} : expand s st = CutBrothers st1 -> expand_all s st1 r -> expand_all s st r
  | expand_all_exp {s st st1 r} : expand s st = Expanded st1 -> expand_all s st1 r -> expand_all s st r.

Lemma run_expand_all_solved {s0 s1 s2 A B}:
  expand_all s0 A (Solved s2) -> run s0 A (Done s1) B -> s1 = s2.
Proof.
  remember (Solved s2) as S eqn:HS => H.
  elim: H s1 s2 B HS; clear => //=.
  + by move=> s0 A r H s1 s2 B []<- H1; move: (run_solved_same_subst H H1).
  + all:
    move=> s0 A AC ? H1 H2 IH s1 s2 B ? H3; inversion H3; clear H3; try congruence; subst; 
    move: H0; rewrite H1 => -[]?; subst; by apply: IH erefl H4.
Qed.

Lemma expand_no_cut_failure_split {s A B AB}: 
  expand_no_cut_failure s (And A B) AB ->
    (exists X, expand_no_cut_failure s A X) \/ (exists s' X, expand_all s A (Solved s') /\ expand_no_cut_failure s' B X).
Proof.
  remember (And A B) as And eqn:HAnd.
  move=> H; elim: H A B HAnd; clear.
  + move=> s ? + A B ?; subst => //=.
    case X: expand => //=.
    + by left; eexists A; apply: expand_no_cut_failure_fail.
    + case Y: expand => //= _; right; do 2 eexists; split.
      + apply: expand_all_done X.
      + by apply: expand_no_cut_failure_fail.
  + move=> s st st1 st2 + H1 + A B ?; subst => //=.
    case X: expand => //=.
    + move=> []?;subst.
      move=> /(_ _ _ erefl) [] [].
      + move=> X1 H; left; eexists; apply: expand_no_cut_failure_step X H.
      + move=> X1 [X2 [H2 H3]]; right.
        do 2 eexists; split.
        + apply: expand_all_exp X H2.
        + apply: H3.
    + case Y: expand => //= [A'] [] ?; subst.
      move=> /(_ _ _ erefl) [].
      + by left.
      + move=> [s' [B' [H2 H3]]]; right.
        do 2 eexists; split; try eassumption.
        inversion H2; subst; try congruence; clear H2.
        move: H6; rewrite X => -[]?; subst.
        by apply: expand_no_cut_failure_step Y H3.
Qed.

Lemma run_or_done_cut {s1 s2 SOL A A' B}:
  run s1 A (Done SOL) A' ->
  run s1 (Or A s2 (cut B)) (Done SOL) (Or A' s2 (cut B)).
Proof.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H s2 SOL B HD; clear => //=.
  + move=> s st s' H s2 SOL B [] ?; subst.
    by apply: run_done => //=; rewrite H.
  + move=> s st st1 st2 r H H1 IH s2 SOL B H2; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by rewrite cut_cut_same; apply: IH erefl.
  + move=> s st st1 st2 r H H1 IH s2 SOL B0 ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + by apply: IH.
Qed.

Lemma run_or_done_cut1 {s1 s2 SOL A A' B B'}:
  run s1 (Or A s2 (cut B)) (Done SOL) (Or A' s2 B') -> B' = (cut B).
Proof.
  remember (Or A _ _) as O1 eqn:HO1.
  remember (Or A' _ _) as O2 eqn:HO2.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H s2 A A' B B' SOL HO1 HO2 HD; clear => //=.
  + by move=> s st s' H s2 A A' B B' SOL H1; rewrite H1 => -[] ?? [] ?; subst.
  + move=> s st st1 st2 r + H1 IH s2 A A' B B' SOL ???; subst => //=.
    by case E: expand => //=; case: expand => //=.
  + move=> s st s1 st2 r + H1 IH s2 A A' B B' SOL ???; subst => //=.
    case E: expand => //=.
    + by move=> []?; subst; apply: IH erefl erefl erefl.
    + by move=> []?; subst; apply: IH erefl erefl; rewrite cut_cut_same.
    + case F: expand => //=.
      + by move: (expand_cut_expanded F).
      + by move: (expand_cut_CB F).
Qed.

Lemma run_or_correct_left {s1 A SOL A'}:
  run s1 A (Done SOL) A' ->
    forall s2 B, exists B', run s1 (Or A s2 B) (Done SOL) (Or A' s2 B').
Proof.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H SOL HD => //=; clear.
  + move=> s st s' H SOL [] ? s2 B; subst.
    by exists B; apply: run_done => //=; rewrite H.
  + move=> s A st1 st2 r H H1 IH SOL ? s2 B; subst.
    exists (cut B).
    apply: run_step => //=.
    + by rewrite H.
    + apply: run_or_done_cut H1.
  + move=> s st st1 st2 r H H1 IH SOL ? s2 B; subst.
    move: (IH SOL erefl s2 B) => [B' H2].
    exists B'; apply: run_step _ H2 => //=.
    by rewrite H.
Qed. 

Lemma run_or_correct_right {s1 s2 A B SOL A' B'}:
  expand_no_cut_failure s1 A A' -> run s2 B (Done SOL) B' ->
    (exists B', run s1 (Or A s2 B) (Done SOL) (Or A' s2 B')).
Proof.
  move=> H.
  elim: H s2 B B' SOL; clear.
  + move=> + + + s2 B B' SOL H1.
    remember (Done SOL) as DS eqn:HDS.
    elim: H1 SOL HDS => //=; clear.
    + move=> s2 B SOL H SOL' [] ? s1 A H1; subst.
      by eexists; apply: run_done =>//=; rewrite H1 H.
    + move=> s2 B BC B' r H H1 + SOL ? s1 A H2; subst.
      move=> /(_ _ erefl _ _ H2) [B2 IH]; eexists.
      apply: run_step _ IH => //=.
      by rewrite H2 H.
    + move=> s2 B BE B' r H H1 + SOL ? s1 A H2; subst.
      move=> /(_ _ erefl _ _ H2) [B2 IH]; eexists.
      apply: run_step _ IH => //=.
      by rewrite H2 H.
  + move=> s1 A EA A' H H1 + s2 B B' SOL H2.
    move=> /(_ _ _ _ _ H2) [B2 IH]; eexists.
    apply: run_step _ IH => //=.
    by rewrite H.
Qed.

Lemma run_or_correct {s1 s2 A B SOL A' B'}:
  (run s1 A (Done SOL) A') \/ 
    (expand_no_cut_failure s1 A A' /\ run s2 B (Done SOL) B') ->
      exists B', run s1 (Or A s2 B) (Done SOL) (Or A' s2 B').
Proof.
  move=> [].
  move=> H; apply: run_or_correct_left H _ _.
  move=> []; apply: run_or_correct_right.
Qed.

Lemma run_or_done {s1 s2 A B SOL r}:
  run s1 (Or A s2 B) (Done SOL) r -> exists x y, r = Or x s2 y.
Proof.
  remember (Or _ _ _) as O eqn:HO.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H s2 A B SOL HO HD; clear => //=.
  + by move=> s st s' H s2 A B SOL ? [] ?; subst; do 2 eexists.
  + move=> s st st1 st2 r + H1 IH s2 A B SOL ??; subst => //=.
    by case E: expand => //=; case E: expand => //=.
  + move=> s st st1 st2 r + H1 IH s2 A B SOL ??; subst => //=.
    case E: expand => //= [A'|A'|].
    + by move=> [] ?; subst; move: (IH s2 A' B SOL erefl erefl).
    + by move=> [] ?; subst; move: (IH s2 A' (cut B) SOL erefl erefl).
    + case F: expand => //= -[]?; subst; by move: (IH _ _ _ SOL erefl erefl).
Qed.

Lemma run_and_done {s A B SOL r}:
  run s (And A B) (Done SOL) r -> exists x y, r = And x y.
Proof.
  remember (And _ _) as O eqn:HO.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H A B SOL HO HD; clear => //=.
  + by move=> s st s' H A B SOL ? [] ?; subst; do 2 eexists.
  + move=> s st st1 st2 r + H1 IH A B SOL ??; subst => //=.
    case E: expand => //=.
    + by move=> []?; subst; apply: IH erefl erefl.
    + by case F: expand => //= -[]?; subst; apply: IH erefl erefl.
  + move=> s st st1 st2 r + H1 IH A B SOL ??; subst => //=.
    case E: expand => //= [A'|A'].
    + by move=> [] ?; subst; apply: IH erefl erefl.
    + by case F: expand => //= -[]?; subst; apply: IH erefl erefl.
Qed.

Lemma run_or_complete {s1 s2 A B SOL A' B'}:
  run s1 (Or A s2 B) (Done SOL) (Or A' s2 B') ->
    run s1 A (Done SOL) A' \/ 
      expand_no_cut_failure s1 A A' /\ run s2 B (Done SOL) B'.
Proof.
  remember (Or _ _ _) as O1 eqn:HO1.
  remember (Or A' _ _) as O2 eqn:HO2.
  remember (Done _) as D eqn:HD.
  move=> H.
  elim: H s2 A A' B B' SOL HO1 HO2 HD; clear => //=.
  + move=> s st s' + s2 A A' B B' SOL H; rewrite H => + [] ?? [] ?; subst => //=.
    case E: expand => //=.
      case F: expand => //= -[] ?; subst.
      by right; repeat split; auto; [apply: expand_no_cut_failure_fail E| apply: run_done].
    move=> [] ?; subst; left.
    apply: run_done E.
  + move=> s ? st1 st2 ? + H1 IH s2 A A' B B' SOL ???; subst => /=.
    case E: expand => //=.
    by case F: expand => //=.
  + move=> s ? st1 st2 ? + H1 IH s2 A A' B B' SOL ??? ; subst => //=.
    case E: expand => [s4|||s4] //=.
    + move=> [] ?; subst.
      move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl) [H|[HL HR]].
      - left; apply: run_step E H.
      - by right; split; [apply: expand_no_cut_failure_step E HL|assumption].
    + move=> [] ?; subst.
      move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl) [H|[HL HR]].
      - by left; apply: run_cut E H.
      - by right; split; auto; move: (run_cut_fail HR).
    + case F: expand => [ss|ss||] //=.
      - move=> [] ?; subst.
        move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl) [H|[HL HR]].
        by destruct (run_Failure_and_Done E H).
        right; split; auto; apply: run_step F HR.
      - move=> [] ?; subst.
        move: IH => /(_ _ _ _ _ _ _ erefl erefl erefl) [H|[HL HR]].
        by destruct (run_Failure_and_Done E H).
        by right; split; auto; apply: run_cut F HR.
Qed.

Lemma run_expand_no_cut_failure {s A ign} : 
  expand_no_cut_failure s A ign -> 
    run s A Failed ign.
Proof.
  move=> H; elim: H => [{}s {}st| {}s {}st st1 st2] H.
  + by apply: run_fail H.
  + by move=> _ H2; apply: run_step H H2.
Qed.

Lemma expand_no_cut_failure_expanded {s1 s2 g1 g2}:
   expand s1 g1 = Expanded s2 ->
    expand_no_cut_failure s1 g1 g2 ->
      expand_no_cut_failure s1 s2 g2.
Proof.
  move=> + H; elim: H s2; [congruence|]; clear.
  move=> s1 st st1 g2 H; rewrite H => H1 IH g1 []?; subst.
  inversion H1; clear H1; subst.
  - by apply: expand_no_cut_failure_fail.
  - by apply: expand_no_cut_failure_step (H0) _; apply IH.
Qed.

Lemma run_or_fail {s1 s2 g1 g2 st}:
  run s1 (Or g1 s2 g2) Failed st ->
    run s1 g1 Failed st /\ (expand_no_cut s1 g1 -> run s2 g2 Failed st).
Proof.
  move=> H.
  remember (Or _ _ _) as O eqn:HO.
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
        apply: HR (expand_no_cut_failure1 F).
      + by case F: expand => //=; case G: expand => //=.
      + by epose proof (expand_no_cutP E H HL); auto.
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

Lemma expand_no_cut_cut {s A B}:
  expand_no_cut s A -> expand s A = CutBrothers B -> False.
Proof. by move=> H; elim: H B; congruence. Qed.

Lemma run_Failed_cut {s s2 A B X Y}:
   run s A Failed X ->
    run s (Or A s2 (cut B)) Failed Y.
Proof.
  remember Failed as F eqn:HF.
  move=> H.
  elim: H s2 B Y HF; clear => //=.
  + move=> s A _ H s2 B Y _.
    move: (expand_cut_result1 s2 B) => [ | [D]] H1.
    + by apply: run_fail => //=; rewrite H H1.
    + by move: (expand_cut_expanded H1).
  + move=> s A st1 st2 r H H1 IH s2 B Y ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + apply: IH erefl.
  + move=> s A st1 st2 r H H1 IH s2 B Y ?; subst.
    apply: run_step => //=.
    + by rewrite H.
    + apply: IH erefl.
Qed.

Lemma run_or_fail1 {s1 s2 g1 g2 st aa}:
    run s1 g1 Failed aa -> (expand_no_cut s1 g1 -> run s2 g2 Failed st) ->
      run s1 (Or g1 s2 g2) Failed st.
Proof.
  move: (classic (expand_no_cut s1 g1)) => [].
  + move=> H + /(_ H) => H1; move: H.  
    remember Failed as F eqn:HF.
    elim: H1 s2 g2 st HF; clear => //=.
    + move=> s A _ H s2 B C _ H1 H2; subst.
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
      by move: (expand_no_cut_cut H3 H0).
    + intros; subst.
      apply: run_step=> //=.
      + by rewrite H0 => //=.
      + by apply: H2 => //=; apply: expand_no_cutP H0 H3 H1.
  + remember Failed as F eqn:HF.
    remember (Or _ _) as O eqn:HO.
    move=> H1 H _.
    elim: H H1 s2 g2 st HF O HO; clear => //=.
    + by move=> s st st1 H []; apply expand_no_cut_failure1.
    + move=> s st st1 st2 r H H1 IH H2 s2 g2 st0 ? O HO; subst.
      apply: run_step => //=.
      + rewrite H => //=.
      + apply: run_Failed_cut H1.
    + intros; subst.
      apply: run_step => //=.
      by rewrite H0.
      apply: H2; auto.
      move=> H4.
      apply H3.
      apply: expand_no_cut_expanded H0 H4.
Qed.

Lemma done_fail {s}: Done s <> Failed. by []. Qed.

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
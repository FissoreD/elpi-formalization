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
  | Expanded of state & Sigma
  | CutBrothers of state
  | Failure
  | Solved of Sigma.

Definition mkAnd left r :=
  match r with
  | Failure => Failure
  | Expanded st s => Expanded (And left st) s
  | CutBrothers st => CutBrothers (And left st)
  | Solved s => Solved s
  end.

Definition mkOr left sr r :=
  match r with
  | Failure => Failure
  | Expanded st s => Expanded (Or left (sr,st)) sr
  | CutBrothers st => Expanded (Or left (sr,st)) sr (* for now this is the rightmost brother *)
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

Fixpoint expand (st :state) s : expand_res :=
  match st with
  | KO => Failure
  | OK => Solved s
  | CutOut => Failure
  | Goal _ Cut  => CutBrothers OK
  | Goal pr (App (v _) _) => Failure
  | Goal pr (App (p pn) args) =>
      let l := F pr pn args s in
      if l is [:: (s1,_) & _] then Expanded (big_or pr l) s1
      else Expanded KO s
  | Or st1 (sr,st2) =>
      match expand st1 s with
      | Solved s => Solved s
      | Expanded st1 s => Expanded (Or st1 (sr,st2)) s
      | CutBrothers st1 => Expanded (Or st1 (sr,cut st2)) s
      | Failure => mkOr st1 sr (expand st2 sr)
      end
  | And st1 st2 =>
      match expand st1 s with
      | Solved s => mkAnd st1 (expand st2 s)
      | Expanded st1 s => Expanded (And st1 st2) s
      | CutBrothers st1 => CutBrothers (And st1 st2)
      | Failure => Failure
      end
  end
.

Lemma expand_And st1 st2 s : expand (And st1 st2) s =
      match expand st1 s with
      | Solved s => mkAnd st1 (expand st2 s)
      | Expanded st1 s => Expanded (And st1 st2) s
      | CutBrothers st1 => CutBrothers (And st1 st2)
      | Failure => Failure
      end.
by [].
Qed.


Inductive run_res := Done of Sigma | Failed.

Inductive run : Sigma -> state -> run_res -> state -> Prop :=
  | run_done s st s' :
      expand st s = Solved s' ->
      run s st (Done s') st
  | run_fail s st :
      expand st s = Failure ->
      run s st Failed st
  | run_cut s st st1 st2 r :
      expand st s = CutBrothers st1 ->
      run s st1 r st2 ->
      run s st r st2 
  | run_step s s' st st1 st2 r :
      expand st s = Expanded st1 s' ->
      run s' st1 r st2 ->
      run s st r st2.

Lemma test s g1 g2 s' st :
  run s (And g1 g2) (Done s') st ->
    exists st1 st2 s'', st = And st1 st2 /\ run s g1 (Done s'') st1 /\ run s'' g2 (Done s') st2.
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
  rewrite expand_And. case L: expand => [|st0||s'] // => [[?]|]; subst.
  move: (IH _ _ erefl _ erefl) => [il [ir [s']]] [-> [ IHl IHr]] {IH}.
  - exists il, ir, s'; split=> //; split.
      by apply: run_cut L IHl.
      by apply: IHr.
  - case R: expand => //= -[?]; subst.
    move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [-> [ IHl IHr]] {IH}.
    exists il, ir, s'''; split=> //; split.
      by apply: IHl.
    move: R.
    elim: st_r => //=.
    - move=> ? [[?]|[|]//]; subst.
      - by apply: run_cut => //=.
      - by move=> ??; case: F => [|[]].
    - move=> s0 ? [s0' p0]; case: expand => //; by case:expand. 
    - move=> s0 + s1 IH1; case: expand => //=.
      - move=> s2 IH [?]; subst.
  admit. admit.
move=> s s' st st1 st2 r + Hr IH g1 g2 ? s'' ?; subst.
rewrite expand_And.
case E:expand => [|||] //.
- move=> [??]; subst.
  move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [-> [ IHl IHr]] {IH}.
  exists il, ir, s'''; split => //; split=>//.
  apply: run_step E IHl.
- case Er:expand => [|||] //= [??]; subst.
  move: (IH _ _ erefl _ erefl) => [il [ir [s''']]] [-> [ IHl IHr]] {IH}.

  exists g1, g2, s.


    exists il, ir, s'''; split => //; split=>//.
    - apply: run_done.

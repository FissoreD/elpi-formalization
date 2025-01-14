From mathcomp Require Import all_ssreflect.

Definition predname := nat.
Inductive pred := true | and of pred & pred | call of predname | cut | fail.
Definition sub := list unit.
Inductive alt := Alt (s : sub) (goal : pred) (ca : list alt).

(* Axiom bodies : predname -> list pred. *)
Definition bodies (p : predname) : list pred :=
  match p with
  | 0 => [:: and true cut ; and fail cut]
  | _ => [:: fail]
  end.

(* Definition tail (l : list alt) := match l with [::] => [::] | [:: _ & l] => l end. *)

Inductive focus := Foc (s : sub) (g : pred) (ca : list alt).

Definition next_alt a (k : focus -> list alt -> option (sub * list alt)) :=
if a is [:: Alt s p ca & a] then k (Foc s p ca) a
else None.

Fixpoint run bodies n (f : focus) a : option (sub * list alt) :=
  match n, f with
  | O, Foc s _ ca => None
  | S n, Foc s p ca =>
        match p with
        | true => Some (s,a)
        | and p1 p2 =>
             if run bodies n (Foc s p1 ca) a is Some (s,a) then
               run bodies n (Foc s p2 ca) a
             else
               next_alt a (run bodies n)
        | call p =>
            match bodies p with
            | [::] => next_alt a (run bodies n)
            | [:: b & bs ] => run bodies n (Foc s b a) ([seq Alt s g a | g <- bs ] ++  a)
            end
        | cut => Some (s,ca)
        | fail =>
            next_alt a (run bodies n)
        end
  end.

Definition func_bodies (p : predname) pl (q : predname) : list pred :=
  if p == q then [seq and x cut | x <- pl] else [:: fail ].


Definition functional n s p :=
  forall s' a ca a' pl, run (func_bodies p pl) n (Foc s (call p) ca) a = Some (s', a') -> a = a'.

Lemma test n s p : functional n s p.
move=> s' a ca a' pl.
elim: n => [//|n IH] /=.
rewrite {1}/func_bodies eqxx.
elim: pl IH => [_|x xs IH] /=.
  case: a => // - [sa ga caa] al /=.
  case: ga.
    case:n => // n /= [].


xxxx

Inductive pred := true | and of pred & pred | call of pred | cut | fail.
Definition sub := list unit.
Inductive alt := Alt (s : sub) (goal : pred) (ca : list alt).

(* Definition tail (l : list alt) := match l with [::] => [::] | [:: _ & l] => l end. *)

Inductive focus := Foc (s : sub) (g : pred) (ca : list alt).

Definition next_alt a (k : focus -> list alt -> option (sub * list alt)) :=
if a is [:: Alt s p ca & a] then k (Foc s p ca) a
else None.

Fixpoint run n (f : focus) a : option (sub * list alt) :=
  match n, f with
  | O, Foc s _ ca => None
  | S n, Foc s p ca =>
        match p with
        | true => Some (s,a)
        | and p1 p2 =>
             if run n (Foc s p1 ca) a is Some (s,a) then
               run n (Foc s p2 ca) a
             else
               next_alt a (run n)
        | call p =>
             run n (Foc s p a) [:: Alt s p ca & a]
        | cut => Some (s,ca)
        | fail =>
            next_alt a (run n)
        end
  end.

Definition functional n s g :=
  forall s' a ca a', run n (Foc s (call g) ca) a = Some (s', a') -> ca = a'.


Definition functional n s g :=
  forall s' a ca a', run n (Foc s g ca) a = Some (s', a') -> ca = a'.

Definition succeeds n s g :=
  forall ca s', exists x, run n (Foc s g ca) ca = Some (s',x ++ ca).

Definition fails n s g :=
  forall ca, run n (Foc s g ca) [::] = None.

Lemma succeeds_monotone n s g :
  succeeds n.+1 s g -> fails n s g \/ exists s', succeeds n s' g.


Lemma test p n s : succeeds n s p -> functional n.+1 s (and p cut).
rewrite /functional /= => + s' a ca a'.
elim: n => // [|n IH sp]. by case: a => [|[]].

xx

rewrite {}Succ_p. elim: n => [|n IH].
  by case: a=>/=[|[] aa].
case: a => /=[|[] aa].

case: n p => /= [//|n p' s s' a ca a'].
case: (run n (Foc s p' ca) a) => [[]|] /=; case: n => //=.
  by move=> ? ? ? [].
  by case: a => /= // -[].
  case: a => [|[] s'' p a1 a2 n] //=.
 by case: n {E} => /= [[]|n []].
Qed.

Lemma test2 p p1 : functional p1 -> functional (and p (and cut p1)).
move=> E; rewrite /functional => n.
case: n p => /= [ p s s' a ca a' [//]|n p' s s' a ca a'].
case E': (run n (Foc s p' ca) a).
case: n {E'} => [[//]|n] /=.
case: n => [[//]|n].
by rewrite {2}[run]lock /= -lock => /E.
Qed.


xxx



Fixpoint run n (f : focus) a : sub * list alt :=
  match n, f with
  | O, Foc s _ ca => (s,ca)
  | S n, Foc s p ca =>
        match p with
        | true => (s,a)
        | and p1 p2 =>
             let: (s,a) := run n (Foc s p1 ca) a in
             run n (Foc s p2 ca) a
        | call p =>
             run n (Foc s p a) [:: Alt s p ca & a]
        | cut => (s,ca)
        | fail =>
            match a with
            | [::] => (s,ca)
            | [:: Alt s p ca & a] => run n (Foc s p ca) a
            end
        end
  end.

Definition functional g :=
  forall n s s' a ca a', run n (Foc s g ca) a = (s', a') -> ca = a'.

Lemma test p : functional (and p cut).
rewrite /functional => n.
case: n p => /= [ p s s' a ca a' [//]|n p' s s' a ca a'].
case E: (run n (Foc s p' ca) a). by case: n {E} => /= [[]|n []].
Qed.

Lemma test2 p p1 : functional p1 -> functional (and p (and cut p1)).
move=> E; rewrite /functional => n.
case: n p => /= [ p s s' a ca a' [//]|n p' s s' a ca a'].
case E': (run n (Foc s p' ca) a).
case: n {E'} => [[//]|n] /=.
case: n => [[//]|n].
by rewrite {2}[run]lock /= -lock => /E.
Qed.


xxx


Inductive pred := call of list pred | cut.
Definition sub := list unit.
Record alt := {s : sub }.

Definition tail (l : list alt) := match l with [::] => [::] | [:: _ & l] => l end.

Fixpoint run n (p : list pred) s a ca : sub * list alt :=
  match n with
  | O => (s,ca)
  | S n =>
        match p with
        | [::] => (s,a)
        | [:: call pl & p] =>
             let: (s,a) := run n pl s [:: {| s := s|} & a] a in
             run n p s a ca
        | [:: cut & p] => run n p s ca ca
        end
  end.

Definition functional g :=
  forall n s s' a ca a', run n g s a ca = (s', a') -> ca = a'.

Lemma test p : functional (rcons p cut).
rewrite /functional => n.
elim: n p => /= [ p s s' a ca a' [//]|n IH p' s s' a ca a'].
case: p' => /=. by case: n {IH} => [|_] /= [].
case => [l l'| ? /IH //].
case E: (run n l s _ _).
by move/IH.
Qed.

Lemma test2 p p1 : functional p1 -> functional (p ++ [:: cut & p1]).
move=> E; rewrite /functional => n.
elim: n p => /= [ p s s' a ca a' [//]|n IH p' s s' a ca a'].
case: p' => /=. by move/E.
case => [l l'| ? /IH //].
case E1: (run n l s _ _).
by move/IH.
Qed.

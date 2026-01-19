From mathcomp Require Import all_ssreflect.
From det Require Import ctx lang tree tree_prop tree_valid_state elpi t2l.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Section Nur.

Variable u : Unif.

Fixpoint of_goals l :=
  match l with
    | [::] => no_goals
    | cutE l :: xs => more_goals (cutE l) (of_goals xs)
    | (callE _ _ as hd) :: xs => more_goals hd (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => -nilCA
  | x :: xs => (empty, of_goals x) ::: (of_alt xs)
  end.

Definition tester l r :=
  t2l l empty nilC = r.

Goal forall B B0 p,
let f x := (TA p (call x)) in
let g x := (p, [::call x]) in
  tester (And (Or OK empty (f B)) (g B0) Bot) 
    ((empty, (callE p B) ::: ((callE p B0) ::: nilC)) ::: nilC).
Proof.
  by move=> //.
Qed.

Goal forall A B D0 D p,
  (* (((! \/ A) \/ B)) /\ (D) *)
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester 
    (And (Or ((Or (TA p cut) empty (f A))) empty (f B)) (g D0) (f D)) 
    (of_alt [:: 
      [::cutE (of_alt [:: [:: callE p B; callE p D0]]); callE p D];
      [:: callE p A; callE p D0]; 
      [:: callE p B; callE p D0]]).
Proof.
  move=> A B D0 D p/=.
  move=>//=.
Qed.


Goal forall B C D E F p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} F) *)
  tester 
    (And (Or OK empty (f B)) (g C) (And (Or (TA p cut) empty (f D)) (g E) (f F)))
    (of_alt [:: 
      [:: cutE (of_alt [:: [:: callE p B; callE p C]]); callE p F];
      [:: callE p D; callE p E]; 
      [:: callE p B; callE p C]]).
Proof.
  move=> B C D E F p/=.
  rewrite //.
Qed.

(* THIS CAN NO MORE EXISTS: reset is never Bot *)
(* Goal forall A B C p,
  let f x := (TA p (call x)) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (TA p cut) empty (f A))) empty (f B)) Bot (Or (TA p cut) empty (f C))) 
    (of_alt [:: 
      [::cut nilC ; cut nilC ];
      [::cut nilC ; call p C]]).
Proof.
  move=> A B C p/=.
  rewrite/t2l//.
Qed. *)

Goal forall A B C0 C p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (TA p cut) empty (f A))) empty (f B)) (g C0) (Or (TA p cut) empty (f C)))
    (of_alt[:: 
      [::cutE (of_alt [:: [:: callE p B; callE p C0]]); cutE (of_alt [::[:: callE p A; callE p C0]; [:: callE p B; callE p C0]])];
      [::cutE (of_alt [:: [:: callE p B; callE p C0]]); callE p C];
      [:: callE p A; callE p C0]; 
      [:: callE p B; callE p C0]]).
Proof.
  move=> A B C0 C p/=.
  rewrite/t2l/=.
  move=>//.
Qed.



Goal forall A B0 p,
    (* (OK \/ A) /\_B0 OK *)
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (And (Or OK empty (f A)) (g B0) OK) (of_alt [::[::]; [::callE p A; callE p B0]]).
Proof.
  move=> A B0 p.
  rewrite/t2l//=.
Qed.

Goal forall A B0 p,
  (* (Bot \/ B) /\_b0 B0  *)
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (And (Or Bot empty (f A)) (g B0) (f B0))
  (of_alt [::[::callE p A; callE p B0]]).
Proof.
  move=> A B0 p.
  rewrite/t2l//=.
Qed.

Goal forall p x y z w a, 
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (
    And 
      (Or (f x) empty (f y)) (g a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: callE p x; callE p z];
    [:: callE p x; callE p w];
    [:: callE p y; callE p a]]).
Proof.
  move=>/=.
  by [].
Qed.

Goal forall p z w a, 
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (
    And 
      (Or OK empty Bot) (g a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: callE p z]; [:: callE p w]]).
Proof.
  move=>p z w a.
  rewrite/t2l/=.
  by [].
Qed.

(* THIS IS IMPORTANT *)
Goal forall p a b c d, 
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (
    And 
      (Or Bot empty (f a)) (g b) 
      (Or (f c) empty (f d))) 
    (* [:: [:: callE a; call b] ]. *)
    (of_alt [:: [:: callE p a; callE p c]; [::callE p a; callE p d] ]).
Proof.
  move=> p a b c d /=.
  by [].
Qed.

Goal forall p a b, 
(* (! \/ a) \/ b *)
  tester (
    Or 
      (Or (TA p cut) empty (TA p (call a))) empty
      (TA p (call b)))
  (of_alt [:: [:: cutE (of_alt[:: [:: callE p b]])]; [:: callE p a]; [:: callE p b]]).
Proof.
  move=>p a b; rewrite/t2l/=.
  by []. Qed.

(* Goal forall A1 A2 s  C0 B p,
  let f x := (TA p (call x)) in
  tester (And (Or (f A1) s (f A2)) (Bot) (And Bot (f C0) (f B))) nilC
  .
Proof.
  move=> A1 A2 s  C0 B p.
  rewrite/t2l.
  by [].
Qed. *)

(* Goal forall A B C p,
  let f x := (TA p (call x)) in
  tester (And (Or (f A) empty (f B)) (Bot) (f C))
  (of_alt[:: [:: callE p A; call p C]]).
Proof.
  move=> s A B C p.
  rewrite/t2l/=.
  by [].
Qed. *)

Goal forall A1 A2 B0 C0 B p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  tester (And (Or (f A1) empty (f A2)) (g B0) (And Bot (g C0) (f B)))
  (of_alt [:: [:: callE p A2 ; callE p B0 ]]).
Proof.
  move=> * /=.
  by [].
Qed.

Goal forall b0 p a b c, 
  let g x := (p, [::call x]) in
  tester (
    Or 
      (Or (And (TA p (call c)) (g b0) (TA p cut)) empty (TA p (call a))) empty
      (TA p (call b)))
  (of_alt[:: [:: callE p c; cutE (of_alt[:: [:: callE p b]])]; [:: callE p a]; [:: callE p b]]).
Proof.
  move=> b0 p a b c.
  rewrite/t2l/=.
  rewrite//=.
Qed.

Goal forall B C Res p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (g Res) (Or (TA p cut) empty (f C))) 
    (of_alt[::[::cutE (of_alt[::[:: callE p B; callE p Res]])]; [::callE p C]; [:: callE p B; callE p Res]]).
Proof.
  move=> B C Res p.
  rewrite /t2l/=.
  move=>//.
Qed.

Goal forall B C Res Reempty p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (OK \/ B) /\ (! /\ C) -> [cut_[]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (g Res) (And (TA p cut) (g Reempty) (f C))) 
    (of_alt[::[::cutE nilC; callE p C]; [:: callE p B; callE p Res]]).
Proof.
  move=> B C Res Reempty p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall A B C C0 p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (A /\ ((! \/ B) \/ C) *)
  tester (And (f A) (g C0) (Or (Or (TA p cut) empty (f B)) empty (f C))) 
  (of_alt [:: 
    [:: callE p A; cutE (of_alt[:: [:: callE p C]])]; 
    [:: callE p A; callE p B]; 
    [:: callE p A; callE p C]]).
Proof.
  move=> A B C C0 p.
  rewrite /t2l/=.
  repeat f_equal => //.
Qed.

Goal forall A B C D E p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) \/_{empty} E) *)
  tester 
    (And (Or (f A) empty (f B)) (g C) (Or (Or (TA p cut) empty (f D)) empty (f E))) 
    (of_alt[:: 
    [:: callE p A; cutE (of_alt [:: [:: callE p E]; [:: callE p B; callE p C]])];
    [:: callE p A; callE p D]; [:: callE p A; callE p E];
    [:: callE p B; callE p C]])
  .
Proof.
  move=> empty A B C D E p/=.
  rewrite/t2l/=.
  move=>//.
Qed.

(* IMPORTANTE!
  The right and side of the first and becomes:
    (!,!); (D, E)
  The two cuts points to different cat_to alternatives:
  The first rejects (D,E) as choice points
  The second rejects (B,C) which is an alternatives at higher level
*)
Goal forall B C D E p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (OK \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} !) *)
  tester 
    (And (Or OK empty (f B)) (g C) (And (Or (TA p cut) empty (f D)) (g E) (TA p cut))) 
    (of_alt [:: 
      [:: cutE (of_alt[:: [:: callE p B; callE p C]]); cutE nilC ];
      [:: callE p D; callE p E]; 
      [:: callE p B; callE p C]]).
Proof.
  move=> B C D E p/=.
  rewrite/t2l/=.
  move=>//.
Qed.

Goal forall A B C p,
  let f x := (TA p (call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester
    (Or (Or (Or (TA p cut) empty ((Or (TA p cut) empty (f A)))) empty (f B)) empty (f C))
    (of_alt[:: 
      [::cutE (of_alt[:: [:: callE p B]; [::callE p C]])];
      [::cutE (of_alt[:: [:: callE p B]; [::callE p C]])];
      [:: callE p A]; 
      [:: callE p B];
      [:: callE p C] ]).
Proof.
  move=> A B C p/=.
  rewrite/t2l/=.
  move=>//=.
Qed.

Goal forall A B C p,
  let f x := (TA p (call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester 
    (Or (Or (Or (And (TA p cut) (p, [::]) OK) empty ((Or (TA p cut) empty (f A)))) empty (f B)) empty (f C)) 
    (of_alt[:: 
      [::cutE (of_alt[:: [:: callE p B]; [::callE p C]])];
      [::cutE (of_alt[:: [:: callE p B]; [::callE p C]])];
      [:: callE p A]; 
      [:: callE p B];
      [:: callE p C] ]).
Proof.
  move=> A B C p/=.
  rewrite/t2l/=.
  move=>//=.
Qed.


Goal forall A B C D0 D p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (((! \/ ! \/ A) \/ B) \/ C) /\ D*)
  tester
    (And (Or (Or (Or (TA p cut) empty ((Or (TA p cut) empty (f A)))) empty (f B)) empty (f C)) (g D0) (f D))
    (of_alt[:: 
      [::cutE (of_alt [:: [:: callE p B; callE p D0]; [::callE p C; callE p D0]]); callE p D];
      [::cutE (of_alt [:: [:: callE p B; callE p D0]; [::callE p C; callE p D0]]); callE p D0];
      [:: callE p A; callE p D0]; 
      [:: callE p B; callE p D0];
      [:: callE p C; callE p D0] ]).
Proof.
  move=> A B C D0 D p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall X A B C D0 D p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* ((X \/ ((! \/ ! \/ A) \/ B) \/ C)) /\ D*)
  tester 
    (And (Or (f X) empty (Or (Or (Or (TA p cut) empty ((Or (TA p cut) empty (f A)))) empty (f B)) empty (f C))) (g D0) (f D))
    (of_alt[:: 
      [:: callE p X; callE p D];
      [::cutE (of_alt[:: [:: callE p B; callE p D0]; [::callE p C; callE p D0]]); callE p D0];
      [::cutE (of_alt[:: [:: callE p B; callE p D0]; [::callE p C; callE p D0]]); callE p D0];
      [:: callE p A; callE p D0]; 
      [:: callE p B; callE p D0];
      [:: callE p C; callE p D0] ]).
Proof.
  move=> X A B C D0 D p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall B0 A B C D p,
  let f x := (TA p (call x)) in
  let g x := (p, [::call x]) in
  (* (((A /\ (! \/ B)) \/ C \/ D)) *)
  tester 
    (Or (Or (f C) empty (And (f A) (g B0) (Or (TA p cut) empty (f B)))) empty (f D))
    (of_alt[:: 
      [:: callE p C]; 
      [:: callE p A; cutE (of_alt[:: [:: callE p D]])]; 
      [:: callE p A; callE p B]; [:: callE p D]]).
Proof.
  move=> B0 A B C D p/=.
  rewrite/t2l/=.
  rewrite//.
Qed.

Goal forall p A B C,
  let f x := (TA p (call x)) in
  (* (((! \/ A) \/ !) \/ B) \/ C *)
  tester 
    (Or (Or (Or (Or (TA p cut) empty (f A)) empty (TA p cut)) empty (f B)) empty (f C))
    (of_alt[:: 
      [::cutE (of_alt[::[::cutE (of_alt[::[::callE p B]; [::callE p C]])]; [::callE p B]; [::callE p C]])];
      [::callE p A];
      [::cutE (of_alt[::[::callE p B]; [::callE p C]])];
      [::callE p B];
      [::callE p C]
    ]).
Proof.
  move=> p A B C/=.
  rewrite/t2l/=.
  rewrite//.
Qed.
Goal forall l p,
  let s := ((Or (Or Dead empty (TA p cut)) empty OK)) in
  let bt := of_alt([::] :: l) in
  t2l s empty (of_alt l) = of_alt[:: [:: cutE bt]; [::]] /\ 
    t2l (odflt Bot (next_alt true (step u empty s).2)) empty (of_alt l) ++ (of_alt l) = bt.
Proof.
  move=>//=.
Qed.

End Nur.
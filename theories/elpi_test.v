From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Section Nur.

Variable u : Unif.

Fixpoint of_goals l :=
  match l with
    | [::] => no_goals
    | cut l :: xs => more_goals (cut l) (of_goals xs)
    | (call _ _ as hd) :: xs => more_goals hd (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => -nilCA
  | x :: xs => (empty, of_goals x) ::: (of_alt xs)
  end.

Definition tester l r :=
  state_to_list l empty nilC = r.

Goal forall B B0 p,
let f x := (CallS p x) in
  tester (And (Or OK empty (f B)) (f B0) Bot) 
    ((empty, (call p B) ::: ((call p B0) ::: nilC)) ::: nilC).
Proof.
  by move=> //.
Qed.

Goal forall A B D0 D p,
  (* (((! \/ A) \/ B)) /\ (D) *)
  let f x := (CallS p x) in
  tester 
    (And (Or ((Or (CutS) empty (f A))) empty (f B)) (f D0) (f D)) 
    (of_alt [:: 
      [::cut (of_alt [:: [:: call p B; call p D0]]); call p D];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0]]).
Proof.
  move=> A B D0 D p/=.
  move=>//=.
Qed.


Goal forall B C D E F p,
  let f x := (CallS p x) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} F) *)
  tester 
    (And (Or OK empty (f B)) (f C) (And (Or (CutS) empty (f D)) (f E) (f F)))
    (of_alt [:: 
      [:: cut (of_alt [:: [:: call p B; call p C]]); call p F];
      [:: call p D; call p E]; 
      [:: call p B; call p C]]).
Proof.
  move=> B C D E F p/=.
  rewrite //.
Qed.


Goal forall A B C p,
  let f x := (CallS p x) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (CutS) empty (f A))) empty (f B)) Bot (Or (CutS) empty (f C))) 
    (of_alt [:: 
      [::cut nilC ; cut nilC ];
      [::cut nilC ; call p C]]).
Proof.
  move=> A B C p/=.
  rewrite/state_to_list//.
Qed.

Goal forall A B C0 C p,
  let f x := (CallS p x) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (CutS) empty (f A))) empty (f B)) (f C0) (Or (CutS) empty (f C)))
    (of_alt[:: 
      [::cut (of_alt [:: [:: call p B; call p C0]]); cut (of_alt [::[:: call p A; call p C0]; [:: call p B; call p C0]])];
      [::cut (of_alt [:: [:: call p B; call p C0]]); call p C];
      [:: call p A; call p C0]; 
      [:: call p B; call p C0]]).
Proof.
  move=> A B C0 C p/=.
  rewrite/state_to_list/=.
  move=>//.
Qed.



Goal forall A B0 p,
    (* (OK \/ A) /\_B0 OK *)
  let f x := (CallS p x) in
  tester (And (Or OK empty (f A)) (f B0) OK) (of_alt [::[::]; [::call p A; call p B0]]).
Proof.
  move=> A B0 p.
  rewrite/state_to_list//=.
Qed.

Goal forall A B0 p,
  (* (Bot \/ B) /\_b0 B0  *)
  let f x := (CallS p x) in
  tester (And (Or Bot empty (f A)) (f B0) (f B0))
  (of_alt [::[::call p A; call p B0]]).
Proof.
  move=> A B0 p.
  rewrite/state_to_list//=.
Qed.

Goal forall p x y z w a, 
  let f x := (CallS p x) in
  tester (
    And 
      (Or (f x) empty (f y)) (f a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: call p x; call p z];
    [:: call p x; call p w];
    [:: call p y; call p a]]).
Proof.
  move=>/=.
  by [].
Qed.

Goal forall p z w a, 
  let f x := (CallS p x) in
  tester (
    And 
      (Or Top empty Bot) (f a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: call p z]; [:: call p w]]).
Proof.
  move=>p z w a.
  rewrite/state_to_list/=.
  by [].
Qed.

(* THIS IS IMPORTANT *)
Goal forall p a b c d, 
  let f x := (CallS p x) in
  tester (
    And 
      (Or Bot empty (f a)) (f b) 
      (Or (f c) empty (f d))) 
    (* [:: [:: call a; call b] ]. *)
    (of_alt [:: [:: call p a; call p c]; [::call p a; call p d] ]).
Proof.
  move=> p a b c d /=.
  by [].
Qed.

Goal forall p a b, 
(* (! \/ a) \/ b *)
  tester (
    Or 
      (Or (CutS) empty (CallS p a)) empty
      (CallS p b))
  (of_alt [:: [:: cut (of_alt[:: [:: call p b]])]; [:: call p a]; [:: call p b]]).
Proof.
  move=>p a b; rewrite/state_to_list/=.
  by []. Qed.

Goal forall A1 A2 s  C0 B p,
  let f x := (CallS p x) in
  tester (And (Or (f A1) s (f A2)) (Bot) (And Bot (f C0) (f B))) nilC
  .
Proof.
  move=> A1 A2 s  C0 B p.
  rewrite/state_to_list.
  by [].
Qed.

Goal forall A B C p,
  let f x := (CallS p x) in
  tester (And (Or (f A) empty (f B)) (Bot) (f C))
  (of_alt[:: [:: call p A; call p C]]).
Proof.
  move=> s A B C p.
  rewrite/state_to_list/=.
  by [].
Qed.

Goal forall A1 A2 B0 C0 B p,
  let f x := (CallS p x) in
  tester (And (Or (f A1) empty (f A2)) (f B0) (And Bot (f C0) (f B)))
  (of_alt [:: [:: call p A2 ; call p B0 ]]).
Proof.
  move=> * /=.
  by [].
Qed.

Goal forall b0 p a b c, 
  tester (
    Or 
      (Or (And (CallS p c) (CallS p b0) (CutS)) empty (CallS p a)) empty
      (CallS p b))
  (of_alt[:: [:: call p c; cut (of_alt[:: [:: call p b]])]; [:: call p a]; [:: call p b]]).
Proof.
  move=> b0 p a b c.
  rewrite/state_to_list/=.
  rewrite//=.
Qed.

Goal forall B C Res p,
  let f x := (CallS p x) in
  (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (f Res) (Or (CutS) empty (f C))) 
    (of_alt[::[::cut (of_alt[::[:: call p B; call p Res]])]; [::call p C]; [:: call p B; call p Res]]).
Proof.
  move=> B C Res p.
  rewrite /state_to_list/=.
  move=>//.
Qed.

Goal forall B C Res Reempty p,
  let f x := (CallS p x) in
  (* (OK \/ B) /\ (! /\ C) -> [cut_[]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (f Res) (And (CutS) (f Reempty) (f C))) 
    (of_alt[::[::cut nilC; call p C]; [:: call p B; call p Res]]).
Proof.
  move=> B C Res Reempty p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.

Goal forall A B C C0 p,
  let f x := (CallS p x) in
  (* (A /\ ((! \/ B) \/ C) *)
  tester (And (f A) (f C0) (Or (Or (CutS) empty (f B)) empty (f C))) 
  (of_alt [:: 
    [:: call p A; cut (of_alt[:: [:: call p C]])]; 
    [:: call p A; call p B]; 
    [:: call p A; call p C]]).
Proof.
  move=> A B C C0 p.
  rewrite /state_to_list/=.
  repeat f_equal => //.
Qed.

Goal forall A B C D E p,
  let f x := (CallS p x) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) \/_{empty} E) *)
  tester 
    (And (Or (f A) empty (f B)) (f C) (Or (Or (CutS) empty (f D)) empty (f E))) 
    (of_alt[:: 
    [:: call p A; cut (of_alt [:: [:: call p E]; [:: call p B; call p C]])];
    [:: call p A; call p D]; [:: call p A; call p E];
    [:: call p B; call p C]])
  .
Proof.
  move=> empty A B C D E p/=.
  rewrite/state_to_list/=.
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
  let f x := (CallS p x) in
  (* (OK \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} !) *)
  tester 
    (And (Or OK empty (f B)) (f C) (And (Or (CutS) empty (f D)) (f E) (CutS))) 
    (of_alt [:: 
      [:: cut (of_alt[:: [:: call p B; call p C]]); cut nilC ];
      [:: call p D; call p E]; 
      [:: call p B; call p C]]).
Proof.
  move=> B C D E p/=.
  rewrite/state_to_list/=.
  move=>//.
Qed.

Goal forall A B C p,
  let f x := (CallS p x) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester
    (Or (Or (Or (CutS) empty ((Or (CutS) empty (f A)))) empty (f B)) empty (f C))
    (of_alt[:: 
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [:: call p A]; 
      [:: call p B];
      [:: call p C] ]).
Proof.
  move=> A B C p/=.
  rewrite/state_to_list/=.
  move=>//=.
Qed.

Goal forall A B C p,
  let f x := (CallS p x) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester 
    (Or (Or (Or (And (CutS) Top Top) empty ((Or (CutS) empty (f A)))) empty (f B)) empty (f C)) 
    (of_alt[:: 
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [:: call p A]; 
      [:: call p B];
      [:: call p C] ]).
Proof.
  move=> A B C p/=.
  rewrite/state_to_list/=.
  move=>//=.
Qed.


Goal forall A B C D0 D p,
  let f x := (CallS p x) in
  (* (((! \/ ! \/ A) \/ B) \/ C) /\ D*)
  tester
    (And (Or (Or (Or (CutS) empty ((Or (CutS) empty (f A)))) empty (f B)) empty (f C)) (f D0) (f D))
    (of_alt[:: 
      [::cut (of_alt [:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D];
      [::cut (of_alt [:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0];
      [:: call p C; call p D0] ]).
Proof.
  move=> A B C D0 D p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.

Goal forall X A B C D0 D p,
  let f x := (CallS p x) in
  (* ((X \/ ((! \/ ! \/ A) \/ B) \/ C)) /\ D*)
  tester 
    (And (Or (f X) empty (Or (Or (Or (CutS) empty ((Or (CutS) empty (f A)))) empty (f B)) empty (f C))) (f D0) (f D))
    (of_alt[:: 
      [:: call p X; call p D];
      [::cut (of_alt[:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [::cut (of_alt[:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0];
      [:: call p C; call p D0] ]).
Proof.
  move=> X A B C D0 D p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.

Goal forall B0 A B C D p,
  let f x := (CallS p x) in
  (* (((A /\ (! \/ B)) \/ C \/ D)) *)
  tester 
    (Or (Or (f C) empty (And (f A) (f B0) (Or (CutS) empty (f B)))) empty (f D))
    (of_alt[:: 
      [:: call p C]; 
      [:: call p A; cut (of_alt[:: [:: call p D]])]; 
      [:: call p A; call p B]; [:: call p D]]).
Proof.
  move=> B0 A B C D p/=.
  rewrite/state_to_list/=.
  rewrite//.
Qed.

Goal forall p A B C,
  let f x := (CallS p x) in
  (* (((! \/ A) \/ !) \/ B) \/ C *)
  tester 
    (Or (Or (Or (Or (CutS) empty (f A)) empty (CutS)) empty (f B)) empty (f C))
    (of_alt[:: 
      [::cut (of_alt[::[::cut (of_alt[::[::call p B]; [::call p C]])]; [::call p B]; [::call p C]])];
      [::call p A];
      [::cut (of_alt[::[::call p B]; [::call p C]])];
      [::call p B];
      [::call p C]
    ]).
Proof.
  move=> p A B C/=.
  rewrite/state_to_list/=.
  rewrite//.
Qed.
Goal forall l,
  let s := ((Or (Or Dead empty (CutS)) empty Top)) in
  let bt := of_alt([::] :: l) in
  state_to_list s empty (of_alt l) = of_alt[:: [:: cut bt]; [::]] /\ 
    state_to_list (odflt Bot (next_alt true (get_state (expand u empty s)))) empty (of_alt l) ++ (of_alt l) = bt.
Proof.
  simpl get_state.
  move=>//=.
Qed.

End Nur.
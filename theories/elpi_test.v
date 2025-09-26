From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Import Language.

Module UAxioms <: Unif.
  Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
  Axiom matching : Tm -> Tm -> Sigma -> option Sigma.
End UAxioms.

Module Nur:= Nur(UAxioms).
Import Nur VS.RunP.Run.

Fixpoint of_goals l :=
  match l with
    | [::] => no_goals
    | cut l :: xs => more_goals (cut l) (of_goals xs)
    | (call _ _ as hd) :: xs => more_goals hd (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => no_alt
  | x :: xs => more_alt (of_goals x) (of_alt xs)
  end.

Goal forall B B0 p,
let f x := (Goal p (Call x)) in
  state_to_list (And (Or OK empty (f B)) (f B0) Bot) no_alt = 
    (more_alt (more_goals (call p B) (more_goals (call p B0) no_goals)) no_alt).
Proof.
  by move=> //.
Qed.

Goal forall s1 A B D0 D p,
  let f x := (Goal p (Call x)) in
  state_to_list 
    (And (Or ((Or (Goal p Cut) s1 (f A))) s1 (f B)) (f D0) (f D)) no_alt = 
    of_alt [:: 
      [::cut (of_alt [:: [:: call p B; call p D0]]); call p D];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0]].
Proof.
  move=> s1 A B D0 D p/=.
  move=>//.
Qed.


Goal forall s1 s2 B C D E F p,
  let f x := (Goal p (Call x)) in
  (* (A \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} F) *)
  state_to_list 
    (And (Or OK s1 (f B)) (f C) (And (Or (Goal p Cut) s2 (f D)) (f E) (f F))) no_alt = 
    of_alt [:: 
      [:: cut (of_alt [:: [:: call p B; call p C]]); call p F];
      [:: call p D; call p E]; 
      [:: call p B; call p C]].
Proof.
  move=> s1 s2 B C D E F p/=.
  rewrite //.
Qed.


Goal forall s1 s2 A B C p,
  let f x := (Goal p (Call x)) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  state_to_list 
    (And (Or ((Or (Goal p Cut) s1 (f A))) s1 (f B)) Bot (Or (Goal p Cut) s2 (f C))) no_alt = 
    of_alt [:: 
      [::cut no_alt; cut no_alt];
      [::cut no_alt; call p C]].
Proof.
  move=> s1 s2 A B C p/=.
  rewrite/state_to_list//.
Qed.

Goal forall s1 s2 A B C0 C p,
  let f x := (Goal p (Call x)) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  state_to_list 
    (And (Or ((Or (Goal p Cut) s1 (f A))) s1 (f B)) (f C0) (Or (Goal p Cut) s2 (f C))) no_alt = 
    of_alt[:: 
      [::cut (of_alt [:: [:: call p B; call p C0]]); cut (of_alt [::[:: call p A; call p C0]; [:: call p B; call p C0]])];
      [::cut (of_alt [:: [:: call p B; call p C0]]); call p C];
      [:: call p A; call p C0]; 
      [:: call p B; call p C0]].
Proof.
  move=> s1 s2 A B C0 C p/=.
  rewrite/state_to_list/=.
  move=>//.
Qed.



Goal forall A B0 p s1,
    (* (OK \/ A) /\_B0 OK *)
  let f x := (Goal p (Call x)) in
  state_to_list (And (Or OK s1 (f A)) (f B0) OK) no_alt =
  of_alt [::[::]; [::call p A; call p B0]].
Proof.
  move=> A B0 p s1.
  rewrite/state_to_list//=.
Qed.

Goal forall A B0 p s1,
  (* (Bot \/ B) /\_b0 B0  *)
  let f x := (Goal p (Call x)) in
  state_to_list (And (Or Bot s1 (f A)) (f B0) (f B0)) no_alt =
  of_alt [::[::call p A; call p B0]].
Proof.
  move=> A B0 p s1.
  rewrite/state_to_list//=.
Qed.

Goal forall p x y z w s1 s2 a, 
  let f x := (Goal p (Call x)) in
  state_to_list (
    And 
      (Or (f x) s1 (f y)) (f a) 
      (Or (f z) s2 (f w))) no_alt = 
    of_alt [:: [:: call p x; call p z];
    [:: call p x; call p w];
    [:: call p y; call p a]].
Proof.
  move=>/=.
  by [].
Qed.

Goal forall p z w s1 s2 a, 
  let f x := (Goal p (Call x)) in
  state_to_list (
    And 
      (Or Top s1 Bot) (f a) 
      (Or (f z) s2 (f w))) no_alt = 
    of_alt [:: [:: call p z]; [:: call p w]].
Proof.
  move=>p z w s1 s2 a.
  rewrite/state_to_list/=.
  by [].
Qed.

(* THIS IS IMPORTANT *)
Goal forall p s1 s2 a b c d, 
  let f x := (Goal p (Call x)) in
  state_to_list (
    And 
      (Or Bot s1 (f a)) (f b) 
      (Or (f c) s2 (f d))) no_alt = 
    (* [:: [:: call a; call b] ]. *)
    of_alt [:: [:: call p a; call p c]; [::call p a; call p d] ].
Proof.
  move=> p s1 s2 a b c d /=.
  by [].
Qed.

Goal forall p a b s1 s2, 
(* (! \/ a) \/ b *)
  state_to_list (
    Or 
      (Or (Goal p Cut) s1 (Goal p (Call a))) s2
      (Goal p (Call b))) no_alt = 
  of_alt [:: [:: cut (of_alt[:: [:: call p b]])]; [:: call p a]; [:: call p b]].
Proof.
  move=>p a b s1 s2; rewrite/state_to_list/=.
  by []. Qed.

Goal forall A1 A2 s  C0 B p,
  let f x := (Goal p (Call x)) in
  state_to_list (And (Or (f A1) s (f A2)) (Bot) (And Bot (f C0) (f B))) no_alt =
  no_alt.
Proof.
  move=> A1 A2 s  C0 B p.
  rewrite/state_to_list.
  by [].
Qed.

Goal forall s A B C p,
  let f x := (Goal p (Call x)) in
  state_to_list (And (Or (f A) s (f B)) (Bot) (f C)) no_alt =
  of_alt[:: [:: call p A; call p C]].
Proof.
  move=> s A B C p.
  rewrite/state_to_list/=.
  by [].
Qed.

Goal forall A1 A2 s B0 C0 B p,
  let f x := (Goal p (Call x)) in
  state_to_list (And (Or (f A1) s (f A2)) (f B0) (And Bot (f C0) (f B))) no_alt =
  of_alt [:: [:: call p A2 ; call p B0 ]].
Proof.
  move=> * /=.
  by [].
Qed.

Goal forall b0 p a b c s1 s2, 
  state_to_list (
    Or 
      (Or (And (Goal p (Call c)) (Goal p (Call b0)) (Goal p Cut)) s1 (Goal p (Call a))) s2
      (Goal p (Call b))) no_alt = 
  of_alt[:: [:: call p c; cut (of_alt[:: [:: call p b]])]; [:: call p a]; [:: call p b]].
Proof.
  move=> b0 p a b c s1 s2.
  rewrite/state_to_list/=.
  rewrite//=.
Qed.

Goal forall s1 s2 B C Res p,
  let f x := (Goal p (Call x)) in
  (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
  state_to_list (And (Or OK s1 (f B)) (f Res) (Or (Goal p Cut) s2 (f C))) no_alt
    = of_alt[::[::cut (of_alt[::[:: call p B; call p Res]])]; [::call p C]; [:: call p B; call p Res]].
Proof.
  move=> s1 s2 B C Res p.
  rewrite /state_to_list/=.
  move=>//.
Qed.

Goal forall s1 B C Res Res2 p,
  let f x := (Goal p (Call x)) in
  (* (OK \/ B) /\ (! /\ C) -> [cut_[]; C; (B, Reset)] *)
  state_to_list (And (Or OK s1 (f B)) (f Res) (And (Goal p Cut) (f Res2) (f C))) no_alt
    = of_alt[::[::cut no_alt; call p C]; [:: call p B; call p Res]].
Proof.
  move=> s1 B C Res Res2 p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.

Goal forall s1 s2 A B C C0 p,
  let f x := (Goal p (Call x)) in
  (* (A /\ ((! \/ B) \/ C) *)
  state_to_list (And (f A) (f C0) (Or (Or (Goal p Cut) s1 (f B)) s2 (f C))) no_alt
  = of_alt [:: 
    [:: call p A; cut (of_alt[:: [:: call p C]])]; 
    [:: call p A; call p B]; 
    [:: call p A; call p C]].
Proof.
  move=> s1 s2 A B C C0 p.
  rewrite /state_to_list/=.
  repeat f_equal => //.
Qed.

Goal forall s1 s2 s3 A B C D E p,
  let f x := (Goal p (Call x)) in
  (* (A \/_{s1} B) /\_C ((! \/_{s2} D) \/_{s3} E) *)
  state_to_list 
    (And (Or (f A) s1 (f B)) (f C) (Or (Or (Goal p Cut) s2 (f D)) s3 (f E))) no_alt = 
    of_alt[:: 
    [:: call p A; cut (of_alt [:: [:: call p E]; [:: call p B; call p C]])];
    [:: call p A; call p D]; [:: call p A; call p E];
    [:: call p B; call p C]]
  .
Proof.
  move=> s1 s2 s3 A B C D E p/=.
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
Goal forall s1 s2 B C D E p,
  let f x := (Goal p (Call x)) in
  (* (OK \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} !) *)
  state_to_list 
    (And (Or OK s1 (f B)) (f C) (And (Or (Goal p Cut) s2 (f D)) (f E) (Goal p Cut))) no_alt = 
    of_alt [:: 
      [:: cut (of_alt[:: [:: call p B; call p C]]); cut no_alt];
      [:: call p D; call p E]; 
      [:: call p B; call p C]].
Proof.
  move=> s1 s2 B C D E p/=.
  rewrite/state_to_list/=.
  move=>//.
Qed.

Goal forall s1 s2 A B C p,
  let f x := (Goal p (Call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  state_to_list 
    (Or (Or (Or (Goal p Cut) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C)) no_alt = 
    of_alt[:: 
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [:: call p A]; 
      [:: call p B];
      [:: call p C] ].
Proof.
  move=> s1 s2 A B C p/=.
  rewrite/state_to_list/=.
  move=>//=.
Qed.

Goal forall s1 s2 A B C p,
  let f x := (Goal p (Call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  state_to_list 
    (Or (Or (Or (And (Goal p Cut) Top Top) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C)) no_alt = 
    of_alt[:: 
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [::cut (of_alt[:: [:: call p B]; [::call p C]])];
      [:: call p A]; 
      [:: call p B];
      [:: call p C] ].
Proof.
  move=> s1 s2 A B C p/=.
  rewrite/state_to_list/=.
  move=>//=.
Qed.


Goal forall s1 s2 A B C D0 D p,
  let f x := (Goal p (Call x)) in
  (* (((! \/ ! \/ A) \/ B) \/ C) /\ D*)
  state_to_list 
    (And (Or (Or (Or (Goal p Cut) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C)) (f D0) (f D)) no_alt = 
    of_alt[:: 
      [::cut (of_alt [:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D];
      [::cut (of_alt [:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0];
      [:: call p C; call p D0] ].
Proof.
  move=> s1 s2 A B C D0 D p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.

Goal forall X s1 s2 A B C D0 D p,
  let f x := (Goal p (Call x)) in
  (* ((X \/ ((! \/ ! \/ A) \/ B) \/ C)) /\ D*)
  state_to_list 
    (And (Or (f X) s1 (Or (Or (Or (Goal p Cut) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C))) (f D0) (f D)) no_alt = 
    of_alt[:: 
      [:: call p X; call p D];
      [::cut (of_alt[:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [::cut (of_alt[:: [:: call p B; call p D0]; [::call p C; call p D0]]); call p D0];
      [:: call p A; call p D0]; 
      [:: call p B; call p D0];
      [:: call p C; call p D0] ].
Proof.
  move=> X s1 s2 A B C D0 D p/=.
  rewrite/state_to_list/=.
  f_equal => //.
Qed.


Goal forall s1 s2 B0 A B C D p,
  let f x := (Goal p (Call x)) in
  (* (((A /\ (! \/ B)) \/ C \/ D)) *)
  state_to_list 
    (Or (Or (f C) s2 (And (f A) (f B0) (Or (Goal p Cut) s1 (f B)))) s1 (f D)) no_alt = 
    of_alt[:: 
      [:: call p C]; 
      [:: call p A; cut (of_alt[:: [:: call p D]])]; 
      [:: call p A; call p B]; [:: call p D]].
Proof.
  move=> s1 s2 B0 A B C D p/=.
  rewrite/state_to_list/=.
  rewrite//.
Qed.

Goal forall s1 s2 s3 s4 p A B C,
  let f x := (Goal p (Call x)) in
  (* (((! \/ A) \/ !) \/ B) \/ C *)
  state_to_list 
    (Or (Or (Or (Or (Goal p Cut) s1 (f A)) s2 (Goal p Cut)) s3 (f B)) s4 (f C)) no_alt = 
    of_alt[:: 
      [::cut (of_alt[::[::cut (of_alt[::[::call p B]; [::call p C]])]; [::call p B]; [::call p C]])];
      [::call p A];
      [::cut (of_alt[::[::call p B]; [::call p C]])];
      [::call p B];
      [::call p C]
    ].
Proof.
  move=> s1 s2 s3 s4 p A B C/=.
  rewrite/state_to_list/=.
  rewrite//.
Qed.

Goal forall p l,
  let s := ((Or (Or Dead empty (Goal p Cut)) empty Top)) in
  let bt := of_alt([::] :: l) in
  state_to_list s (of_alt l) = of_alt[:: [:: cut bt]; [::]] /\ 
    state_to_list (clean_success (get_state (expand empty s))) (of_alt l) ++ (of_alt l) = bt.
Proof.
  simpl get_state.
  move=>//=.
Qed.
From mathcomp Require Import all_ssreflect.
From det Require Import ctx lang tree tree_prop valid_tree elpi t2l.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Section Nur.

Variable u : Unif.

Fixpoint of_goals l :=
  match l with
    | [::]%SEQ => [::]%G
    | [:: hd & xs]%SEQ => [:: (hd.1, hd.2) & of_goals xs]%G
  end.

Fixpoint of_alt l :=
  match l with
  | [::]%SEQ => [::]%A
  | [:: x & xs]%SEQ => (empty, of_goals x) ::: (of_alt xs)
  end.

Definition clean_ca_G f (g : A * alts) :=
  match g with
  | (call a, ca) => (call a, [::])
  | (cut, ca) => (cut, f ca)
  end.

Fixpoint clean_ca_goals gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (clean_ca_G clean_ca hd) ::: (clean_ca_goals tl)
  end
with clean_ca (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, clean_ca_goals xs) ::: (clean_ca tl)
  end.

Definition tester l r :=
  clean_ca (t2l l empty nilC) = r.

Goal forall B B0,
let f x := (TA (call x)) in
let g x := ([:: (call x) ]%SEQ) in
  tester (And (Or OK empty (f B)) (g B0) KO) 
    ((empty, (call B,[::]) ::: ((call B0,[::]) ::: nilC)) ::: nilC).
Proof.
  by move=> //.
Qed.

Definition callN A := (call A, no_alt).

Goal forall A B D0 D,
  (* (((! \/ A) \/ B)) /\ (D) *)
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  tester 
    (And (Or ((Or (TA cut) empty (f A))) empty (f B)) (g D0) (f D)) 
    (of_alt [:: 
      [:: (cut, of_alt [:: [:: (callN B); (callN D0)]%SEQ]); (callN D)];
      [:: (callN A); (callN D0)]; 
      [:: (callN B); (callN D0)]]%SEQ).
Proof.
  move=> A B D0 D p/=.
  move=>//=.
Qed.


Goal forall B C D E F,
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} F) *)
  tester 
    (And (Or OK empty (f B)) (g C) (And (Or (TA cut) empty (f D)) (g E) (f F)))
    (of_alt [:: 
      [:: (cut, (of_alt [:: [:: callN B; callN C]])); callN F];
      [:: callN D; callN E]; 
      [:: callN B; callN C]])%SEQ.
Proof.
  move=> B C D E F p/=.
  rewrite //.
Qed.

Definition g x := ([::call x]%SEQ).
(* THIS CAN NO MORE EXISTS: reset is never KO *)
(* Goal forall A B C,
  let f x := (TA (call x)) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (TA cut) empty (f A))) empty (f B)) KO (Or (TA cut) empty (f C))) 
    (of_alt [:: 
      [::cut nilC ; cut nilC ];
      [::cut nilC ; call p C]]%SEQ).
Proof.
  move=> A B C p/=.
  rewrite/t2l//.
Qed. *)

Goal forall A B C0 C,
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  (* (((! \/ A) \/ B)) /\ (! \/ C)*)
  tester 
    (And (Or ((Or (TA cut) empty (f A))) empty (f B)) (g C0) (Or (TA cut) empty (f C)))
    (of_alt[:: 
      [::(cut, (of_alt [:: [:: callN B; callN C0]])); (cut, (of_alt [::[:: callN A; callN C0]; [:: callN B; callN C0]]))];
      [::(cut, (of_alt [:: [:: callN B; callN C0]])); callN C];
      [:: callN A; callN C0]; 
      [:: callN B; callN C0]]%SEQ).
Proof.
  move=> A B C0 C p//=.
Qed.



Goal forall A B0,
    (* (OK \/ A) /\_B0 OK *)
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  tester (And (Or OK empty (f A)) (g B0) OK) (of_alt [::[::]; [::callN A; callN B0]]%SEQ).
Proof.
  move=> A B0 p.
  rewrite/t2l//=.
Qed.

Goal forall A B0,
  (* (KO \/ B) /\_b0 B0  *)
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  tester (And (Or KO empty (f A)) (g B0) (f B0))
  (of_alt [::[::callN A; callN B0]]%SEQ).
Proof.
  move=> A B0 p.
  rewrite/t2l//=.
Qed.

Goal forall x y z w a, 
  let f x := (TA (call x)) in
  let g x := ([::call x]%SEQ) in
  tester (
    And 
      (Or (f x) empty (f y)) (g a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: callN x; callN z];
    [:: callN x; callN w];
    [:: callN y; callN a]]%SEQ).
Proof.
  move=>/=.
  by [].
Qed.

Goal forall z w a, 
  let f x := (TA (call x)) in
  tester (
    And 
      (Or OK empty KO) (g a) 
      (Or (f z) empty (f w))) 
    (of_alt [:: [:: callN z]; [:: callN w]]%SEQ).
Proof.
  move=>p z w a.
  rewrite/t2l/=.
  by [].
Qed.

(* THIS IS IMPORTANT *)
Goal forall a b c d, 
  let f x := (TA (call x)) in
  tester (
    And 
      (Or KO empty (f a)) (g b) 
      (Or (f c) empty (f d))) 
    (* [:: [:: callN a; call b] ]. *)
    (of_alt [:: [:: callN a; callN c]; [::callN a; callN d] ]%SEQ).
Proof.
  move=> a b c d /=.
  by [].
Qed.

Goal forall a b, 
(* (! \/ a) \/ b *)
  tester (
    Or 
      (Or (TA cut) empty (TA (call a))) empty
      (TA (call b)))
  (of_alt [:: [:: (cut, (of_alt[:: [:: callN b]]))]; [:: callN a]; [:: callN b]]%SEQ).
Proof.
  move=> a b; rewrite/t2l/=.
  by []. Qed.

(* Goal forall A1 A2 s  C0 B,
  let f x := (TA (call x)) in
  tester (And (Or (f A1) s (f A2)) (KO) (And KO (f C0) (f B))) nilC
  .
Proof.
  move=> A1 A2 s  C0 B p.
  rewrite/t2l.
  by [].
Qed. *)

(* Goal forall A B C,
  let f x := (TA (call x)) in
  tester (And (Or (f A) empty (f B)) (KO) (f C))
  (of_alt[:: [:: callN A; call p C]]%SEQ).
Proof.
  move=> s A B C p.
  rewrite/t2l/=.
  by [].
Qed. *)

Goal forall A1 A2 B0 C0 B,
  let f x := (TA (call x)) in
  tester (And (Or (f A1) empty (f A2)) (g B0) (And KO (g C0) (f B)))
  (of_alt [:: [:: callN A2 ; callN B0 ]]%SEQ).
Proof.
  move=> * /=.
  by [].
Qed.

Goal forall b0 a b c, 
  tester (
    Or 
      (Or (And (TA (call c)) (g b0) (TA cut)) empty (TA (call a))) empty
      (TA (call b)))
  (of_alt[:: [:: callN c; (cut, (of_alt[:: [:: callN b]]))]; [:: callN a]; [:: callN b]]%SEQ).
Proof.
  move=> b0 p a b .
  rewrite/t2l/=.
  rewrite//=.
Qed.

Goal forall B C Res,
  let f x := (TA (call x)) in
  (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (g Res) (Or (TA cut) empty (f C))) 
    (of_alt[::[::(cut, (of_alt[::[:: callN B; callN Res]]))]; [::callN C]; [:: callN B; callN Res]]%SEQ).
Proof.
  move=> B C Res p.
  rewrite /t2l/=.
  move=>//.
Qed.

Goal forall B C Res Reempty,
  let f x := (TA (call x)) in
  (* (OK \/ B) /\ (! /\ C) -> [cut_[]; C; (B, Reset)] *)
  tester (And (Or OK empty (f B)) (g Res) (And (TA cut) (g Reempty) (f C))) 
    (of_alt[::[::(cut, nilC); callN C]; [:: callN B; callN Res]]%SEQ).
Proof.
  move=> B C Res Reempty p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall A B C C0,
  let f x := (TA (call x)) in
  (* (A /\ ((! \/ B) \/ C) *)
  tester (And (f A) (g C0) (Or (Or (TA cut) empty (f B)) empty (f C))) 
  (of_alt [:: 
    [:: callN A; (cut, (of_alt[:: [:: callN C]]))]; 
    [:: callN A; callN B]; 
    [:: callN A; callN C]]%SEQ).
Proof.
  move=> A B C C0 p.
  rewrite /t2l/=.
  repeat f_equal => //.
Qed.

Goal forall A B C D E,
  let f x := (TA (call x)) in
  (* (A \/_{empty} B) /\_C ((! \/_{empty} D) \/_{empty} E) *)
  tester 
    (And (Or (f A) empty (f B)) (g C) (Or (Or (TA cut) empty (f D)) empty (f E))) 
    (of_alt[:: 
    [:: callN A; (cut, (of_alt [:: [:: callN E]; [:: callN B; callN C]]))];
    [:: callN A; callN D]; [:: callN A; callN E];
    [:: callN B; callN C]]%SEQ)
  .
Proof.
  by [].
Qed.

(* IMPORTANTE!
  The right and side of the first and becomes:
    (!,!); (D, E)
  The two cuts points to different cat_to alternatives:
  The first rejects (D,E) as choice points
  The second rejects (B,C) which is an alternatives at higher level
*)
Goal forall B C D E,
  let f x := (TA (call x)) in
  (* (OK \/_{empty} B) /\_C ((! \/_{empty} D) /\_{E} !) *)
  tester 
    (And (Or OK empty (f B)) (g C) (And (Or (TA cut) empty (f D)) (g E) (TA cut))) 
    (of_alt [:: 
      [:: (cut, (of_alt[:: [:: callN B; callN C]])); (cut, nilC) ];
      [:: callN D; callN E]; 
      [:: callN B; callN C]]%SEQ).
Proof.
  move=> B C D E p/=.
  rewrite/t2l/=.
  move=>//.
Qed.

Goal forall A B C,
  let f x := (TA (call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester
    (Or (Or (Or (TA cut) empty ((Or (TA cut) empty (f A)))) empty (f B)) empty (f C))
    (of_alt[:: 
      [::(cut, (of_alt[:: [:: callN B]; [::callN C]]))];
      [::(cut, (of_alt[:: [:: callN B]; [::callN C]]))];
      [:: callN A]; 
      [:: callN B];
      [:: callN C] ]%SEQ).
Proof.
  move=> A B C p/=.
  rewrite/t2l/=.
  move=>//=.
Qed.

Goal forall A B C,
  let f x := (TA (call x)) in
  (* ((! \/ ! \/ A) \/ B) \/ C *)
  tester 
    (Or (Or (Or (And (TA cut) ([::]) OK) empty ((Or (TA cut) empty (f A)))) empty (f B)) empty (f C)) 
    (of_alt[:: 
      [::(cut, (of_alt[:: [:: callN B]; [::callN C]]))];
      [::(cut, (of_alt[:: [:: callN B]; [::callN C]]))];
      [:: callN A]; 
      [:: callN B];
      [:: callN C] ]%SEQ).
Proof.
  move=> A B C p/=.
  rewrite/t2l/=.
  move=>//=.
Qed.


Goal forall A B C D0 D,
  let f x := (TA (call x)) in
  (* (((! \/ ! \/ A) \/ B) \/ C) /\ D*)
  tester
    (And (Or (Or (Or (TA cut) empty ((Or (TA cut) empty (f A)))) empty (f B)) empty (f C)) (g D0) (f D))
    (of_alt[:: 
      [::(cut, (of_alt [:: [:: callN B; callN D0]; [::callN C; callN D0]])); callN D];
      [::(cut, (of_alt [:: [:: callN B; callN D0]; [::callN C; callN D0]])); callN D0];
      [:: callN A; callN D0]; 
      [:: callN B; callN D0];
      [:: callN C; callN D0] ]%SEQ).
Proof.
  move=> A B C D0 D p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall X A B C D0 D,
  let f x := (TA (call x)) in
  (* ((X \/ ((! \/ ! \/ A) \/ B) \/ C)) /\ D*)
  tester 
    (And (Or (f X) empty (Or (Or (Or (TA cut) empty ((Or (TA cut) empty (f A)))) empty (f B)) empty (f C))) (g D0) (f D))
    (of_alt[:: 
      [:: callN X; callN D];
      [::(cut, (of_alt[:: [:: callN B; callN D0]; [::callN C; callN D0]])); callN D0];
      [::(cut, (of_alt[:: [:: callN B; callN D0]; [::callN C; callN D0]])); callN D0];
      [:: callN A; callN D0]; 
      [:: callN B; callN D0];
      [:: callN C; callN D0] ]%SEQ).
Proof.
  move=> X A B C D0 D p/=.
  rewrite/t2l/=.
  f_equal => //.
Qed.

Goal forall B0 A B C D,
  let f x := (TA (call x)) in
  (* (((A /\ (! \/ B)) \/ C \/ D)) *)
  tester 
    (Or (Or (f C) empty (And (f A) (g B0) (Or (TA cut) empty (f B)))) empty (f D))
    (of_alt[:: 
      [:: callN C]; 
      [:: callN A; (cut, (of_alt[:: [:: callN D]]))]; 
      [:: callN A; callN B]; [:: callN D]]%SEQ).
Proof.
  move=> B0 A B C D p/=.
  rewrite/t2l/=.
  rewrite//.
Qed.

Goal forall A B C,
  let f x := (TA (call x)) in
  (* (((! \/ A) \/ !) \/ B) \/ C *)
  tester 
    (Or (Or (Or (Or (TA cut) empty (f A)) empty (TA cut)) empty (f B)) empty (f C))
    (of_alt[:: 
      [::(cut, (of_alt[::[::(cut, (of_alt[::[::callN B]; [::callN C]]))]; [::callN B]; [::callN C]]))];
      [::callN A];
      [::(cut, (of_alt[::[::callN B]; [::callN C]]))];
      [::callN B];
      [::callN C]
    ]%SEQ).
Proof.
  move=> p A B C/=.
  rewrite/t2l/=.
  rewrite//.
Qed.
Goal forall p l,
  let s := ((Or (Or Dead empty (TA cut)) empty OK)) in
  let bt := of_alt([::]%SEQ :: l) in
  t2l s empty (of_alt l) = of_alt[:: [:: (cut, bt)]; [::]]%SEQ /\ 
    t2l (odflt KO (next_alt true (step u p fset0 empty s).2)) empty (of_alt l) ++ (of_alt l) = bt.
Proof.
  move=>//= _ l.
  rewrite cat_cons cat0s//.
Qed.

End Nur.
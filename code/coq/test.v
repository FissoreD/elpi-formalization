From mathcomp Require Import all_ssreflect.
From det Require Import program.
From det Require Import interpreter.
From det Require Import semantic.
From det Require Import aux.

Module Test1.


  Definition p : predname := 0.
  Definition f : predname := 1.
  Definition q : predname := 2.

  Definition bodiesTest (n:predname) : seq (seq pred) := match n with
    | 0 (*p*) => [:: ((call f) :: (call f) :: nil); [::call f] ; [::]]
    | 1 (*f*) => [:: [::]; [::]; [::]]
    | 2 (*q*) => [:: [::call p] ; [::call 3]]
    | _ => [::]
  end.

  Ltac step := econstructor 2 with (n:=100) (m:=100); simpl.

  Definition p1 : bodiesT := fun n =>
    match n with 
    | 0 => [:: [::]]
    | _ => [::]
    end.

  Definition p2 : bodiesT := fun n =>
    match n with 
    | 0 => [:: [::]; [:: call 1]]
    | _ => [::]
    end.

  Definition p3 : bodiesT := fun n =>
    match n with 
    | 0 => [:: [::cut]; [:: call 1]]
    | _ => [::]
    end.

  Definition p4 : bodiesT := fun n =>
    match n with 
    | 0 => [:: [:: call 1];  [::]]
    | _ => [::]
    end.

  Lemma a: same_solutions p1 p2 [::[:: Goal (call 0) [::]]] [::[:: Goal (call 0) [::]]].
  Proof.
    step.
    constructor;[reflexivity|]; try reflexivity.
    econstructor 1.
    destruct n; auto.
  Qed.

  Lemma b: same_solutions p1 p3 [::[:: Goal (call 0) [::]]] [::[:: Goal (call 0) [::]]].
  Proof.
    step.
    constructor;
    reflexivity.
    repeat constructor.
  Qed.

  Lemma c: same_solutions p1 p4 [::[:: Goal (call 0) [::]]] [::[:: Goal (call 0) [::]]].
  Proof.
    step.
    repeat constructor.
    repeat constructor.
  Qed.

  Lemma d: forall g, same_solutions p1 p3 [::[:: Goal g [::]]] [::[:: Goal g [::]]].
  Proof.
    destruct g.
    step.
    constructor; reflexivity.
    repeat constructor.

    destruct (n).
    apply b.

    constructor 1.
    simpl.
    destruct n1; auto.
  Qed.

  Lemma e: same_semantics p1 p3.
  Proof.
    intros ?.
    induction gs as [|g gs]; simpl.
    - step; repeat constructor.
    - inversion IHgs; subst; simpl in *. 
      * econstructor 1.
        move=> [|] // /=.
        destruct g as[|p]; auto.
        destruct p; simpl; auto; constructor.
        destruct (H n); auto.
        destruct n; auto.
        simpl; destruct (H n); auto.
      * destruct g.
          econstructor 2 with (n:=1+n) (m:=m.+1) (x:= x) (y:=y); simpl; auto.
        destruct n0.
          econstructor 2 with (n:=1+n) (m:=m.+2) (x:= x) (y:=y); simpl; auto.
        constructor.
        intros []; auto.
  Qed.

  

  Lemma xx {T : Type}: forall l0 l1 l2 l3 l4 l5 (e:T),
    rev (l0 :: l1) = l2 :: l3 ->
      rcons (rev l3) (e :: l2) = l4 :: l5 ->
        l0 = l4 /\ exists lk, rcons lk l2 = l1 /\ rcons lk (e :: l2) = l5.
  Proof.
    intros.
  Admitted.


  Lemma g: same_semantics p1 (add_last_cut p1).
  Proof.
    intros ?.
    induction gs as [|g gs]; simpl.
    - step; repeat constructor.
    - inversion IHgs; clear IHgs; subst.
      * simpl in *.
        econstructor 1.
        simpl.
        intros.
        destruct n; auto.
        simpl.
        destruct g; auto.
        unfold add_last_cut.
        destruct (p1 p0); simpl; auto.
        rewrite fold_add_last_cut.
        destruct (rev (l::l0)) eqn:R.
        destruct (rev_non_empty _ _ R).
        destruct (rcons (rev l2) (cut :: l1)) eqn:RC.
        destruct (rcons_non_empty _ _ RC).
        pose proof (xx _ _ _ _ _ _ _ R RC) as []; subst.
        destruct H1.
        destruct H0.
        subst.
        constructor.
        rewrite cats0.
        pose proof (run_alternatives_none p1 n).
  Abort.
End Test1.

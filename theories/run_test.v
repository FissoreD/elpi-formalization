From mathcomp Require Import all_ssreflect.
From det Require Import lang run.

Notation "X &&& Y" := (And X _ Y) (at level 3).
Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
Notation "` X" := ((ACall X)) (at level 3).

Definition empty_sig : sigT := fun _ => b(d Func).

Definition build_progr l := {|
    modes := (fix rec t := match t with RCallable_Comb h _ => o :: rec h | RCallable_Kp _ => [::] end);
    sig := empty_sig;
    rules := l;
|}.

(* Section RunAxiom:= Run(UAxioms). *)
Definition unifyF    (t1 t2 : Tm) (s : Sigma) :=
  match t1, t2 with
  | Tm_V X, _ => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t2 else s.(sigma) x) |} | Some t => if t == t2 then Some s else None end
  | _, Tm_V X => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t1 else s.(sigma) x) |} | Some t => if t == t1 then Some s else None end
  | _, _ => if t1 == t2 then Some s else None
  end.

Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.

(* Definition derefF (s:Sigma) (t1:Tm) : Tm := t1. *)

Definition unif : Unif := {|
  unify := unifyF;
  matching := matchingF;
  (* deref := derefF; *)
|}.

Definition r := (IKp 2).
Definition p := (IKp 1).
Definition q := (IKp 0).

Definition v_X := Tm_V (IV 0).
Definition pred_q x  := Tm_Comb (Tm_Kp p) x.
Definition pred_p x  := Tm_Comb (Tm_Kp q) x.
Definition pred_r x  := Tm_Comb (Tm_Kp r) x.
Definition pred_fail := Tm_Kp (IKp 100).

Definition s1 := {| sigma := (fun x => if x == IV 0 then Some (Tm_Kd (IKd 1)) else None) |}.
Definition s2 := {| sigma := (fun x => if x == IV 0 then Some (Tm_Kd (IKd 2)) else None) |}.

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 2))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp r) (Tm_Kd (IKd 2))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1)))
        [:: ACall (Callable_Comb (Callable_Kp p) v_X) ; ACall (Callable_Comb (Callable_Kp r) v_X) ] 
    ].


  Goal Texists r, runb unif empty (CallS p_test (Callable_Comb (Callable_Kp q) (Tm_Kd (IKd 1)))) s2 r false.
  Proof.
    eexists.
    apply: run_backtrack => //.
    - apply: expanded_step.
      - move=> //.
      - rewrite /big_or/F/select//=.
        apply: expanded_fail => //=.
    - move=>/=. reflexivity.
    - apply: run_backtrack => //.
      - apply: expanded_step => //=.
        rewrite /big_or/F/select/= -/s1 -/s2.
        (* apply: expanded_step => //=. *)
        apply: expanded_fail => //=.
      - reflexivity.
      - apply: run_backtrack => //.
        - apply: expanded_step => //=.
          apply: expanded_step => //=.
          (* apply: expanded_step => //=. *)
          apply: expanded_fail => //=.
        - move=> //=.
        - apply: run_backtrack => //.
          - apply: expanded_fail => //.
          - move=> //.
          - apply: run_backtrack.
            apply: expanded_step => //=.
            apply: expanded_step => //=.
            rewrite /big_or/F//=.
            (* apply: expanded_step => //=. *)
            apply: expanded_fail => //=.
          - move=>//.
          - apply: run_done.
            apply: expanded_step => //=.
            apply: expanded_step => //=.
            apply: expanded_done => //=.
            reflexivity.
            reflexivity.
            reflexivity.
  Qed.
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 0))) 
        [::ACall (Callable_Comb (Callable_Kp q) v_X); ACut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
    ].

  Goal Texists r, runb unif empty (CallS p_test1 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) s1 r false 
    /\ forall s, dead_run unif s r.
  Proof.
    repeat eexists.
    apply: run_backtrack.
    apply: expanded_step.
    + move=> //.
    + rewrite /big_or/F/select/=.
      (* apply: expanded_step => //=. *)
      apply: expanded_fail => //.
      reflexivity.
    apply: run_backtrack => //.
      apply: expanded_step => //=.
    + rewrite /big_or/F/select/=.
      (* apply: expanded_step => //=. *)
      apply: expanded_fail => //=.
      reflexivity.
      rewrite -/s1-/s2.
      apply: run_done.
      apply: expanded_step => //.
      rewrite [CutS]lock.
      apply: expanded_step => //=.
      rewrite -lock [mkAnd]lock /= -/s1 -/s2.
      rewrite -lock [mkOr]lock /=.
      rewrite -lock //=.
      apply: expanded_step => //=.
      apply: expanded_done => //=.
      reflexivity.
      reflexivity.
    move=> s1 s2 B b.
    inversion 1; subst => //.
      inversion H0 => //.
    inversion H0; clear H0 => //; subst.
    inversion H6; clear H6; subst => //.
    inversion H1; clear H1; subst => //.
    inversion H2; clear H2; subst => //.
      inversion H0 => //.
    inversion H0; clear H0 => //; subst.
    inversion H6; subst => //; clear H6.
    inversion H1; clear H1; subst => //.
    inversion_clear H3; subst.
    inversion_clear H0 => //.
    inversion_clear H0 => //.
    move: H3 => [?]; subst => //.
  Qed.
End Test5.

Section Test6.

  Definition pred_true := ((IKp 200)).

  Definition p_test2 : program := build_progr [:: 
      mkR ((RCallable_Kp pred_true)) [::];
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 0))) 
        [::ACall (Callable_Comb (Callable_Kp q) v_X);ACall ((Callable_Kp pred_true)); ACut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
  ].

  Goal Texists r, 
    runb unif empty ((CallS p_test2 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) ) s1 r false 
      /\ forall s, dead_run unif s r.
  Proof.
    repeat eexists.
    apply: run_backtrack.
    apply: expanded_step.
    + move=> //.
    + rewrite /big_or/F/select/=.
      (* apply: expanded_step => //=. *)
      apply: expanded_fail => //.
      reflexivity.
    apply: run_backtrack => //.
      apply: expanded_step => //=.
    + rewrite /big_or/F/select/=.
      (* apply: expanded_step => //=. *)
      apply: expanded_fail => //=.
      rewrite -/s2 -/s1.
      reflexivity.
      apply: run_backtrack.
      apply: expanded_step => //.
      (* rewrite [Cut]lock. *)
      apply: expanded_step => //=.
      (* apply: expanded_step => //=. *)
      apply: expanded_fail => //=.
      move=>//.
      apply: run_done.
      apply: expanded_step => //=.
      apply: expanded_step => //=.
      apply: expanded_step => //=.
      apply: expanded_done => //=.
      reflexivity.
      reflexivity.
      reflexivity.
    - move=> s1 s2 A b H.
      inversion_clear H.
        by inversion_clear H0.
      inversion_clear H0 => //.
      case: H => ?; subst.
      case: H1 => ?; subst.
      inversion_clear H2 => //.
      inversion_clear H => //.
      inversion_clear H => //.
      case: H2 => ?; subst.
      case: H0 => ?; subst.
      inversion_clear H1 => //.
        by inversion_clear H => //.
      inversion_clear H => //.
      case: H1 => ?; subst.
      case: H0 => ?; subst.
      inversion_clear H2 => //.
        by inversion_clear H => //.
      inversion_clear H => //.
      case: H2 => ?; subst => //.
  Qed.
End Test6.


Section Test2.
  (* Import RunAxiom. *)
  Goal expand unif empty (Or OK empty OK) = Success empty (Or OK empty OK) . by []. Qed.

  Goal runb unif empty (Or (CutS) empty OK) empty (Or Bot empty Bot) false.
    apply: run_done => //=. 
    apply: expanded_step => //=.
    by apply: expanded_done => /=.
    move=>/=.
    reflexivity. 
  Qed.

  Goal forall r, 
    runb unif empty (Or (CutS) empty r) empty (Or Bot empty (cutr r)) false.
    move=> r.
    apply: run_done.
    apply: expanded_step => //=.
    apply: expanded_done => //=.
    move=>/=.
    reflexivity.
  Qed.

  Goal runb unif empty (Or OK empty (Or OK empty OK)) empty (Or Bot empty (((Or OK empty OK)))) false.
  Proof. apply: run_done => //=. apply: expanded_done => //=.
    move=>/=.
    reflexivity. Qed.

  (* (Dead \/ !) \/ C *)
  Goal expand unif empty (Or (Or Dead empty (CutS)) empty Top) = Expanded empty (Or (Or Dead empty OK) empty Top) .
  Proof.
    move=>//=.
  Qed.

  (* Goal forall s s1 p R B, 
    failed p = false -> failed R = false -> 
      run s (And (Or OK s1 p) R OK) s B -> 
        next_alt s B = Some (s1, And (Or Dead s1 p) R R).
  Proof.
    move=> s s1 p R B fP fR [b H].
    inversion H; clear H; subst.
      inversion H0; subst => //.
      case: H6 => <-.
      simpl clean_success.
      simpl.
      rewrite (failed_dead fP)fR.
      case X: next_alt => [[x xs]|].
      case: ifP => // dP _.
      rewrite fP fR//.
    inversion H0; subst => //.
  Qed. *)
End Test2.

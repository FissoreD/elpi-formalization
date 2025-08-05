From mathcomp Require Import all_ssreflect.
From det Require Import lang.
Import Language.

Definition empty_sig : sigT := fun _ => b(d Func).

Definition build_progr l := {|
    modes := (fix rec (t : Tm) := match t with Comb h _ => o :: rec h | Code _ | Data _ => [::] end);
    sig := empty_sig;
    rules := l;
|}.

Module Axioms.
  Parameter program_eqb : program -> program -> bool.
  Parameter is_program : program -> Type.
  Parameter is_program_inhab : forall p : program, is_program p.
  Parameter program_eqb_correct : forall p1 p2, program_eqb p1 p2 -> p1 = p2.
  Parameter program_eqb_refl : forall x, program_eqb x x.


  Parameter Sigma_eqb : Sigma -> Sigma -> bool.
  Parameter is_Sigma : Sigma -> Type.
  Parameter is_Sigma_inhab : forall p : Sigma, is_Sigma p.
  Parameter Sigma_eqb_correct : forall p1 p2, Sigma_eqb p1 p2 -> p1 = p2.
  Parameter Sigma_eqb_refl : forall x, Sigma_eqb x x.


  Parameter same_subst : forall (s1 s2 : Sigma), s1 = s2.
  Parameter same_progr : forall (s1 s2 : program), s1 = s2.
End Axioms.

Module UAxioms <: Unif.
  Axiom unify : Tm -> Tm -> Sigma -> option Sigma.
  Axiom matching : Tm -> Tm -> Sigma -> option Sigma.
  Include Axioms.
End UAxioms.
Module RunAxiom:= Run(UAxioms).

Module Test1.

  Module U <: Unif.
    Definition unify    (t1 t2 : Tm) (s : Sigma) :=
      match t1, t2 with
      | Code (v X), _ => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t2 else s.(sigma) x) |} | Some t => if t == t2 then Some s else None end
      | _, Code (v X) => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t1 else s.(sigma) x) |} | Some t => if t == t1 then Some s else None end
      | _, _ => if t1 == t2 then Some s else None
      end.

    Definition matching (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.
    Include Axioms.
  End U.

  Module Run := Run(U).
  Import Run.

  Definition v_X := Code (v 0).
  Definition pred_q x  := Comb (Code (p 1)) x.
  Definition pred_p x  := Comb (Code (p 0)) x.
  Definition pred_r x  := Comb (Code (p 2)) x.
  Definition pred_fail := Code (p 100).

  Definition p_test : program := build_progr [:: 
      mkR (pred_p (Data 1)) [::] ;
      mkR (pred_p (Data 2)) [::] ;
      mkR (pred_r (Data 2)) [::] ;
      mkR (pred_q (Data 1)) [:: Call (pred_p v_X) ; Call (pred_r v_X) ] 
    ].

  Notation "X &&& Y" := (And X _ Y) (at level 3).
  Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
  Notation "` X" := (Goal _ (Call X)) (at level 3).
  (* Notation "[ x -> _]" := {| sigma := (fun x : V => _) |} (x binder). *)

  Definition s1 := {| sigma := (fun x => if x == 0 then Some (Data 1) else None) |}.
  Definition s2 := {| sigma := (fun x => if x == 0 then Some (Data 2) else None) |}.

  Goal exists r, run empty (Goal p_test (Call (pred_q (Data 1)))) s2 r.
  Proof.
    do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_step => //=.
      rewrite /big_or/F/select/=.
      (* apply: expanded_step => //=. *)
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
          - apply: expanded_step => //=.
            apply: expanded_step => //=.
            rewrite /big_or/F//=.
            (* apply: expanded_step => //=. *)
            apply: expanded_fail => //=.
          - move=>//.
          - apply: run_done.
            apply: expanded_step => //=.
            apply: expanded_step => //=.
            apply: expanded_done => //=.
            move=>/=.
            reflexivity.
  Qed.
End Test1.

Module Test5.

  Module Run := Run(Test1.U).
  Import Run.

  Definition v_X := Code (v 0).
  Definition pred_f x  := Comb (Code (p 1)) x.
  Definition pred_g x  := Comb (Code (p 0)) x.

  Definition p_test : program := build_progr [:: 
      mkR (pred_f (Data 0)) [:: Call (pred_g v_X); Cut] ;
      mkR (pred_g (Data 1)) [::];
      mkR (pred_g (Data 2)) [::]
    ].

  Notation "X &&& Y" := (And X _ Y) (at level 3).
  Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
  Notation "` X" := (Goal _ (Call X)) (at level 3).
  (* Notation "[ x -> _]" := {| sigma := (fun x : V => _) |} (x binder). *)

  Definition s1 := {| sigma := (fun x => if x == 0 then Some (Data 1) else None) |}.
  Definition s2 := {| sigma := (fun x => if x == 0 then Some (Data 2) else None) |}.

  Goal exists r, run empty (Goal p_test (Call (pred_f (Data 0)))) s1 r /\ next_alt empty r = None.
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
      rewrite [Cut]lock.
      apply: expanded_step => //=.
      rewrite -lock [mkAnd]lock /= -/s1 -/s2.
      rewrite -lock [mkOr]lock /=.
      rewrite -lock //=.
      apply: expanded_step => //=.
      apply: expanded_done => //=.
      reflexivity.
      reflexivity.
    reflexivity.
  Qed.
End Test5.

Module Test6.

  Module Run := Run(Test1.U).
  Import Run.

  Definition v_X := Code (v 0).
  Definition pred_f x  := Comb (Code (p 1)) x.
  Definition pred_g x  := Comb (Code (p 0)) x.
  Definition pred_true := (Code (p 0)).

  Definition p_test : program := build_progr [:: 
      mkR pred_true [::];
      mkR (pred_f (Data 0)) [:: Call (pred_g v_X); Call pred_true; Cut] ;
      mkR (pred_g (Data 1)) [::];
      mkR (pred_g (Data 2)) [::]
  ].

  Notation "X &&& Y" := (And X _ Y) (at level 3).
  Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
  Notation "` X" := (Goal _ (Call X)) (at level 3).
  (* Notation "[ x -> _]" := {| sigma := (fun x : V => _) |} (x binder). *)

  Definition s1 := {| sigma := (fun x => if x == 0 then Some (Data 1) else None) |}.
  Definition s2 := {| sigma := (fun x => if x == 0 then Some (Data 2) else None) |}.

  Goal exists r, run empty (Goal p_test (Call (pred_f (Data 0)))) s1 r /\ next_alt empty r = None.
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
      reflexivity.
  Qed.
End Test6.


Module Test2.
  Import RunAxiom.
  Goal expand empty (Or OK empty OK) = Solved empty (Or OK empty OK) . by []. Qed.

  Goal forall p, run empty (Or (Goal p Cut) empty OK) empty (Or Bot empty Bot).
    move=> pr //=.
    eexists. apply: run_done => //=. 
    apply: expanded_step => //=.
    by apply: expanded_done => /=.
    move=>/=.
    reflexivity. 
  Qed.

  Goal forall p r, 
    run empty (Or (Goal p Cut) empty r) empty (Or Bot empty (cutr r)).
    move=> p; eexists.
    apply: run_done.
    apply: expanded_step => //=.
    apply: expanded_done => //=.
    move=>/=.
    reflexivity.
  Qed.

  Goal run empty (Or OK empty (Or OK empty OK)) empty (Or Bot empty (((Or OK empty OK)))).
  Proof. eexists; apply: run_done => //=. apply: expanded_done => //=.
    move=>/=.
    reflexivity. Qed.

  Goal forall s s1 p R B, 
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
      have := failed_dead fP.
      case: ifP => /eqP// dP _.
      rewrite fP fR//.
    inversion H0; subst => //.
  Qed.
End Test2.

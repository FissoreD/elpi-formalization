From mathcomp Require Import all_ssreflect.
From det Require Import lang run.
Import Language.


Notation "X &&& Y" := (And X _ Y) (at level 3).
Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
Notation "` X" := ((Call X)) (at level 3).

Definition empty_sig : sigT := fun _ => b(d Func).

Definition build_progr l := {|
    modes := (fix rec (t : Tm) := match t with Comb h _ => o :: rec h | Code _ | Data _ => [::] end);
    sig := empty_sig;
    rules := l;
|}.

(* Section RunAxiom:= Run(UAxioms). *)
Definition unifyF    (t1 t2 : Tm) (s : Sigma) :=
  match t1, t2 with
  | Code (v X), _ => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t2 else s.(sigma) x) |} | Some t => if t == t2 then Some s else None end
  | _, Code (v X) => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t1 else s.(sigma) x) |} | Some t => if t == t1 then Some s else None end
  | _, _ => if t1 == t2 then Some s else None
  end.

Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.
Definition unif : Unif := {|
  unify := unifyF;
  matching := matchingF
|}.


Definition v_X := Code (v 0).
Definition pred_q x  := Comb (Code (p 1)) x.
Definition pred_p x  := Comb (Code (p 0)) x.
Definition pred_r x  := Comb (Code (p 2)) x.
Definition pred_fail := Code (p 100).

Definition s1 := {| sigma := (fun x => if x == 0 then Some (Data 1) else None) |}.
Definition s2 := {| sigma := (fun x => if x == 0 then Some (Data 2) else None) |}.

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (pred_p (Data 1)) [::] ;
      mkR (pred_p (Data 2)) [::] ;
      mkR (pred_r (Data 2)) [::] ;
      mkR (pred_q (Data 1)) [:: Call (pred_p v_X) ; Call (pred_r v_X) ] 
    ].


  Goal exists r, runb unif empty (CallS p_test (pred_q (Data 1))) s2 r false.
  Proof.
    eexists.
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
            reflexivity.
  Qed.
End Test1.

Section Test5.

  Definition pred_f x  := Comb (Code (p 1)) x.
  Definition pred_g x  := Comb (Code (p 0)) x.

  Definition p_test1 : program := build_progr [:: 
      mkR (pred_f (Data 0)) [:: Call (pred_g v_X); Cut] ;
      mkR (pred_g (Data 1)) [::];
      mkR (pred_g (Data 2)) [::]
    ].

  Goal exists r, runb unif empty (CallS p_test1 ((pred_f (Data 0)))) s1 r false /\ next_alt None r = None.
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
    reflexivity.
  Qed.
End Test5.

Section Test6.

  Definition pred_true := (Code (p 0)).

  Definition p_test2 : program := build_progr [:: 
      mkR pred_true [::];
      mkR (pred_f (Data 0)) [:: Call (pred_g v_X); Call pred_true; Cut] ;
      mkR (pred_g (Data 1)) [::];
      mkR (pred_g (Data 2)) [::]
  ].

  (* Notation "[ x -> _]" := {| sigma := (fun x : V => _) |} (x binder). *)

  Goal exists r, runb unif empty (CallS p_test2 ((pred_f (Data 0)))) s1 r false /\ next_alt None r = None.
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

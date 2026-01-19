From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree tree_prop.

(* Notation "X &&& Y" := (And X _ Y) (at level 3).
Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
Notation "` X" := ((call X)) (at level 3). *)

Definition prop := b (d Pred).
Definition build_arr m := arr m prop prop.

Definition build_progr l := {|
    (* modes := [fmap].[IKp false <- [::o]].[IKp 1 <- [::o]].[IKp 2 <- [::o]].[IKp 200 <-  [::]]; *)
    sig := [fmap].[IKp false <- build_arr o].[IKp 1 <- build_arr o].[IKp 2 <- build_arr o].[IKp 200 <- prop];
    rules := l;
|}.

Definition unifyF    (t1 t2 : Tm) (s : Sigma) :=
  match t1, t2 with
  | Tm_V X, _ => match lookup X s with None => Some (add X t2 s) | Some t => if t == t2 then Some s else None end
  | _, Tm_V X => match lookup X s with None => Some (add X t2 s) | Some t => if t == t1 then Some s else None end
  | _, _ => if t1 == t2 then Some s else None
  end.

Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.

Definition unif : Unif := {|
  unify := unifyF;
  matching := matchingF;
|}.

Definition r := (IKp 2).
Definition p := (IKp 1).
Definition q := (IKp false).

Definition v_X := Tm_V (IV false).
Definition pred_q x  := Tm_Comb (Tm_Kp p) x.
Definition pred_p x  := Tm_Comb (Tm_Kp q) x.
Definition pred_r x  := Tm_Comb (Tm_Kp r) x.
Definition pred_fail := Tm_Kp (IKp 100).

Definition s1 : Sigma := [fmap].[IV false <- Tm_Kd (IKd 1)].
Definition s2 : Sigma := [fmap].[IV false <- Tm_Kd (IKd 2)].

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 2))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp r) (Tm_Kd (IKd 2))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1)))
        [:: call (Callable_Comb (Callable_Kp p) v_X) ; call (Callable_Comb (Callable_Kp r) v_X) ] 
    ].

  Goal unify unif v_X (Tm_Kd (IKd 1)) empty = Some s1.
  Proof.
    rewrite/unif.
    rewrite [unifyF]lock/=-lock.
    rewrite/unifyF/= fnd_fmap0.
    move=> //.
  Qed.

  (* Goal Texists r, runb unif empty (CallS p_test (Callable_Comb (Callable_Kp q) (Tm_Kd (IKd 1)))) (Some s2) r false.
  Proof.
    eexists.
    apply: run_step => //.
    apply: run_fail => //=. 
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //.
    apply: run_done => //=.
  Qed. *)
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd false))) 
        [::call (Callable_Comb (Callable_Kp q) v_X); cut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
    ].

  (* Goal Texists r, runb unif empty (CallS p_test1 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd false)))) (Some s1) r false /\ is_dead r.
  Proof.
    repeat eexists.
    apply: run_step => //.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_done => //=.
    by [].
  Qed. *)
End Test5.

Section Test6.

  Definition pred_true := ((IKp 200)).

  Definition p_test2 : program := build_progr [:: 
      mkR ((RCallable_Kp pred_true)) [::];
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd false))) 
        [::call (Callable_Comb (Callable_Kp q) v_X);call ((Callable_Kp pred_true)); cut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
  ].

  (* Goal Texists r, runb unif empty ((CallS p_test2 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd false)))) ) (Some s1) r false /\ is_dead r.
  Proof.
    repeat eexists.
    apply: run_step => //.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_done => //.
    by [].
  Qed. *)
End Test6.

Definition CutS := TA (build_progr [::]) cut.

Section Test2.
  Goal step unif empty (Or OK empty OK) = (Success, Or OK empty OK). by []. Qed.

  Goal runb unif empty (Or (CutS) empty OK) (Some empty) (Or Dead empty Dead) false.
    apply: run_step => //=.
    apply: run_done => //.
  Qed.

  Goal forall r, 
    runb unif empty (Or (CutS) empty r) (Some empty) (dead (Or (CutS) empty r)) false.
    move=> r.
    apply: run_step => //.
    apply: run_done => //=.
    rewrite next_alt_cutr /= dead_cutr//.
  Qed.

  Goal runb unif empty (Or OK empty (Or OK empty OK)) (Some empty) ((Or Dead empty (((Or OK empty OK))))) false.
  Proof. apply: run_done => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal step unif empty (Or (Or Dead empty (CutS)) empty OK) = (Expanded, (Or (Or Dead empty OK) empty OK)).
  Proof.
    move=>//=.
  Qed.
End Test2.

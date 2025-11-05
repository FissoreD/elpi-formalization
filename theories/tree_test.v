From mathcomp Require Import all_ssreflect.
From det Require Import lang tree tree_prop.

Notation "X &&& Y" := (And X _ Y) (at level 3).
Notation "X ||[ Y s ]" := (Or X s Y) (at level 3).
Notation "` X" := ((ACall X)) (at level 3).

Definition empty_sig : sigT := fun _ => b(d Func).

Definition build_progr l := {|
    modes := (fix rec t := match t with RCallable_Comb h _ => o :: rec h | RCallable_Kp _ => [::] end);
    sig := empty_sig;
    rules := l;
|}.

Definition unifyF    (t1 t2 : Tm) (s : Sigma) :=
  match t1, t2 with
  | Tm_V X, _ => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t2 else s.(sigma) x) |} | Some t => if t == t2 then Some s else None end
  | _, Tm_V X => match s.(sigma) X with None => Some {| sigma := (fun x => if x == X then Some t1 else s.(sigma) x) |} | Some t => if t == t1 then Some s else None end
  | _, _ => if t1 == t2 then Some s else None
  end.

Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.

Definition unif : Unif := {|
  unify := unifyF;
  matching := matchingF;
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


  Goal Texists r, runb unif empty (CallS p_test (Callable_Comb (Callable_Kp q) (Tm_Kd (IKd 1)))) (Some s2) r 0.
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
  Qed.
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 0))) 
        [::ACall (Callable_Comb (Callable_Kp q) v_X); ACut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
    ].

  Goal Texists r, runb unif empty (CallS p_test1 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) (Some s1) r 0 /\ is_dead r.
  Proof.
    repeat eexists.
    apply: run_step => //.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_fail => //=.
    apply: run_step => //=.
    apply: run_done => //=.
    by [].
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

  Goal Texists r, runb unif empty ((CallS p_test2 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) ) (Some s1) r 0 /\ is_dead r.
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
  Qed.
End Test6.


Section Test2.
  Goal expand unif empty (Or OK empty OK) = Success (Or OK empty OK) . by []. Qed.

  Goal runb unif empty (Or (CutS) empty OK) (Some empty) (Or Dead empty Dead) 0.
    apply: run_step => //=.
    apply: run_done => //.
  Qed.

  Goal forall r, 
    runb unif empty (Or (CutS) empty r) (Some empty) (dead (Or (CutS) empty r)) 0.
    move=> r.
    apply: run_step => //.
    apply: run_done => //=.
    rewrite next_alt_cutr /= dead_cutr//.
  Qed.

  Goal runb unif empty (Or OK empty (Or OK empty OK)) (Some empty) ((Or Dead empty (((Or OK empty OK))))) 0.
  Proof. apply: run_done => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal expand unif empty (Or (Or Dead empty (CutS)) empty OK) = Expanded (Or (Or Dead empty OK) empty OK) .
  Proof.
    move=>//=.
  Qed.
End Test2.

From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree tree_prop.

Definition prop := b (d Pred).
Definition build_arr m := arr m prop prop.

Definition build_progr l := {|
  sig := [fmap].[IP false <- build_arr o].[IP 1 <- build_arr o].[IP 2 <- build_arr o].[IP 200 <- prop];
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

Definition r := (IP 2).
Definition p := (IP 1).
Definition q := (IP false).

Definition v_X := Tm_V (IV false).
Definition pred_q x  := Tm_App (Tm_P p) x.
Definition pred_p x  := Tm_App (Tm_P q) x.
Definition pred_r x  := Tm_App (Tm_P r) x.
Definition pred_fail := Tm_P (IP 100).

Definition s1 : Sigma := [fmap].[IV false <- Tm_D (ID 1)].
Definition s2 : Sigma := [fmap].[IV false <- Tm_D (ID 2)].

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (Callable_App (Callable_P p) (Tm_D (ID 1))) [::] ;
      mkR (Callable_App (Callable_P p) (Tm_D (ID 2))) [::] ;
      mkR (Callable_App (Callable_P r) (Tm_D (ID 2))) [::] ;
      mkR (Callable_App (Callable_P q) (Tm_D (ID 1)))
        [:: call (Callable_App (Callable_P p) v_X) ; call (Callable_App (Callable_P r) v_X) ] 
    ].

  Goal unify unif v_X (Tm_D (ID 1)) empty = Some s1.
  Proof.
    rewrite/unif.
    rewrite [unifyF]lock/=-lock.
    rewrite/unifyF/= fnd_fmap0.
    move=> //.
  Qed.

  (* Goal Texists r, run unif empty (CallS p_test (Callable_App (Callable_P q) (Tm_D (ID 1)))) (Some s2) r false.
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
      mkR (Callable_App (Callable_P p) (Tm_D (ID false))) 
        [::call (Callable_App (Callable_P q) v_X); cut] ;
      mkR (Callable_App (Callable_P q) (Tm_D (ID 1))) [::] ;
      mkR (Callable_App (Callable_P q) (Tm_D (ID 2))) [::] 
    ].

  (* Goal Texists r, run unif empty (CallS p_test1 (Callable_App (Callable_P p) (Tm_D (ID false)))) (Some s1) r false /\ is_dead r.
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

  Definition pred_true := ((IP 200)).

  Definition p_test2 : program := build_progr [:: 
      mkR ((Callable_P pred_true)) [::];
      mkR (Callable_App (Callable_P p) (Tm_D (ID false))) 
        [::call (Callable_App (Callable_P q) v_X);call ((Callable_P pred_true)); cut] ;
      mkR (Callable_App (Callable_P q) (Tm_D (ID 1))) [::] ;
      mkR (Callable_App (Callable_P q) (Tm_D (ID 2))) [::] 
  ].

  (* Goal Texists r, run unif empty ((CallS p_test2 (Callable_App (Callable_P p) (Tm_D (ID false)))) ) (Some s1) r false /\ is_dead r.
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

Definition emptyp := (build_progr [::]).

Definition CutS := TA cut.

Section Test2.
  Goal step unif emptyp fset0 empty (Or (Some OK) empty OK) = (fset0, Success, Or (Some OK) empty OK). by []. Qed.

  Goal run unif emptyp fset0 empty (Or (Some CutS) empty OK) (Some empty) None false fset0.
    apply: run_step => //=.
    apply: run_done => //.
  Qed.

  Goal forall r, 
    run unif emptyp fset0 empty (Or (Some CutS) empty r) (Some empty) None false fset0.
    move=> r.
    apply: run_step => //.
    apply: run_done => //=.
  Qed.

  Goal run unif emptyp fset0 empty (Or (Some OK) empty (Or (Some OK) empty OK)) (Some empty) (Some (Or None empty (((Or (Some OK) empty OK))))) false fset0.
  Proof. apply: run_done => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal step unif emptyp fset0 empty (Or (Some (Or None empty (CutS))) empty OK) = (fset0, Expanded, (Or (Some (Or None empty OK)) empty OK)).
  Proof.
    move=>//=.
  Qed.
End Test2.

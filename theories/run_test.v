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

(* Lemma deref_vars:
  de *)

Definition inter {T : eqType} (s1 s2 : seq T) :=
  [seq x <- s1 | x \in s2].

Eval compute in inter [:: 1; 2; 3] [:: 2; 3; 4].

(* Lemma deref_superset s t3:
  all (mem s.(all_vars)) ((vars (deref s t3))).
Proof.
  elim: t3 => //=.
  - move=> v; case: s => //= s av H1 H2.
    case X: s => [t1|]/=; last first.
      rewrite andbT.
    Admitted. *)

(* Fixpoint subst (tm:Tm) (k:V) (v:Tm) :=
  match tm with
  | Tm_V k' => if k == k' then v else tm
  | Tm_Kd _ | Tm_Kp _ => tm
  | Tm_Comb hd bo => Tm_Comb (subst hd k v) (subst bo k v)
  end.

Definition add_subst (s:Sigma) (k:V) (v:Tm) : Sigma.
Proof.
  case: s; rewrite/valid_sigma_def => /= s av H1 H2.
  refine {|sigma := foldl (fun s' v' => fun k => if k == v' then ((omap (fun tm => subst tm k v) (s' v'))) else s' v') s av |}.
  let l := s.(all_vars) in
  foldl (fun s' v' => ) s l. *)

(* Section RunAxiom:= Run(UAxioms). *)
Definition unifyF  : forall  (t1 t2 : Tm) (s : Sigma), option Sigma.
Proof.
  move=> t1 t2 s.
  remember (deref s t1) as t1' eqn:H1.
  remember (deref s t2) as t2' eqn:H2.
  case X : (t1' == t2'); move /eqP: X => H; subst.
    apply: Some s.
  case: t1 H => /=.
  - move=> k; case: t2 => /=.
    - move=> _ _; apply: None.
    - move=> _ _; apply: None.
    - move=>v. 
      case S: sigma => //=[a|]; last first.
      - move=> H.
        refine (Some {| 
          sigma := (fun x => if (x == v) then Some (Tm_Kp k) else s.(sigma) x); 
          all_vars := v :: s.(all_vars) |}) => /=.
        - move=> v'; rewrite in_cons; case: eqP => //=; case: s S => /= sigma av H1 H2 H3 S//.
        - (*TODO: this is wrong... since we need do explore all the subst and make all v to point to k...*)

  
Definition unifyF  : forall  (t1 t2 : Tm) (s : Sigma), option Sigma.
Proof.
  move=> t1 t2 s.
  refine (let t1 := deref s t1 in let t2 := deref s t2 in
    if t1 == t2 then Some s else
    match t1, t2 with
    | Tm_V X, t2 => 
      if X \in vars t2 then None 
      else 
        Some {| 
          sigma := (fun x => if (x == X) then Some t2 else s.(sigma) x); 
          all_vars := X :: s.(all_vars) |} 
    | _, Tm_V X => 
      if X \in vars t1 then None 
      else 
        Some {| 
          sigma := (fun x => if (x == X) then Some t1 else s.(sigma) x); 
          all_vars := X :: s.(all_vars) |} 
    | _, _ => None
  end) => //=; rewrite/t1/t2.
  (* Show Proof. *)
  -
    { move=> x; case: eqP => //=; case: s {t1 t2} => //=sigma v1 H H1.
        move=> ->; rewrite /=in_cons?eqxx//=.
      rewrite in_cons; case: eqP => //=; rewrite !andbT?andbF.
    }
    {
      case: s t1 t2; rewrite/valid_sigma_def => /= sigma av H1 H2 _ _.
      move=> x t; case: eqP.
        move=> ?[]?; subst.
        elim: t3 => //=.
        - move=> v; case H3: sigma => [t|]//=.
          - 
        - move=> _.
    }


        
        ; case: eqP => //=; rewrite ?andbT//=.
  Admitted.


Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None.

(* Definition derefF (s:Sigma) (t1:Tm) : Tm := t1. *)

Lemma match_propF (s : Sigma) (t1 t2 : Tm) (r : Sigma):
matchingF t1 t2 s = Some r ->
let v1 := vars t1 in all (fun x => sigma r x == None) v1 .
Admitted.
Lemma smaller_sigmaF s1 s2 : smaller_sigmaD unifyF s1 s2.
Admitted.

Definition unif : Unif := {|
  unify := unifyF;
  matching := matchingF;
  match_prop := match_propF;
  smaller_sigma := smaller_sigmaF;
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


  Goal exists r, runb unif empty (CallS p_test (Callable_Comb (Callable_Kp q) (Tm_Kd (IKd 1)))) s2 r false.
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

  Goal exists r, runb unif empty (CallS p_test1 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) s1 r false /\ next_alt None r = None.
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

  Definition pred_true := ((IKp 200)).

  Definition p_test2 : program := build_progr [:: 
      mkR ((RCallable_Kp pred_true)) [::];
      mkR (RCallable_Comb (RCallable_Kp p) (Tm_Kd (IKd 0))) 
        [::ACall (Callable_Comb (Callable_Kp q) v_X);ACall ((Callable_Kp pred_true)); ACut] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 1))) [::] ;
      mkR (RCallable_Comb (RCallable_Kp q) (Tm_Kd (IKd 2))) [::] 
  ].

  Goal exists r, 
    runb unif empty ((CallS p_test2 (Callable_Comb (Callable_Kp p) (Tm_Kd (IKd 0)))) ) s1 r false /\ next_alt None r = None.
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

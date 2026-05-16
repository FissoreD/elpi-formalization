From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree unif.

Definition prop := b (d Pred).
Definition build_arr := arr output prop prop.

Definition build_progr l := {|
  sig := [fmap].[IP false <- build_arr].[IP 1 <- build_arr].[IP 2 <- build_arr].[IP 200 <- prop];
  rules := l;
|}.

(* Definition unifyF    (t1 t2 : Tm) (s : Sigma) :=
  match t1, t2 with
  | Tm_V X, _ => match lookup X s with None => Some (add X t2 s) | Some t => if t == t2 then Some s else None end
  | _, Tm_V X => match lookup X s with None => Some (add X t2 s) | Some t => if t == t1 then Some s else None end
  | _, _ => if t1 == t2 then Some s else None
  end.

Definition matchingF (t1 t2 : Tm) (s : Sigma) := if t1 == t2 then Some s else None. *)

Definition unif : Unif := mk_Unif unify matching.

Notation r := (IP 2).
Notation p := (IP 1).
Notation q := (IP false).

Definition v_X := Tm_V (IV false).
Definition pred_q x  := Tm_App (Tm_P p) x.
Definition pred_p x  := Tm_App (Tm_P q) x.
Definition pred_r x  := Tm_App (Tm_P r) x.
Definition pred_fail := Tm_P (IP 100).

Definition s1 : Sigma := [fmap].[fresh [fset IV false] <- Tm_D (ID 1)].
Definition s2 : Sigma := [fmap].[fresh [fset IV false] <- Tm_D (ID 2)].
Definition s3 : Sigma := empty.[fresh
         (IV 0
          |` (varsU_rule
                {|
                  head := Tm_App (Tm_P (IP 0)) (Tm_D (ID 2));
                  premises := [::]
                |}
              `|` varsU_rule
                    {|
                      head := Tm_App test.p (Tm_D (ID 0));
                      premises :=
                        [:: call (Tm_App (Tm_P (IP 0)) v_X); cut]
                    |})) <- Tm_D (ID 1)].
Definition pred_true := ((IP 200)).

Definition s4 := empty.[fresh
         (IV 0
          |` (varsU_rule
                {|
                  head := Tm_App (Tm_P (IP 0)) (Tm_D (ID 2)); premises := [::]
                |}
              `|` varsU_rule
                    {|
                      head := Tm_App test.p (Tm_D (ID 0));
                      premises :=
                        [:: call (Tm_App (Tm_P (IP 0)) v_X);
                            call (Tm_P pred_true); cut]|})) <- Tm_D (ID 1)].

Lemma vars_sigma_set v s: vars_sigma empty.[v <- s] = v |` vars_tm s.
Proof. by rewrite /vars_sigma/= /codom_vars codom0_set/= !fsetU0. Qed.

Definition simpl_set:= (fsetU0, fset0U, codomf0, cat0f, vars_sigma0, fsetUid, acyclic_sigma0, deref_D, deref_P, ren_P, ren_D, ren_app, deref_empty, vars_sigma_set, unify_refl, cardfs1).

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (Tm_App (Tm_P p) (Tm_D (ID 1))) [::] ;
      mkR (Tm_App (Tm_P p) (Tm_D (ID 2))) [::] ;
      mkR (Tm_App (Tm_P r) (Tm_D (ID 2))) [::] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 1)))
        [:: call (Tm_App (Tm_P p) v_X) ; call (Tm_App (Tm_P r) v_X) ] 
    ].

  Goal exists v, runT unif p_test fset0 empty (TA (call (Tm_App (Tm_P q) (Tm_D (ID 1))))) (Some (s2, None)) false v.
  Proof.
    repeat eexists.
    set X := [fset IV 0; fresh [fset IV 0]].
    apply: StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite deref_App [vars_tm _]/= !simpl_set.
      rewrite in_fnd.
        by rewrite /p_test/= !inE eqxx orbT.
      move=> qs.
      replace (flatten_mode _) with [::output]; last by rewrite/= ffunE !FmapE.fmapE.
      rewrite/= !simpl_set.
      rewrite/fresh_rule /varsU_rule/varsU_rhead/varsU_rprem/= !simpl_set/=.
      rewrite !FmapE.fmapE/= !inE/= in_fnd/=?inE//=.
      rewrite/rename/= !simpl_set/= => H; rewrite !inE/=.
      rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
      by rewrite in_fnd/= ffunE//=.
    by [].
    set Z := (_ `|` _).
    set K := (fresh _).
    apply: StepT => //=.
      rewrite /bc deref_App get_tm_hd_app !simpl_set [get_tm_hd _]/=.
      cbn iota.
      replace (_.[? _]) with (Some build_arr); last by rewrite !FmapE.fmapE.
      rewrite [fresh_rules _ _]/= /fresh_rule !simpl_set.
      rewrite/rename [fresh_tm _ _ _]/= !simpl_set.
      rewrite /= !simpl_set /rename/= !simpl_set !inE /=.
      by rewrite !unify_V_0r//=.
    by [].
    set R := (_ `|` _).
    apply: StepT => //.
      rewrite/step/=.
      rewrite/bc /next_subst [next _ _]/= acyclic_sigma_set_D//.
      rewrite deref_App deref_P get_tm_hd_app/get_tm_hd.
      rewrite 2!FmapE.fmapE/= !simpl_set.
      rewrite /fresh_rule/= !simpl_set.
      rewrite/rename [fresh_tm _ _ _]/= !simpl_set.
      rewrite !inE/= !simpl_set.
      rewrite /=in_fnd/=?inE// => KK.
      rewrite ffunE/= eqxx.
      rewrite unify_ground//.
    by [].
    rewrite !simpl_set fsetUC.
    set T := (_ `|` _).
    apply: BackT => //=.
    apply: StepT => //=.
      rewrite /bc [flatten_term _]/= [get_tm_hd _]/=.
      rewrite/next_subst/= acyclic_sigma_set_D//=.
      rewrite !FmapE.fmapE/= !simpl_set.
      rewrite/= /fresh_rule/= !simpl_set.
      rewrite /rename/= !simpl_set in_fset1/=.
      rewrite eqxx/= unify_ground//.
    by [].
    rewrite !simpl_set/=.
    apply: StopT => //=.
  Qed.
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (Tm_App (Tm_P p) (Tm_D (ID false))) 
        [::call (Tm_App (Tm_P q) v_X); cut] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 1))) [::] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 2))) [::] 
    ].

  Goal exists v, runT unif p_test1 fset0 empty (TA (call (Tm_App (Tm_P p) (Tm_D (ID false))))) (Some (s1, None)) false v.
  Proof.
    repeat eexists.
    apply: StepT => //=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !simpl_set in_fnd; first by rewrite/= !inE eqxx orbT.
      move=> H.
      rewrite[fresh_rules _ _]/= !simpl_set/= !ffunE/= FmapE.fmapE/=.
      rewrite FmapE.fmapE/= !simpl_set/=.
      rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
      rewrite /= !FmapE.fmapE/= !inE/= in_fnd/=?inE// => Hx.
      rewrite ffunE//=.
    by [].
    set X := _ `|` _.
    apply: StepT => //=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE/= not_fnd//= unify_V_0r//=.
      rewrite unify_V_0r//= acyclic_sigma0//=.
    by [].
    apply/StepT => //=.
    apply/StopT => //=.
  Qed.
End Test5.

Section Test6.

  Definition p_test2 : program := build_progr [:: 
      mkR ((Tm_P pred_true)) [::];
      mkR (Tm_App (Tm_P p) (Tm_D (ID false))) 
        [::call (Tm_App (Tm_P q) v_X);call ((Tm_P pred_true)); cut] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 1))) [::] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 2))) [::] 
  ].

  Goal exists r, runT unif p_test2 fset0 empty (TA (call (Tm_App (Tm_P p) (Tm_D (ID false)))) ) (Some (s1, None)) false r.
  Proof.
    repeat eexists.
    apply: StepT => //.
      rewrite/=/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/= !simpl_set.
      rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
      rewrite !FmapE.fmapE/= inE/= in_fnd?inE//= => H.
      by rewrite ffunE//.
    by [].
    set X:= (_ `|` _).
    apply: StepT => //=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      rewrite acyclic_sigma0/= !FmapE.fmapE/= not_fnd//= !unify_V_0r//=.
    by [].
    rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
    set Y := _ `|` _.
    apply/StepT => //=.
      rewrite/next_subst/=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/= !simpl_set.
      rewrite acyclic_sigma_set_D//=.
      by rewrite !FmapE.fmapE.
    by [].
    rewrite !simpl_set.
    apply: StepT => //=.
    apply: StopT => //=.
  Qed.
End Test6.

Definition emptyp := (build_progr [::]).

Definition CutS := TA cut.

Section Test2.
  Goal step unif emptyp fset0 empty (Or (Some OK) empty OK) = (fset0, Success, Or (Some OK) empty OK). by []. Qed.

  Goal runT unif emptyp fset0 empty (Or (Some CutS) empty OK) (Some (empty, None)) false fset0.
    apply: StepT => //=.
    apply: StopT => //.
  Qed.

  Goal forall r, 
    runT unif emptyp fset0 empty (Or (Some CutS) empty r) (Some (empty, None)) false fset0.
    move=> r.
    apply: StepT => //.
    apply: StopT => //=.
  Qed.

  Goal runT unif emptyp fset0 empty (Or (Some OK) empty (Or (Some OK) empty OK)) (Some (empty, (Some (Or None empty (((Or (Some OK) empty OK))))))) false fset0.
  Proof. apply: StopT => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal step unif emptyp fset0 empty (Or (Some (Or None empty (CutS))) empty OK) = (fset0, Expanded, (Or (Some (Or None empty OK)) empty OK)).
  Proof.
    move=>//=.
  Qed.
End Test2.

From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree.

Definition prop := b (d Pred).
Definition build_arr := arr prop prop.

Definition build_progr l := {|
  sig := [fmap].[IP false <- (0, build_arr)].[IP 1 <- (0, build_arr)].[IP 2 <- (0, build_arr)].[IP 200 <- (0, prop)];
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

Definition s1 : Sigma := [fmap].[fresh [fset IV false] <- Tm_D (ID 1)].
Definition s2 : Sigma := [fmap].[fresh [fset IV false] <- Tm_D (ID 2)].

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (Tm_App (Tm_P p) (Tm_D (ID 1))) [::] ;
      mkR (Tm_App (Tm_P p) (Tm_D (ID 2))) [::] ;
      mkR (Tm_App (Tm_P r) (Tm_D (ID 2))) [::] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 1)))
        [:: call (Tm_App (Tm_P p) v_X) ; call (Tm_App (Tm_P r) v_X) ] 
    ].

  (* Goal unify unif v_X (Tm_D (ID 1)) empty = Some s1.
  Proof.
    rewrite/unif.
    rewrite [unifyF]lock/=-lock.
    rewrite/unifyF/= fnd_fmap0.
    move=> //.
  Qed. *)

  Lemma codom0: codom empty = [::].
  Proof. by rewrite /empty codomE/= enum_fset0. Qed.

  Lemma codom_vars0: codom_vars empty = fset0.
  Proof. by rewrite/codom_vars codom0. Qed.

  Lemma codom0_set v s: codom empty.[v <- s] = [::s].
  Proof. by rewrite/= codomE/= fsetU0 enum_fset1/= ffunE//=eqxx. Qed.

  Lemma acyclic_sigma_set_D k t:
    k \notin vars_tm t ->
    acyclic_sigma empty.[k <- t].
  Proof.
    rewrite/acyclic_sigma/=/codom_vars codom0_set/= !fsetU0/=.
    by rewrite/fdisjoint fsetIC fsetI1 => /negPf ->.
  Qed.
  

  Goal exists v, runT unif p_test fset0 empty (TA (call (Tm_App (Tm_P q) (Tm_D (ID 1))))) (Some (s2, None)) false v.
  Proof.
    repeat eexists.
    set X := [fset IV 0; fresh [fset IV 0]].
    apply: StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U/=/fresh_rule/= !codomf0 !fset0U/=!fsetU0 !cat0f.
      rewrite/rename_fresh/=in_fset1 eqxx/=.
      rewrite !fset0U/= !fsetU0/varsU_rule/=/varsU_rhead/=/varsU_rprem/=.
      rewrite /vars_sigma codom_vars0 domf0 /= !fset0U.
      rewrite !ren_app !ren_P ren_V/=.
      rewrite in_fnd//= ?in_fset1//= => H.
      rewrite ffunE/=/vars_atoms/= !fsetU0 !fset0U/= fsetUid.
      rewrite (fsetUC _ [fset fresh _]) fsetUA fsetUid.
      rewrite fsetUC -/X//.
      rewrite acyclic_sigma0//.
    move=> //.
    apply: StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      replace _.[? _] with (Some (0, build_arr)); last first.
        by rewrite !FmapE.fmapE eqxx/=.
      rewrite/=.
      rewrite !fset0U/=/fresh_rule/= !codomf0 !fset0U/=!fsetU0 !cat0f.
      rewrite/rename_fresh/=in_fset1 eqxx/=.
      rewrite acyclic_sigma0//.
      by rewrite not_fnd//= not_fnd//=.
      by [].
    rewrite !fsetU0 !fset0U/=.
    rewrite !fsetUA !fsetU0 /codom_vars !codom0_set/=.
    rewrite !fsetU0 -!(fsetUC [fset fresh _]).
    rewrite !fsetUA !fsetUid.
    rewrite -!(fsetUC [fset IV 0]) !fsetUA !fsetUid.
    rewrite-/X.
    set Y:= (_ `|` _).
    apply: StepT => //=.
      rewrite /bc [get_tm_hd _]/=.
      cbn iota.
      replace _.[? _] with (Some (0, build_arr)); last first.
        by rewrite !FmapE.fmapE eqxx/=.
      rewrite/=.
      rewrite FmapE.fmapE.
      rewrite !fset0U/=/fresh_rule/= !codomf0 !fset0U/=!fsetU0 !cat0f.
      rewrite/rename_fresh/=in_fset1 eqxx/=.
      rewrite not_fnd//= eqxx/=.
      rewrite !fset0U fsetU0.
      (* rewrite !(fsetUC _ [fset IV 0]) !fsetUA !fsetUid.
      rewrite -!(fsetUC [fset fresh [fset IV 0]]) !fsetUA.
      rewrite (fsetUC _ [fset IV 0]) -/X.
      rewrite (fsetUC X) -fsetUA -/Y. *)
      rewrite /next_subst/= acyclic_sigma_set_D//=.
      by [].
    set Z := (_ `|` _).
    apply: BackT => //=.
    apply: StepT => //=.
      rewrite /bc [get_tm_hd _]/=.
      cbn iota.
      replace _.[? _] with (Some (0, build_arr)); last first.
        by rewrite !FmapE.fmapE eqxx/=.
      rewrite/=.
      rewrite FmapE.fmapE.
      rewrite !fset0U/=/fresh_rule/= !codomf0 !fset0U/=!fsetU0 !cat0f.
      rewrite/rename_fresh/=in_fset1 eqxx/=.
      rewrite not_fnd//= eqxx/=.
      rewrite !fset0U !fsetU0.
      rewrite/next_subst/= acyclic_sigma_set_D//.
      (* rewrite /next_subst/=/varsU_rule/varsU_rhead/=/varsU_rprem/=.
      rewrite /vars_sigma/= /codom_vars codom0_set/= !fsetU0/=. *)
      by [].
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
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U/= !fsetU0 /varsU_rule /varsU_rhead /varsU_rprem/= !fsetU0 !fset0U.
      rewrite codomf0 cat0f fsetU0 ren_app ren_P ren_V/= in_fnd/= ?in_fset1// => H.
      rewrite/vars_atoms/= !fsetUA codom_vars0 !fsetU0 ffunE/= fsetUC fsetUA fsetUid.
      rewrite fsetUC//.
      by rewrite acyclic_sigma0.
      move=> //.
    apply: StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U/= not_fnd//= not_fnd//=.
      by rewrite acyclic_sigma0.
      by [].
    rewrite codomf0 /varsU_rule /varsU_rhead /varsU_rprem/= !fsetU0.
    rewrite /vars_sigma/codom_vars !codom0_set/= !fsetU0 fsetUid !fsetUA.
    rewrite -!(fsetUC [fset fresh _]) fsetUA !fsetUid !fsetUA.
    rewrite -!(fsetUC [fset IV 0]) !fsetUA fsetUid.
    set X := (_ `|` _).
    apply/StepT => //=.
    apply/StopT => //=.
  Qed.
End Test5.

Section Test6.

  Definition pred_true := ((IP 200)).

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
      rewrite/=/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U/= !fsetU0 /varsU_rule /varsU_rhead /varsU_rprem/= !fsetU0 !fset0U.
      rewrite codomf0 cat0f fsetU0 ren_app ren_P ren_V/= in_fnd/= ?in_fset1// => H.
      rewrite/vars_atoms/= !fsetUA codom_vars0 !fsetU0 ffunE/= fsetUC fsetUA fsetUid.
      rewrite fsetUC//.
      by rewrite acyclic_sigma0.
      move=> //.
    apply: StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U/= not_fnd//= not_fnd//=.
      by rewrite acyclic_sigma0.
      by [].
    rewrite codomf0 /varsU_rule /varsU_rhead /varsU_rprem/= !fsetU0.
    rewrite /vars_sigma/codom_vars !codom0_set/= !fsetU0 fsetUid !fsetUA.
    rewrite -!(fsetUC [fset fresh _]) fsetUA !fsetUid !fsetUA.
    rewrite -!(fsetUC [fset IV 0]) !fsetUA fsetUid.
    set X := (_ `|` _).
    apply/StepT => //=.
      rewrite/bc [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/=.
      rewrite !fset0U//=.
      by rewrite /next_subst/= acyclic_sigma_set_D//.
      by [].
    apply: StepT => //=.
    apply: StopT => //.
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

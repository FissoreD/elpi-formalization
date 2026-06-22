From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree unif fresh.

Definition prop := b (d Pred).
Definition func := b (d Func).
Definition exp := b Exp.
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
                      head := Tm_App (Tm_P p) (Tm_D (ID 0));
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
                      head := Tm_App (Tm_P p) (Tm_D (ID 0));
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

  Goal exists v, runT unif p_test fset0 empty (TA (call (Tm_App (Tm_P q) (Tm_D (ID 1))))) (One s2) false v.
  Proof.
    repeat eexists.
    set X := [fset IV 0; fresh [fset IV 0]].
    apply: StepT' => //=; cycle 1.
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
    rewrite !simpl_set/=.
    apply: StopOT => //=.
    by [].
  Qed.
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (Tm_App (Tm_P p) (Tm_D (ID false))) 
        [::call (Tm_App (Tm_P q) v_X); cut] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 1))) [::] ;
      mkR (Tm_App (Tm_P q) (Tm_D (ID 2))) [::] 
    ].

  Goal exists v, runT unif p_test1 fset0 empty (TA (call (Tm_App (Tm_P p) (Tm_D (ID false))))) (One s1) false v.
  Proof.
    repeat eexists.
    apply: StepT' => //=; cycle 1.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !simpl_set in_fnd; first by rewrite/= !inE eqxx orbT.
      move=> H.
      rewrite[fresh_rules _ _]/= !simpl_set/= !ffunE/= FmapE.fmapE/=.
      rewrite FmapE.fmapE/= !simpl_set/=.
      rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
      rewrite /= !FmapE.fmapE/= !inE/= in_fnd/=?inE// => Hx.
      rewrite ffunE//=.
    set X := _ `|` _.
    apply: StepT => //=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE/= not_fnd//= unify_V_0r//=.
      rewrite unify_V_0r//= acyclic_sigma0//=.
    apply/StepT => //=.
    apply/StopOT => //=.
    by [].
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

  Goal exists r, runT unif p_test2 fset0 empty (TA (call (Tm_App (Tm_P p) (Tm_D (ID false)))) ) (One s1) false r.
  Proof.
    repeat eexists.
    apply: StepT' => //; cycle 1.
      rewrite/=/bc [flatten_term _]/= [get_tm_hd _]/=.
      cbn iota.
      rewrite !FmapE.fmapE eqxx/= !simpl_set.
      rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
      rewrite !FmapE.fmapE/= inE/= in_fnd?inE//= => H.
      by rewrite ffunE//.
    set X:= (_ `|` _).
    apply: StepT => //=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/=.
      rewrite acyclic_sigma0/= !FmapE.fmapE/= not_fnd//= !unify_V_0r//=.
    rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
    set Y := _ `|` _.
    apply/StepT => //=.
      rewrite/next_subst/=.
      rewrite/bc [flatten_term _]/= [get_tm_hd _]/= !simpl_set.
      rewrite acyclic_sigma_set_D//=.
      by rewrite !FmapE.fmapE.
    rewrite !simpl_set.
    apply: StepT => //=.
    apply: StopOT => //=.
    by [].
  Qed.
End Test6.

Definition emptyp := (build_progr [::]).

Definition CutS := TA cut.

Section Test2.
  Goal step unif emptyp fset0 empty (Or (Some OK) empty OK) = (fset0, Success, Or (Some OK) empty OK). by []. Qed.

  Goal runT unif emptyp fset0 empty (Or (Some CutS) empty OK) (One empty) false fset0.
    apply: StepT' => //=; cycle 1.
    apply: StopOT => //.
    by [].
  Qed.

  Goal forall r, 
    runT unif emptyp fset0 empty (Or (Some CutS) empty r) (One empty) false fset0.
    move=> r.
    apply: StepT' => //; cycle 1.
    apply: StopOT => //=.
    by [].
  Qed.

  Goal runT unif emptyp fset0 empty (Or (Some OK) empty (Or (Some OK) empty OK)) (Many empty (Or None empty (Or (Some OK) empty OK))) false fset0.
  Proof. apply: StopMT => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal step unif emptyp fset0 empty (Or (Some (Or None empty (CutS))) empty OK) = (fset0, Expanded, (Or (Some (Or None empty OK)) empty OK)).
  Proof.
    move=>//=.
  Qed.
End Test2.

Section map.
  Definition map := IP 0.
  Definition cons := ID 0.
  Definition nil := ID 1.
  Definition one := ID 2.
  Definition two := ID 3.
  Definition four := ID 5.
  Definition double := IP 4.

  Coercion Tm_P : P >-> Tm. 
  Coercion Tm_D : D >-> Tm. 
  Coercion Tm_V : V >-> Tm. 

  Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
  Definition consS := arr output exp exp.
  Definition nilS := exp.
  Definition oneS := exp.
  Definition twoS := exp.
  Definition fourS := exp.
  Definition doubleS := arr input exp func.

  Definition X := IV 1.
  Definition X' := IV 10.
  Definition Y := IV 2.
  Definition Y' := IV 20.
  Definition F := IV 3.


  Definition p' := {|
    sig := [fmap].[map <- mapS].[double <- doubleS];
    rules := 
      mkR (Tm_App (Tm_App (Tm_App map F) nil) nil) [::] ::
      mkR (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons X) Y)) (Tm_App (Tm_App cons X') Y') ) 
        [:: call (Tm_App (Tm_App F X) X'); call (Tm_App (Tm_App map Y) Y')] ::
      mkR (Tm_App (Tm_App double one) two) [::]
      :: [::]
  |}.

  Definition list12 := Tm_App (Tm_App cons one) nil.
  Definition list24 := Tm_App (Tm_App cons two) nil.

  Definition map12d := Tm_App (Tm_App (Tm_App map double) list12) X.

  Goal exists f s, runT u p' fset0 fmap0 (TA (call map12d)) (One s) false f /\ deref s X = list24.
  Proof.
    do 2 eexists.
    split.
      apply: StepT'=> //=; cycle 1.
      rewrite/bc ifF ?acyclic_sigma0//.
      rewrite !FmapE.fmapE.
      set s0 := (_ `|` _).
      rewrite not_fnd//.
      case X : fresh_rules => [f rs]/=.
      rewrite not_fnd//=.
      case: rs X => [|r0 rs]; first by rewrite /=push.

      (* matching r0 *)
      rewrite[select _ _ _ _ _]/= !fset0U => H.
      rewrite ifF; last by move: H; rewrite/= !push//= => -[?<-?].
      case ft: flatten_term => [|hd args].
        by move: H ft; rewrite/= !push//= => -[?<-?]//.
      rewrite {2}/matching/montanari_deref/montanari_pair montanari_equation/=.
      rewrite deref_empty ifF; last first.
        move: H ft; rewrite/= !push//= => -[?<-?]//=.
        rewrite !FmapE.fmapE/= !inE/= => -[<-?]; subst.
        by rewrite in_fnd ?inE//=.
      have: hd = fresh
        (F |` (fresh_rule s0
        {| head := Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons X) Y)) (Tm_App (Tm_App cons X') Y');
           premises := [:: call (Tm_App (Tm_App F X) X'); call (Tm_App (Tm_App map Y) Y')] |}).1).
        move: H ft; rewrite/= !push/= => -[???]; subst => /=-[<-]/=?; subst.
        rewrite !FmapE.fmapE/= inE/= in_fnd?inE//= => ?; rewrite ffunE/=.
        rewrite !simpl_set//=.
      move=> ?; subst => /=.
      rewrite montanari_equation/=.
      case: args ft => [|a0 an] ft.
        exfalso; move: H ft; rewrite/=!push/= => -[???]; subst.
        by rewrite !FmapE.fmapE/= inE/= => -[??]; subst => //=.
      rewrite {1}/matching/montanari_deref/montanari_pair.
      rewrite !deref_App/=.
      have ?: a0 = nil; subst.
        move: H ft; rewrite/=!push/= => -[???]; subst.
        by rewrite !FmapE.fmapE/= inE/= => -[??]; subst => //=.
      rewrite /= montanari_equation/=.

      (* matchin r1 *)
      case: rs H => [|r1 rs] H/=.
        exfalso; by move:H; rewrite/=!push => -[???]; subst => //.
      rewrite/= ifF; last first.
        move: H ft; rewrite /= !push => -[????]; subst => //=.
        rewrite !FmapE.fmapE inE/= => -[+?]//=; subst => /= H.
        by rewrite head_fresh_rule/= /rename push/=.
      rewrite !simpl_set.
      case ft1: flatten_term => [|hd args].
        exfalso; clear ft.
        move: H ft1; rewrite/= !push//= => -[????]//; subst.
        by rewrite head_fresh_rule/= /rename push ren_app//.
      rewrite {2}/matching/montanari_deref/montanari_pair montanari_equation/=.
      rewrite deref_empty.
      set X := fresh_tm (F |` [fset X; Y] `|` [fset X'; Y'] `|` s0) [fmap]
        (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons X) Y)) (Tm_App (Tm_App cons X') Y')).
      have FX : F \in (X.2) by rewrite/X (fsubsetP (fresh_tm_sub1 _ _ _) _ _)//= !inE.
      have XX : map.X \in (X.2) by rewrite/X (fsubsetP (fresh_tm_sub1 _ _ _) _ _)//= !inE.
      have YX : Y \in (X.2) by rewrite/X (fsubsetP (fresh_tm_sub1 _ _ _) _ _)//= !inE.
      have Y'X : Y' \in (X.2) by rewrite/X (fsubsetP (fresh_tm_sub1 _ _ _) _ _)//= !inE.
      have X'X : X' \in (X.2) by rewrite/X (fsubsetP (fresh_tm_sub1 _ _ _) _ _)//= !inE.
      have [??] : Tm_V (X.2 [` FX]) = hd /\ [:: Tm_App (Tm_App cons (X.2 [` XX])) (X.2 [` YX]);
        Tm_App (Tm_App cons (X.2 [` X'X])) (X.2 [` Y'X])] = args; subst.
        move: H ft1 {ft}; rewrite/= !push//= => -[????]//; subst.
        rewrite !simpl_set head_fresh_rule/=.
        rewrite /rename [vars _]/= !simpl_set.
        rewrite-/X.
        rewrite !push/= => -[<-<-].
        by rewrite !in_fnd/=.
      rewrite /=deref_sigma0.
      rewrite montanari_equation/=.
      rewrite/matching/montanari_deref/montanari_pair.
      rewrite montanari_equation/=.
      rewrite !simpl_set/= ifF; last first.
        apply/eqP => -[].
        rewrite not_fnd//=.
        rewrite !inE; apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ [`XX] [`FX] Hx).
      rewrite montanari_equation/=.
      rewrite ifF; last first.
        apply/eqP => -[].
        rewrite not_fnd//=.
        rewrite !inE; apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ [`XX] [`FX] Hx).
      rewrite montanari_equation//=.
      rewrite montanari_equation//=.
      rewrite ifF;last first.
        apply/eqP => -[].
        rewrite not_fnd//=.
        rewrite !inE; apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ [`XX] [`FX] Hx).
      rewrite not_fnd; last first.
        rewrite !inE; apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ [`XX] [`FX] Hx).
      rewrite/=montanari_equation/=.
      rewrite ifF/=; last first.
        apply/eqP => -[].
        rewrite/derefkv/=.
        rewrite not_fnd//=.
          rewrite not_fnd//=.
          rewrite !inE//= orbF;apply/eqP => Hx.
          have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
          rewrite-/X.
          by move=> /injectiveP /(_ _ _ Hx).
        rewrite !inE;apply/eqP => Hx.
          have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
          rewrite-/X.
          by move=> /injectiveP /(_ _ _ Hx).
      rewrite not_fnd/=; last first.
        rewrite !inE;apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ _ _ Hx).
      rewrite/derefkv/=.
      rewrite not_fnd/=; last first.
        rewrite !inE orbF; apply/eqP => Hx.
        have:= fresh_tm_inj (F |` [fset map.X; Y] `|` [fset X'; Y'] `|` s0) (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons map.X) Y)) (Tm_App (Tm_App cons X') Y')) injectiveb0.
        rewrite-/X.
        by move=> /injectiveP /(_ _ _ Hx).
      rewrite montanari_equation/=.

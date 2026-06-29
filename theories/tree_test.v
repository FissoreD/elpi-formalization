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
        [:: call (Tm_App (Tm_App F X) X'); call (Tm_App (Tm_App (Tm_App map F) Y) Y')] ::
      mkR (Tm_App (Tm_App double one) two) [::]
      :: [::]
  |}.

  Definition list12 := Tm_App (Tm_App cons one) nil.
  Definition list24 := Tm_App (Tm_App cons two) nil.

  Definition map12d := Tm_App (Tm_App (Tm_App map double) list12) X.

  Lemma get_frozen_vars_ground m T:
    all ground T -> get_frozen_vars m T = fset0.
  Proof.
    elim: m T => //[x xs IH] []//= X XS /andP[G1 G2].
    by rewrite IH// ground_vars_tm// fset0U if_same.
  Qed.

  Lemma p'map: (sig p').[? map] = Some mapS.
  Proof. by rewrite !FmapE.fmapE. Qed.

  Lemma fresh_rules_cons s r0 rs:
    fresh_rules s (r0 :: rs) =
    ((fresh_rule (fresh_rules s rs).1 r0).1,
      (fresh_rule (fresh_rules s rs).1 r0).2 :: (fresh_rules s rs).2).
  Proof. by rewrite/=!push//. Qed.

  Lemma fstS T1 T2 (a:T1) (b:T2): (a,b).1 = a. by []. Qed.
  Lemma sndS T1 T2 (a:T1) (b:T2): (a,b).2 = b. by []. Qed.

  Lemma select_cons m ft md x xs s: select u m ft md (x::xs) s = 
    (if inl m != get_tm_hd (head x)
      then select u m ft md xs s
      else
      match H u (get_frozen_vars md ft) md ft (flatten_term (head x)) s with
      | Some sigma1 =>
      let
      '(fv, rs) := select u m ft md xs s in
      (vars_sigma sigma1 `|` varsU_rule x `|` fv, (sigma1, premises x) :: rs)
      | None => select u m ft md xs s
      end).
  Proof. by []. Qed.

  Lemma select_consF m ft md x xs s:
    inl m = get_tm_hd (head x) ->
    select u m ft md (x::xs) s = 
    match H u (get_frozen_vars md ft) md ft (flatten_term (head x)) s with
    | Some sigma1 =>
      let '(fv, rs) := select u m ft md xs s in
      (vars_sigma sigma1 `|` varsU_rule x `|` fv, (sigma1, premises x) :: rs)
    | None => select u m ft md xs s
    end.
  Proof. by move=> /=->; rewrite eqxx. Qed.


  Lemma inl_map_get_tm_hdmap:
    inl map == get_tm_hd map.
  Proof. by []. Qed.

  Lemma ifTS T (a b:T) : (if true then a else b) = a. by []. Qed.
  Lemma ifFS T (a b:T) : (if false then a else b) = b. by []. Qed.
  Lemma fmapIn e (S: {fset V}) (f: V) (H : e \in S):
    [ffun x : S => f].[? e] = Some f.
  Proof. by rewrite in_fnd/= ffunE/=. Qed.

  Lemma fresh_tm_app s m f a: fresh_tm s m (Tm_App f a) = 
    ((fresh_tm (fresh_tm s m f).1 (fresh_tm s m f).2 a)).
  Proof. by rewrite/=!push -surjective_pairing. Qed.

  Lemma fresh_tm_P s r p: fresh_tm s r (Tm_P p) = (s, r). by []. Qed.
  Lemma fresh_tm_D s r p: fresh_tm s r (Tm_D p) = (s, r). by []. Qed.
  Lemma getfmap12d: (get_frozen_vars [:: input;  input;  output] (flatten_term map12d)) = fset0.
  Proof. by rewrite/= !simpl_set. Qed.

    (* Print fresh_tm. *)

  Goal exists f s, runT u p' fset0 fmap0 (TA (call map12d)) (One s) false f /\ deref s X = list24.
  Proof.
    do 2 eexists.
    split.
      apply: StepT'=> //=; cycle 1.
      rewrite/bc ifF ?acyclic_sigma0//.
      rewrite p'map.
      set s0 := (_ `|` _).
      rewrite !fresh_rules_cons !fstS !sndS.
      rewrite !simpl_set.
      set F0 := (_ `|` _).
      set F1 := (_ `|` _).
      set F2 := (_ `|` _).
      rewrite select_consF// [head _]/=.
      rewrite [flatten_term (Tm_App _ _)]/= [flatten_mode _]/=.
      rewrite fmapIn; last by rewrite !inE.
      rewrite [odflt _ _]/=.
      replace (H _ _ _ _ _ _) with (@None Sigma); last first.
        rewrite/= !simpl_set /matching/montanari_deref deref_empty/=.
        rewrite{2}/montanari_pair montanari_equation/=.
        rewrite montanari_equation/=/montanari_pair.
        by rewrite montanari_equation/=.
      rewrite select_consF//head_fresh_rule [head _]/= /rename (push (fresh_tm _ _ _)) sndS; last by [].
      set F3 := (_ `|` _).

      rewrite/fresh_tm !simpl_set.
      rewrite !inE.
      set F4 := _ `|` _.
      set F5 := _ `|` _.
      set F6 := _ `|` _.
  Abort.
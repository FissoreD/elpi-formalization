From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang tree unif fresh.

Definition prop := b (d Pred).
Definition func := b (d Func).
Definition exp := b Exp.
Definition build_arr := arr output prop prop.

Notation r := (IP 2).
Notation p := (IP 1).
Notation q := (IP 0).
Notation fail := (IP 3).
Notation true := (IP 4).

Notation tt := (IP 100).
Notation ff := (IP 101).

Definition build_progr l := {|
  sig := [fmap].[p <- build_arr].[q <- build_arr].[r <- build_arr].[true <- prop];
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


Definition v0 := Tm_V (IV 0).

Notation app x y := (Tm_App x y).

Coercion Tm_P : P >-> Tm.

Definition s1 : Sigma := [fmap].[fresh [fset IV 0] <- Tm_P tt].
Definition s2 : Sigma := [fmap].[fresh [fset IV 0] <- Tm_P ff].

Lemma vars_sigma_set v s: vars_sigma empty.[v <- s] = v |` vars_tm s.
Proof. by rewrite /vars_sigma/= /codom_vars codom0_set/= !fsetU0. Qed.

Definition simpl_set:= (fsetU0, fset0U, codomf0, cat0f, vars_sigma0, fsetUid, acyclic_sigma0, deref_P, ren_P, ren_app, deref_empty, vars_sigma_set, unify_refl, cardfs1).

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (app p tt) [::] ;
      mkR (app p ff) [::] ;
      mkR (app r ff) [::] ;
      mkR (app q tt) [:: call (app p v0) ; call (app r v0) ] 
    ].

  Goal exists v, runT unif p_test fset0 empty (TA (call (app q tt))) (One s2) false v.
  Proof.
    repeat eexists.
    set X := [fset IV 0; fresh [fset IV 0]].
    apply: StepT' => //=; cycle 1.
      rewrite/bc.
      rewrite deref_App [vars_tm _]/= !simpl_set.
      rewrite/= !simpl_set.
      rewrite/fresh_rule /varsU_rule/varsU_rhead/varsU_rprem/=.
      rewrite !simpl_set FmapE.fmapE/= !inE/=.
      rewrite/rename/= !inE/= !FmapE.fmapE/=.
      rewrite in_fnd?inE//= => H.
      by rewrite ffunE unify_refl/= !simpl_set//.
    set Z := (_ `|` _).
    set K := (fresh _).
    apply: StepT => //=.
      rewrite/bc deref_App !simpl_set.
      rewrite [fresh_rules _ _]/= /fresh_rule !simpl_set.
      rewrite/rename [fresh_tm _ _ _]/= !simpl_set.
      rewrite /= !simpl_set /rename/= !simpl_set !inE /=.
      rewrite !FmapE.fmapE/=.
      by rewrite !unify_V_0r.
    set R := (_ `|` _).
    apply: StepT => //.
      rewrite/step/=.
      rewrite/bc /next_subst [next _ _]/= acyclic_sigma_set_D//.
      rewrite deref_App deref_P /get_tm_hd.
      rewrite/= !simpl_set.
      rewrite /fresh_rule/= !simpl_set.
      rewrite/rename [fresh_tm _ _ _]/= !simpl_set.
      rewrite !inE/= !simpl_set !FmapE.fmapE/=.
      rewrite in_fnd/=?inE// => JK.
      rewrite ffunE/= eqxx.
      rewrite unify_ground//=.
    rewrite !simpl_set fsetUC.
    set T := (_ `|` _).
    apply: BackT => //=.
    apply: StepT => //=.
      rewrite /bc.
      rewrite/next_subst/= acyclic_sigma_set_D//=.
      rewrite !FmapE.fmapE/= !simpl_set.
      rewrite/= /fresh_rule/= !simpl_set.
      rewrite /rename/= !simpl_set in_fset1/=.
      rewrite !FmapE.fmapE/= not_fnd//=.
      rewrite eqxx/= unify_ground//.
    rewrite !simpl_set/=.
    apply: StopOT => //=.
    by [].
  Qed.
End Test1.

Section Test5.

  Definition p_test1 : program := build_progr [:: 
      mkR (app p ff) [::call (app q v0); cut] ;
      mkR (app q tt) [::] ;
      mkR (app q ff) [::] 
    ].

  Goal exists v, runT unif p_test1 fset0 empty (TA (call (app p ff))) (One s1) false v.
  Proof.
    repeat eexists.
    apply: StepT' => //=; cycle 1.
      rewrite/bc.
      rewrite !simpl_set.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/=.
      rewrite !inE/=.
      by rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
    set X := _ `|` _.
    apply: StepT => //=.
      rewrite/bc/=.
      rewrite !FmapE.fmapE/= in_fnd//=?inE//= => H.
      rewrite ffunE/= not_fnd//= unify_V_0r//=.
      rewrite unify_V_0r//= acyclic_sigma0//=.
    apply/StepT => //=.
    apply/StopOT => //=.
    by [].
  Qed.
End Test5.

Section Test6.

  Definition p_test2 : program := build_progr [:: 
      mkR true [::];
      mkR (app p tt) [::call (app q v0); call true; cut] ;
      mkR (app q tt) [::] ;
      mkR (app q ff) [::] 
  ].

  Goal exists r, runT unif p_test2 fset0 empty (TA (call (app p tt)) ) (One s1) false r.
  Proof.
    repeat eexists.
    apply: StepT' => //; cycle 1.
      rewrite/=/bc/=.
      rewrite !FmapE.fmapE not_fnd//= !simpl_set/=.
      rewrite in_fnd//=?inE// => H; rewrite !inE/= ffunE//=.
    set X:= (_ `|` _).
    apply: StepT => //=.
      rewrite/bc/=.
      by rewrite acyclic_sigma0/= !FmapE.fmapE/= not_fnd//= !unify_V_0r//=.
    rewrite /varsU_rule/varsU_rhead/varsU_rprem/=/vars_atoms/= !simpl_set/=.
    set Y := _ `|` _.
    apply/StepT => //=.
      rewrite/next_subst/=.
      rewrite/bc /=!simpl_set/=.
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
  Definition cons := IP 501.
  Definition nil := IP 502.
  Definition one := IP 503.
  Definition two := IP 504.
  Definition four := IP 505.
  Definition map := IP 600.
  Definition double := IP 601.

  Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
  Definition consS := arr output exp exp.
  Definition nilS := exp.
  Definition oneS := exp.
  Definition twoS := exp.
  Definition fourS := exp.
  Definition doubleS := arr input exp func.

  Definition X := IV 300.
  Definition X' := IV 301.
  Definition Y := IV 400.
  Definition Y' := IV 401.
  Definition F := IV 500.

  Coercion Tm_V : V >-> Tm.

  Definition p' := {|
    sig := [fmap].[map <- mapS].[double <- doubleS];
    rules := 
      mkR (app (app (app map F) nil) nil) [::] ::
      mkR (app (app (app map F) (app (app cons X) Y)) (app (app cons X') Y') ) 
        [:: call (app (app F X) X'); call (app (app (app map F) Y) Y')] ::
      mkR (app (app double one) two) [::]
      :: [::]
  |}.

  Definition list12 := app (app cons one) nil.
  Definition list24 := app (app cons two) nil.

  Definition map12d := app (app (app map double) list12) X.

  (* Lemma get_input_vars_ground m T:
    all ground T -> get_input_vars m T = fset0.
  Proof.
    elim: m T => //[x xs IH] []//= X XS /andP[G1 G2].
    by rewrite IH// ground_vars_tm// fset0U if_same.
  Qed. *)

  Lemma p'map: (sig p').[? map] = Some mapS.
  Proof. by rewrite !FmapE.fmapE. Qed.

  Lemma fresh_rules_cons s r0 rs:
    fresh_rules s (r0 :: rs) =
    ((fresh_rule (fresh_rules s rs).1 r0).1,
      (fresh_rule (fresh_rules s rs).1 r0).2 :: (fresh_rules s rs).2).
  Proof. by rewrite/=!push//. Qed.

  Lemma fstS T1 T2 (a:T1) (b:T2): (a,b).1 = a. by []. Qed.
  Lemma sndS T1 T2 (a:T1) (b:T2): (a,b).2 = b. by []. Qed.

  (* Lemma select_cons m ft md x xs s: select u m ft md (x::xs) s = 
    (if inl m != get_tm_hd (head x)
      then select u m ft md xs s
      else
      match H u (get_input_vars md ft) md ft (flatten_term (head x)) s with
      | Some sigma1 =>
      let
      '(fv, rs) := select u m ft md xs s in
      (vars_sigma sigma1 `|` varsU_rule x `|` fv, (sigma1, premises x) :: rs)
      | None => select u m ft md xs s
      end).
  Proof. by []. Qed. *)

  Lemma select_consF sP ft x xs s:
    (* inl m = get_tm_hd (head x) -> *)
    select u sP ft (x::xs) s = 
    match H u sP (get_input_vars sP ft).1 ft (head x) s with
    | Some (_, sigma1) =>
      let '(fv, rs) := select u sP ft xs s in
      (vars_sigma sigma1 `|` varsU_rule x `|` fv, ((sigma1, premises x) :: rs))
    | None => select u sP ft xs s
    end.
  Proof. by rewrite//=. Qed.

  Lemma inl_map_get_tm_hdmap:
    inl map == get_tm_hd map.
  Proof. by []. Qed.

  (* Lemma ifTS T (a b:T) : (if true then a else b) = a. by []. Qed.
  Lemma ifFS T (a b:T) : (if false then a else b) = b. by []. Qed. *)
  Lemma fmapIn e (S: {fset V}) (f: V) (H : e \in S):
    [ffun x : S => f].[? e] = Some f.
  Proof. by rewrite in_fnd/= ffunE/=. Qed.

  Lemma fresh_tm_app s m f a: fresh_tm s m (app f a) = 
    ((fresh_tm (fresh_tm s m f).1 (fresh_tm s m f).2 a)).
  Proof. by rewrite/=!push -surjective_pairing. Qed.

  Lemma fresh_tm_P s r p: fresh_tm s r (Tm_P p) = (s, r). by []. Qed.
  (* Lemma getfmap12d: (get_input_vars [:: input;  input;  output] (flatten_term map12d)) = fset0.
  Proof. by rewrite/= !simpl_set. Qed. *)

    (* Print fresh_tm. *)

  Lemma get_input_vars_map12d:
    (get_input_vars p' map12d).1 = fset0.
  Proof.
    rewrite/map12d/= !FmapE.fmapE not_fnd// !simpl_set.
    by rewrite !eqxx/= !fsetU0.
  Qed.

  Lemma rename_app fv f a v:
    (rename fv (Tm_App f a) v).2 = 
    app
      (ren
      (fresh_tm (fresh_tm (vars f `|` vars a `|` fv) v f).1
      (fresh_tm (vars f `|` vars a `|` fv) v f).2 a).2 f)
      (ren
      (fresh_tm (fresh_tm (vars f `|` vars a `|` fv) v f).1
      (fresh_tm (vars f `|` vars a `|` fv) v f).2 a).2 a).
  Proof. by rewrite/rename/= !push/=. Qed.

  Goal exists f s, runT u p' fset0 fmap0 (TA (call map12d)) (One s) false f /\ deref s X = list24.
  Proof.
    do 2 eexists.
    split.
      apply: StepT'=> //=; cycle 1.
      rewrite/bc ifF ?acyclic_sigma0//.
      rewrite !simpl_set.
      rewrite !fresh_rules_cons !fstS !sndS.
      rewrite !simpl_set.
      set F0 := (_ `|` _).
      set F1 := (_ `|` _).
      set F2 := (_ `|` _).
      rewrite select_consF// [head _]/=.
      rewrite get_input_vars_map12d fmapIn?inE//.
      case H: H => //.
        exfalso; move: H; rewrite/map12d/H eqxx !FmapE.fmapE.
        rewrite eqxx [omap _ _]/= /mapS [omap _ _]/=.
        case M: matching => //.
        rewrite [omap _ _]/=.
        cbn match.
        rewrite eqxx [omap _ _]/=.
        rewrite/matching/montanari_deref/montanari_pair.
        rewrite !ground_deref//; last first.
          by rewrite/list12/ground/= !simpl_set.
        by rewrite montanari_equation/=.
      rewrite {H} select_consF.
      rewrite head_fresh_rule [head _]/=.
      rewrite get_input_vars_map12d/map12d premises_fresh_rule [head _]/=.
      rewrite [vars _]/= !simpl_set [premises _]/=.
      set F3 := (_ `|` _).
      rewrite !rename_app !ren_app !ren_P.
      rewrite [vars _]/= !simpl_set [vars _]/= !simpl_set.
      set FT := (fresh_tm _ _ _).2.
      rewrite/H eqxx !FmapE.fmapE eqxx [omap _ _]/= /mapS eqxx.
      rewrite/u [lang.matching _]/=.
      rewrite/matching/montanari_deref/montanari_pair.
      rewrite !deref_empty montanari_equation [omap _ _]/=.
      rewrite montanari_equation [omap _ _]/=.
      cbn match; rewrite eqxx.
      rewrite in_fnd.
        apply/fsubsetP.
          apply: fresh_tm_domf_sub.
        apply/fsubsetP.
          apply: fresh_tm_sub1.
        by rewrite/= !inE eqxx.
      move=> iFT; rewrite !deref_App !odflt_Some !deref_P.
      rewrite deref_sigma0 not_in_deref; last first.
        rewrite/= fsetU0 fdisjointX1 inE.
        admit.
      rewrite not_in_deref; last first.
        admit.
      rewrite 3!montanari_equation.
      case: eqP => [H|_].
        by exfalso; move: H; rewrite/ren; case: fndP => //.
      case: eqP => [H|_].
        by exfalso; move: H; rewrite/ren; case: fndP => //.
      rewrite montanari_equation eqxx montanari_equation.
      case: eqP => [H|_].
        by exfalso; move: H; rewrite/ren; case: fndP => //.
  Abort.
End map.
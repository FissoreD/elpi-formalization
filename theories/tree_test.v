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

Definition unif : Unif := mk_Unif unify matching.


Definition v0 := Tm_V (IV 0).

Notation app x y := (Tm_App x y).

Coercion Tm_P : P >-> Tm.

Definition s1 : Sigma := [fmap].[IV 1 <- Tm_P tt].
Definition s2 : Sigma := [fmap].[IV 1 <- Tm_P ff].

Lemma vars_sigma_set v s: vars_sigma fmap0.[v <- s] = v |` vars_tm s.
Proof. by rewrite /vars_sigma/= /codom_vars codom0_set/= !fsetU0. Qed.

Definition simpl_set:= (fsetU0, fset0U, codomf0, cat0f, vars_sigma0, fsetUid, acyclic_sigma0, deref_P, ren_P, ren_app, deref_empty, vars_sigma_set, unify_refl, cardfs1, freshUU, freshP0, freshP1).

Ltac sif := simpl (if _ then _ else _); cbn match.

Section Test1.

  Definition p_test : program := build_progr [:: 
      mkR (app p tt) [::] ;
      mkR (app p ff) [::] ;
      mkR (app r ff) [::] ;
      mkR (app q tt) [:: call (app p v0) ; call (app r v0) ] 
    ].

  Goal exists v, runT unif p_test 0 fmap0 (Unexplored (call (app q tt))) (One s2) false v.
  Proof.
    repeat eexists.
    have PV : v_prog (rules p_test) = [fset IV 0].
      by rewrite/v_prog/=/varsU_rule/varsU_rhead/varsU_rprem/vars_atoms/=!simpl_set.

    apply: StepT' => //=; cycle 1.
      rewrite/bc; rewrite PV.
      rewrite vars_sigma0 !simpl_set /maxn; sif.
      rewrite/fresh_rule/= !FmapE.fmapE !inE eqxx orbF.
      rewrite !FmapE.fmapE eqxx [odflt _ _]/=.
      set X := select _ _ _ _ _.
      have : [:: ([fmap], [:: call (app p (Tm_V (IV 1))); call (app r (Tm_V (IV 1)))])]  = X.
        rewrite/X select_cons/get_input_vars !FmapE.fmapE eqxx.
        do 2 case: eqP => // _.
        rewrite/build_arr/H [head _]/=.
        cbn match.
        case: eqP => // _.
        rewrite select_cons/get_input_vars !FmapE.fmapE eqxx.
        do 2 case: eqP => // _.
        rewrite simpl_set/build_arr/H [head _]/=.
        cbn match.
        case: eqP => // _.
        rewrite select_cons/get_input_vars !FmapE.fmapE eqxx.
        do 2 case: eqP => // _.
        rewrite/build_arr/H [head _]/=.
        cbn match.
        case: eqP => // _.
        rewrite select_cons/get_input_vars !FmapE.fmapE eqxx.
        rewrite/build_arr/H [head _]/=.
        cbn match.
        case: eqP => // _.
        rewrite !FmapE.fmapE eqxx.
        do 2 case: eqP => // _.
        rewrite [omap _ _]/=; cbn match.
        rewrite fsetU0  ![omap _ _]/= unify_refl [omap _ _]/=.
        rewrite//=.
      move=><-.
      rewrite/=/vars_atoms/= !freshUU !freshP1 codom_vars0 freshP0/=.
      rewrite/maxn//=.

    apply: StepT => //=.
      rewrite/bc vars_sigma0 PV !simpl_set /maxn; sif.
      rewrite /fresh_rule/= !FmapE.fmapE !inE eqxx orbF.
      set X := select _ _ _ _ _.
      have : X = [:: ([fmap].[IV 1 <- Tm_P tt], [::]); ([fmap].[IV 1 <- Tm_P ff], [::])] .
        rewrite/X/= !FmapE.fmapE.
        do 4 case: eqP => // _.
        rewrite/build_arr/=.
        rewrite unify_V_0r//.
        by rewrite/=unify_V_0r//=.
      move=> ->{X}/=.
      rewrite/vars_sigma/codom_vars/vars_atoms freshP0 !codom0_set/= !simpl_set.
      by rewrite/maxn/=.
    apply: StepT => //.
      rewrite/=/bc/next_subst [next _ _]/= acyclic_sigma_set_D//.
      rewrite deref_App PV deref_V FmapE.fmapE eqxx [vars _]/=.
      rewrite vars_sigma_set !simpl_set /maxn; sif.
      rewrite /fresh_rule/= !inE eqxx !FmapE.fmapE eqxx orbF.
      set X := select _ _ _ _ _.
      have : X = [::] by rewrite/X/= !simpl_set !FmapE.fmapE/=unify_ground.
      by move=> ->{X}/=.
    apply: BackT => //=.
    apply: StepT => //.
      rewrite/=/bc/next_subst [next _ _]/= acyclic_sigma_set_D//.
      rewrite deref_App PV deref_V FmapE.fmapE eqxx [vars _]/=.
      rewrite vars_sigma_set !simpl_set /maxn; sif.
      rewrite /fresh_rule/= !inE eqxx !FmapE.fmapE eqxx orbF.
      set X := select _ _ _ _ _.
      have : X = [:: ([fmap].[IV 1 <- Tm_P ff], [::])].
        by rewrite/X/=!FmapE.fmapE eqxx/= unify_refl/=.
      move=>->{X}/=; rewrite/maxn !simpl_set//=.
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

  Goal exists v, runT unif p_test1 0 fmap0 (Unexplored (call (app p ff))) (One s1) false v.
  Proof.
    repeat eexists.
    apply: StepT' => //=; cycle 1.
      rewrite/bc.
      rewrite !simpl_set !maxnn.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/=simpl_set [omap _ _]/=; sif.
      rewrite in_fnd?inE//= => H.
      rewrite ffunE [val _]/={H} eqxx/vars_atoms/= !simpl_set/maxn//=.
    apply: StepT => //=.
      rewrite/bc.
      rewrite !simpl_set !maxnn.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/= [omap _ _]/=; sif.
      rewrite !unify_V_0r/=/vars_atoms/=; only 2-5: by [].
      by rewrite freshP0 vars_sigma_set !simpl_set /maxn//=.
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

  Goal exists r, runT unif p_test2 0 fmap0 (Unexplored (call (app p tt)) ) (One s1) false r.
  Proof.
    repeat eexists.
    apply: StepT' => //; cycle 1.
      rewrite/=/bc.
      rewrite !simpl_set !maxnn.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/=simpl_set [omap _ _]/=; sif.
      rewrite in_fnd?inE//= => H.
      rewrite ffunE [val _]/={H} eqxx/vars_atoms/= !simpl_set/maxn//=.
    apply: StepT => //=.
      rewrite/bc.
      rewrite !simpl_set !maxnn.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/= !unify_V_0r; only 2-5: by [].
      
      by rewrite/=/vars_atoms !simpl_set/maxn//=.
    apply/StepT => //=.
      rewrite/next_subst[next _ _]/=.
      rewrite/=/bc.
      rewrite !simpl_set !maxnn.
      rewrite[fresh_rules _ _]/= !simpl_set/= !FmapE.fmapE/= simpl_set acyclic_sigma_set_D ?[negb _]/=; last by [].
      by sif; rewrite !simpl_set /maxn//=.
    apply: StepT => //=.
    apply: StopOT => //=.
    by [].
  Qed.
End Test6.

Definition emptyp := (build_progr [::]).

Definition CutS := Unexplored cut.

Section Test2.
  Goal step unif emptyp 0 fmap0 (Or (Some OK) fmap0 OK) = (0, Success, Or (Some OK) fmap0 OK). by []. Qed.

  Goal runT unif emptyp 0 fmap0 (Or (Some CutS) fmap0 OK) (One fmap0) false 0.
    apply: StepT' => //=; cycle 1.
    apply: StopOT => //.
    by [].
  Qed.

  Goal forall r, 
    runT unif emptyp 0 fmap0 (Or (Some CutS) fmap0 r) (One fmap0) false 0.
    move=> r.
    apply: StepT' => //; cycle 1.
    apply: StopOT => //=.
    by [].
  Qed.

  Goal runT unif emptyp 0 fmap0 (Or (Some OK) fmap0 (Or (Some OK) fmap0 OK)) (Many fmap0 (Or None fmap0 (Or (Some OK) fmap0 OK))) false 0.
  Proof. apply: StopMT => //=. Qed.

  (* (Dead \/ !) \/ C *)
  Goal step unif emptyp 0 fmap0 (Or (Some (Or None fmap0 (CutS))) fmap0 OK) = (0, Expanded, (Or (Some (Or None fmap0 OK)) fmap0 OK)).
  Proof.
    move=>//=.
  Qed.
End Test2.

Section map.
  Definition cons := IP 1.
  Definition nil := IP 2.
  Definition one := IP 3.
  Definition two := IP 4.
  Definition four := IP 5.
  Definition map := IP 6.
  Definition double := IP 7.

  Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
  Definition consS := arr output exp exp.
  Definition nilS := exp.
  Definition oneS := exp.
  Definition twoS := exp.
  Definition fourS := exp.
  Definition doubleS := arr input exp (arr output exp func).

  Definition X := IV 8.
  Definition X' := IV 9.
  Definition Y := IV 10.
  Definition Y' := IV 11.
  Definition F := IV 12.

  Coercion Tm_V : V >-> Tm.
  
  Definition mk_p F X Y X' Y' := {|
    sig := [fmap].[map <- mapS].[double <- doubleS];
    rules := 
      mkR (app (app (app map F) nil) nil) [::] ::
      mkR (app (app (app map F) (app (app cons X) Y)) (app (app cons X') Y') ) 
        [:: call (app (app F X) X'); call (app (app (app map F) Y) Y')] ::
      mkR (app (app double one) two) [::]
      :: [::]
  |}.
    

  Definition p' := mk_p F X Y X' Y'.

  Definition list12 := app (app cons one) nil.
  Definition list24 := app (app cons two) nil.

  Definition map12d := app (app (app map double) list12) X.

  Lemma p'map: (sig p').[? map] = Some mapS.
  Proof. by rewrite !FmapE.fmapE. Qed.

  Lemma fresh_rules_cons s r0 rs:
    fresh_rules s (r0 :: rs) =
    ((fresh_rule (fresh_rules s rs).1 r0).1,
      (fresh_rule (fresh_rules s rs).1 r0).2 :: (fresh_rules s rs).2).
  Proof. by rewrite/=!push//. Qed.

  Lemma fstS T1 T2 (a:T1) (b:T2): (a,b).1 = a. by []. Qed.
  Lemma sndS T1 T2 (a:T1) (b:T2): (a,b).2 = b. by []. Qed.

  Lemma inl_map_get_tm_hdmap:
    inl map == get_tm_hd map.
  Proof. by []. Qed.

  Lemma fmapIn e (S: {fset V}) (f: V) (H : e \in S):
    [ffun x : S => f].[? e] = Some f.
  Proof. by rewrite in_fnd/= ffunE/=. Qed.

  Lemma fresh_tm_app s m f a: fresh_tm s m (app f a) = 
    ((fresh_tm (fresh_tm s m f).1 (fresh_tm s m f).2 a)).
  Proof. by rewrite/=!push. Qed.

  Lemma fresh_tm_P s r p: fresh_tm s r (Tm_P p) = (s, r). by []. Qed.

  Lemma get_input_vars_map12d:
    (get_input_vars p' map12d).1 = fset0.
  Proof.
    rewrite/map12d/= !FmapE.fmapE not_fnd// !simpl_set.
    by rewrite !eqxx/= !fsetU0.
  Qed.

  Lemma sum_pop x (S: {fset V}): IV x \notin S ->
    (\max_(i <- (IV x |` S : {fset V})) (let 'IV n := i in n)) = (maxn x 
      (\max_(i <- S) (let 'IV n := i in n)))%nat.
  Proof.
    rewrite (big_fsetD1 (IV x))/=; last by rewrite !inE eqxx.
    move=> IV; rewrite !fsetDUl !rem1 eqxx !simpl_set.
    by do 3 f_equal; apply/fsetDidPl; rewrite fdisjointX1.
  Qed.

  Lemma sum_pop0 x:
    (\max_(i <- [fset IV x]) (let 'IV n := i in n)) = x.
  Proof.
    rewrite (big_fsetD1 (IV x))/=; last by rewrite !inE eqxx.
    by rewrite rem1 eqxx/= big_nil maxn0.
  Qed.

  Local Lemma v_progP: fresh (v_prog (rules p')) = 13.
  Proof.
    by rewrite /v_prog/=/varsU_rule/varsU_rhead/varsU_rprem/= !simpl_set/maxn/=.
  Qed.
  
   Check fresh_atoms.
  
  Lemma fresh_atoms_cons n m x xs:
    fresh_atoms n m (x :: xs) =
      let Fxs := fresh_atoms n m xs in
      let Fx := fresh_atom Fxs.1.1 Fxs.1.2 x in
      (Fx.1.1,Fx.1.2,(Fx.2::Fxs.2)).
  Proof. by rewrite/= !push//=. Qed.

  Local Lemma simpl_p (n:nat):
    fresh_rules n (rules p') = (addn 6 n,
       [:: {| head := app (app (app map (IV (5+n))) nil) nil; premises := [::] |};
           {|
             head :=
               app (app (app map (IV n)) (app (app cons (IV n.+1)) (IV (2 + n))))
                 (app (app cons (IV (3+n))) (IV (4+n)));
             premises :=
               [:: call (app (app (IV n) (IV n.+1)) (IV (3+n)));
                   call (app (app (app map (IV n)) (IV (2+n))) (IV (4+n)))]
           |};
           {| head := app (app double one) two; premises := [::] |}]).
  Proof.
    set r1 := {| head := _; premises := _ |}.
    set r2 := {| head := _; premises := _ |}.
    set r3 := {| head := _; premises := _ |}.
    rewrite/p' fresh_rules_cons.
    set X := fresh_rules _ _.
    rewrite /=FmapE.fmapE eqxx/=.
    have: X = (addn 5 n, [:: r2; r3]).
      rewrite{}/X fresh_rules_cons.
      set X := fresh_rules _ _.
      have: X = (n,[:: r3]) by [].
      move=> ->{X}//=.
      set RF := fresh_rule _ _.
      have: RF = (addn 5 n, r2).
        rewrite{}/RF/fresh_rule [premises _]/=[head _]/=.
        rewrite /rename [fresh_tm _ _ _]/=.
        repeat (rewrite ?orbF!inE; repeat case: eqP => // _); sif.
        rewrite fresh_atoms_cons.
        set FR := fresh_atoms _ _ _.
        set sigma := [fmap].[F <- IV n].[X <- IV n.+1].[Y <- IV (2+n)].[X' <- IV (3+n)].[Y' <- IV (4+n)].
        set bo := call (app (app (app map (IV n)) (IV (2+n))) (IV (4+n))).
        have: FR = (addn 5 n, sigma, [:: bo]).
          rewrite{}/FR fresh_atoms_cons.
          set FR := fresh_atoms _ _ _.
          have: FR = (addn 5 n, sigma, [::]).
            by [].
          move=> ->{FR}; cbn zeta.
          set FR := fresh_atom _ _ _.
          have: FR = (addn 5 n, sigma, bo).
            rewrite{}/FR/fresh_atom/rename.
            set FR := fresh_tm _ _ _.
            have: FR = (addn 5 n, sigma).
              rewrite{}/FR/= !inE eqxx orbT.
              by rewrite !inE eqxx orbT !inE eqxx/=.
            move=>->; rewrite !ren_app !ren_V !FmapE.fmapE.
            by rewrite !eqxx/=.
          by move=> /=->.
        move=>->{FR}; cbn zeta.
        set FR := fresh_atom _ _ _.
        have: FR = (addn 5 n, sigma, call (app (app (IV n) (IV n.+1)) (IV (3+n)))).
          rewrite{}/FR /fresh_atom/rename.
          set FR := fresh_tm _ _ _.
          have: FR = (addn 5 n, sigma).
            by rewrite{}/FR/= !inE eqxx orbT !inE orbT !inE orbT.
          by move=> ->{FR}; rewrite !ren_app !ren_V !FmapE.fmapE eqxx/=.
        move=> ->{FR}.
        by rewrite/ren !FmapE.fmapE eqxx/=.
      by move=> ->{RF}//.
    move=> ->{X}//.
  Qed.
  
  Check matching.
  
  Lemma matching_Vd f (v: V) t s: v \notin vars_sigma s -> v \notin f -> 
    v \notin (vars t) -> matching f (Tm_V v) t s = Some s.[v <- deref s t].
  Proof.
    move=> /[dup]; rewrite {1}inE => /norP[vd vc] vs vf vt.
    rewrite/matching/montanari_deref/montanari_pair.
    rewrite not_in_deref/=; last rewrite fdisjointX1//.
    rewrite montanari_equation (negbTE vf).
    rewrite ifF; last first.
      case: eqP => //; subst.
      move: vc vt.
      destruct t; rewrite//=!inE; case: eqP => //=vv1.
      case: fndP => //= v1s + _.
        by move=> +/= H; move=> /codom_varsP[]; exists v1,v1s; rewrite -H/= inE.
      by move=> +[?]; subst.
    rewrite ifF; last first.
      move: (conj vt vc) => /norP.
      apply: contraNF.
      by move=> /fsubsetP-/(_ _ (vars_tm_deref_sub _ _)); rewrite inE orbC.
    rewrite montanari_equation/=/deref_sigma; do 2 f_equal.
    apply/fmapP => k.
    case: fndP => ks; last by rewrite not_fnd.
    rewrite ffunE valPE/derefkv in_fnd not_in_deref//= fsetU0 fdisjoint1X.
    by apply/contra/vc => H; apply/codom_varsP; eexists _,ks.
  Qed.
  
  Ltac simpl_acyclic_set:=
    rewrite !acyclic_sigma_set !inE !remf1_set empty_rem/=;
    repeat rewrite codom_vars_set ?remf1_set empty_rem/=;
    rewrite codom_vars0 !fsetU0 inE ?fdisjointXU fdisjointX0 ?fdisjointX1 ?inE !andbT.

  Goal exists f s, runT u p' 0 fmap0 (Unexplored (call map12d)) (One s) false f /\ deref s X = list24.
  Proof.
    do 2 eexists.
    rewrite/u.
    split.
      apply: StepT'=> //=; cycle 1.
      { rewrite/bc ifF ?acyclic_sigma0//.
      rewrite !simpl_set !maxnn /maxn simpl_p; sif.
      set FR := select _ _ _ _ _.
      have : FR = [:: ([fmap].[IV 13 <- Tm_P double].[IV 14 <- one].[IV 15 <- nil].[X <- 
       app (app cons (IV 16)) (IV 17)],
       [:: call (app (app (IV 13) (IV 14)) (IV 16));
           call (app (app (app map (IV 13)) (IV 15)) (IV 17))])].
        { rewrite{}/FR select_cons [head _]/=[premises _]/= get_input_vars_map12d.
        rewrite/addn ![Nat.add _ _]/=.
        rewrite/map12d/list12.
        rewrite/H eqxx !FmapE.fmapE eqxx /mapS.
        rewrite[omap _ _]/=; cbn match.
        rewrite eqxx [lang.matching _]/= matching_Vd//?vars_sigma0//.
        rewrite [omap _ _]/=; cbn match.
        rewrite eqxx.
        set W := matching _ _ _ _.
        have : W = None.
          by rewrite/W/matching/montanari_deref/montanari_pair/= montanari_equation.
        move=> ->{W}; rewrite [omap _ _]/=.
        cbn match; rewrite select_cons.
        set X:= select _ _ _ _ _.
        have: X = [::] by [].
        move=> ->{X}; rewrite[head _]/=.
        set X := get_input_vars _ _.
        have: X.1 = fset0.
          by rewrite/X/get_input_vars !FmapE.fmapE/= !simpl_set.
        move=> ->{X}.
        rewrite/H/= !FmapE.fmapE/=.
        rewrite matching_Vd?vars_sigma0//=.
        rewrite !matching_app?acyclic_sigma_set_D//.
        rewrite !matching_refl/= matching_Vd//; last first.
          by rewrite vars_sigma_set !inE.
        rewrite /= matching_Vd//=; last first.
          rewrite /vars_sigma/=.
          by repeat rewrite !codom_vars_set ?remf1_set/= ?(empty_rem, codom_vars0,inE).
        rewrite unify_Vr//; (only 2,4: by rewrite !inE); last first.
          by repeat rewrite !codom_vars_set ?remf1_set/= ?(empty_rem, codom_vars0,inE).
        rewrite !deref_App !deref_P !deref_V !FmapE.fmapE/= !not_fnd//.
      }
      move=> ->{FR}.
      rewrite/max_sigmas/=/vars_atoms/=/vars_sigma codom_vars_set !remf1_set empty_rem/=.
      do 3 rewrite codom_vars_set ?remf1_set empty_rem/=.
      by rewrite codom_vars0 !simpl_set/maxn/=.
      }
      apply: StepT => //=.
      {
      rewrite/bc ifF ?acyclic_sigma0//.
      set X := fresh _.
      have: X = 20.
        rewrite{}/X deref_App !deref_V !FmapE.fmapE not_fnd//.
        rewrite !simpl_set/=.
        rewrite in_fnd?inE//.
        move=> X; rewrite ffunE/={X}.
        rewrite !FmapE.fmapE/=.
        repeat rewrite codom_vars_set ?remf1_set empty_rem/=.
        rewrite codom_vars0 !simpl_set.
        by rewrite/maxn/=/addn![Nat.add _ _]/=.
      move=> ->{X}.
      rewrite simpl_p.
      rewrite/addn ![Nat.add _ _]/=.
      set FR := select _ _ _ _ _.
      have : FR =  [:: ([fmap].[IV 16 <- Tm_P two].[IV 13 <- double].[IV 14 <- one].[IV 15 <- nil].[X <- app
                      (app cons two) (IV 17)], [::])].
        { rewrite{}/FR select_cons [head _]/=[premises _]/=.
          set FR := deref _ _.
          have: FR = app (app double one) (IV 16).
            by rewrite/FR !deref_App !deref_V !FmapE.fmapE/= not_fnd//=.
          move=> ->{FR}.
          set FR := get_input_vars _ _.
          have: FR = (fset0, Some func).
            by rewrite/FR/get_input_vars !FmapE.fmapE/= !simpl_set.
          move=> ->{FR}.
          rewrite/H select_cons [head _]/=[premises _]/=.
          set FR := (get_input_vars _ _).1.
          have: FR = fset0.
            by rewrite/FR/get_input_vars !FmapE.fmapE/= !simpl_set.
          move=> ->{FR}.
          rewrite/H.
          rewrite select_cons [select _ _ _ _ _]/= [head _]/=.
          set FR := (get_input_vars _ _).1.
          have: FR = fset0.
            by rewrite/FR/get_input_vars !FmapE.fmapE/= !simpl_set.
          move=> ->{FR}.
          rewrite/H eqxx !FmapE.fmapE eqxx [omap _ _]/=/doubleS eqxx.
          rewrite [lang.matching _]/= matching_refl [omap _ _]/=/=.
          rewrite unify_VR//; last by rewrite !inE.
          rewrite deref_P !deref_sigma_set; only 2-5: by [].
          rewrite deref_sigma0/derefkv !deref_App !deref_P !deref_V.
          rewrite !FmapE.fmapE/= !not_fnd// deref_sigma0/=.
        }
      move=> ->{FR}.
      rewrite/max_sigmas/=/vars_sigma/vars_atoms/=.
      repeat rewrite codom_vars_set ?remf1_set empty_rem/=.
      rewrite codom_vars0 !simpl_set.
      by rewrite/maxn/=.
    apply/negbF.
    repeat simpl_acyclic_set.
    by rewrite !acyclic_sigma_set !inE empty_rem acyclic_sigma0 codom_vars0/= fdisjointX0.
    }
    apply: StepT => //=.
    {
      rewrite/bc ifF ?acyclic_sigma0//.
      rewrite/next_subst[next _ _]/=.
      set X := fresh _.
      have: X = 27.
        rewrite{}/X deref_App !deref_V !FmapE.fmapE not_fnd//.
        rewrite !simpl_set/=.
        rewrite in_fnd?inE//.
        move=> X; rewrite ffunE/={X}.
        rewrite !FmapE.fmapE/=.
        repeat rewrite codom_vars_set ?remf1_set empty_rem/=.
        by rewrite codom_vars0 !simpl_set.
      move=> ->{X}.
      set FR:= deref _ _.
      have: FR = app (app (app map double) nil) (IV 17).
        rewrite/FR !deref_App !deref_V !FmapE.fmapE/= not_fnd//=.
      move=> ->{FR}.
      rewrite simpl_p.
      set FR := select _ _ _ _ _.
      have : FR = [:: ([fmap].[IV 17 <- Tm_P nil].[IV 16 <- two].[IV 13 <- double].[
         IV 14 <- one].[IV 15 <- nil].[X <- app (app cons two) nil].[
         IV 32 <- double], [::])].
        { rewrite{}/FR select_cons [head _]/=[premises _]/=.
        set FR := (get_input_vars _ _).1.
        have: FR = fset0.
          by rewrite/FR/get_input_vars !FmapE.fmapE/= !simpl_set.
        move=> ->{FR}.
        rewrite/addn ![Nat.add _ _]/=.
        set FR := H _ _ _ _ _ _.
        have: FR = Some
          (func,
           [fmap].[IV 17 <- Tm_P nil].[IV 16 <- two].[IV 13 <- double].[
           IV 14 <- one].[IV 15 <- nil].[X <- app (app cons two) nil].[
           IV 32 <- double]).
          rewrite{}/FR/H/= !FmapE.fmapE/= matching_Vd//; last first.
            rewrite/vars_sigma/=.
            repeat rewrite codom_vars_set ?remf1_set empty_rem/=.
            by rewrite codom_vars0 !simpl_set !inE.
          rewrite/=matching_refl/=.
          rewrite unify_VR; only 2-4: by rewrite //!inE//.
          rewrite !deref_sigma_set; only 2-7: by [].
          rewrite deref_sigma0/derefkv !deref_App !deref_P !deref_V.
          by rewrite !FmapE.fmapE/=.
        move=> ->{FR}.
        rewrite select_cons [head _]/=[premises _]/=.
        set FR := H _ _ _ _ _ _.
        have: FR = None.
          rewrite{}/FR/H/=!FmapE.fmapE/= !simpl_set matching_Vd//; last first.
            rewrite/vars_sigma/=.
            repeat rewrite codom_vars_set ?remf1_set empty_rem/=.
            by rewrite codom_vars0 !simpl_set !inE.
          rewrite/=.
          rewrite/matching/montanari_deref !deref_App !deref_P !deref_V !FmapE.fmapE/=!not_fnd//=.
          by rewrite /montanari_pair montanari_equation/=.
        by move=> ->/=.
        }
      move=> ->{FR}//.
      apply:negbF.
      repeat simpl_acyclic_set.
      by rewrite !acyclic_sigma_set !inE empty_rem acyclic_sigma0 codom_vars0 fdisjointX0 inE.
      }
      apply: StopOT => //=.
      by [].
    rewrite/next_subst[next _ _]/=/X.
    by rewrite deref_V !FmapE.fmapE/=.
  Qed.
End map.
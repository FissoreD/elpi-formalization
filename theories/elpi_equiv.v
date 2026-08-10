From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop.
From det Require Import list tree_vars elpi_clean_ca.

Section NurEqiv.
  Variable (u : Unif).
  Notation runT := (runT u).
  Notation runS := (runS u).

  Lemma tree_to_elpi_aux p fv A s1 b fv' r:
    vars_tree A `<=` fv -> vars_sigma s1 `<=` fv ->
    sld_tree A ->
      runT p fv s1 A r b fv' -> 
        let xs := tree_to_stack A s1 [::] in
        match r with
        | Zero => runS p fv xs None
        | One s' => runS p fv xs (Some (s', [::]))
        | Many s' t => runS p fv xs (Some (s', tree_to_stack t s1 [::]))
        end.
  Proof.
    move=> +++H.
    elim_run H => vtA vts1 vA.
    + by rewrite (success_tree_to_stack s1)//= NN; apply: StopS.
    + by rewrite (success_tree_to_stack s1)//= NS; apply: StopS.
    + have [fvB fvs] := vars_tree_step_sub_flow vtA vts1 eA.
      have /=vB:= (valid_tree_step vA eA). 
      have {IH}/=:= IH fvB fvs vB; subst.
      have /=[] := incomplete_exp_cut pA eA => ?; subst.
        have H5 := step_cb_same_subst1 vA eA; subst.
        have [x[tl[H1 [H2 H3]]]] := s2l_CutBrothers s1 [::] vA eA.
        rewrite H1 H2 H5 => IH.
        have ?:= tree_fv_step_cut eA; subst.
        by case: r rB IH => > rB; apply: CutS => //=.
      have fA := step_not_failed eA notF.
      have [s[x[xs +]]] := failed_tree_to_stack vA fA s1 [::].
      move=> H; rewrite H/=.
      case: x H => [|g gs]/= H.
        have [] := s2l_empty_hd_success vA (step_not_failed eA notF) H.
        by rewrite (step_not_solved eA notF)//.
      fConsG g gs.
      case: g H => [[|c] ca] H; last first.
        have:= s2l_Expanded_call vA eA H.
        move=> [??]; subst.
        case X: bc => /=[fv3 rules].
        rewrite !cats0 => H1.
        have {}H1 : tree_to_stack B s1 [::] =
            match rules with
            | [::]%SEQ => [::]
            | (w :: ws)%SEQ => (w.1, save_gs xs gs w.2) :: save_as xs gs ws
            end ++ xs.
          by case: rules H1 X => //; rewrite cat0s.
        have {}H2 : stepE u p v0 c (next_subst s1 A) xs gs = (fv3,
          match rules with
          | [::]%SEQ => [::]
          | (w :: ws)%SEQ => (w.1, save_gs xs gs w.2) :: save_as xs gs ws
          end).
          by rewrite /stepE X//=; destruct rules;rewrite//cat0s.
        rewrite H1.
        by case: r rB => > rB Hx; apply: CallS Hx.
      have [[[? SS] H1]] := s2l_Expanded_cut vA eA H; subst.
      rewrite cats0 => ->.
      by case: r {rB} => >; apply: CutS.
    + have vB := valid_tree_prune vA nA.
      have {}fvP := vars_tree_prune_sub_flow vtA nA.
      have {IH} /= := IH fvP vts1 vB.
      by rewrite (pruneF_tree_to_stack vA fA nA).
    + move=>/=.
      rewrite (failed_prune_none_tree_to_stack _ _ nA)//.
        by constructor.
      by apply/prune_None.
  Qed.

(* USED TO SKIP NO-OP IN TREE SEMANTICS *)
Lemma elpi_to_tree_no_op v0 p a r s0:
  size a != 0 ->
  runS p v0 a r ->
  let P t0 := 
    sld_tree t0 -> tree_to_stack t0 s0 [::] = a ->  
    exists b v1,
    if r is Some (s1, a') then 
      match a' with
      | [::] => runT p v0 s0 t0 (One s1) b v1
      | _ => exists t1, runT p v0 s0 t0 (Many s1 t1) b v1 /\ tree_to_stack t1 s0 [::] = a'
      end
    else runT p v0 s0 t0 Zero b v1 
  in
  (forall A, failed A = false -> P A) -> forall a, P a.
Proof.
  simpl.
  move=> sA R P A vA H.
  case fA: (failed A); last by auto.
  case nA: (prune false A) => [A'|]; last first.
    by rewrite (failed_prune_none_tree_to_stack vA fA nA) in H; subst.
  have /= fA' := prune_Some nA.
  have /= vA' := (valid_tree_prune vA nA).
  rewrite (pruneF_tree_to_stack vA fA nA) in H.
  have [b[v1 {}P]] := P A' fA' vA' H.
  case: r P R => [[s1 a0]|H1 H2]; subst.
    case: a0.
      by repeat eexists; apply: BackT P.
    move=> x xs.
    move=> [t' [H1 H2 H3]].
    by repeat eexists; eauto; apply: BackT fA nA H1.
  repeat eexists; apply: BackT fA nA H1.
Qed.

Lemma elpi_to_tree_aux p v0 a r : 
  runS p v0 a r -> 
  forall s0 t0, sld_tree t0 -> tree_to_stack t0 s0 [::] = a ->  
  exists b v1,
  match r with
  | None => runT p v0 s0 t0 Zero b v1
  | Some (s, [::]) => runT p v0 s0 t0 (One s) b v1
  | Some (s, a') => exists t1, runT p v0 s0 t0 (Many s t1) b v1 /\ tree_to_stack t1 s0 [::] = a'
  end.
Proof.
  elim; clear.
  - move=> s a fv s1 A vA /= H.
    have H1 := elpi_to_tree_no_op _ (StopS _ _ _ _ _) _ vA H.
    apply: H1; auto => A' fA' vA' H1.
    have [skA ?]:= s2l_empty_hd_success vA' fA' H1; subst.    
    have:=@s2l_prune_tl _ s1 nilA vA' skA; rewrite H1 behead_cons => ?; subst.
    case P: prune => [A''|]/=; last by repeat eexists; apply: StopOT.
    have [sz[k[ks Hk]]]/= := failed_tree_to_stack (valid_tree_prune vA' P) (prune_Some P) s1 [::].
    by rewrite Hk; repeat eexists; first apply: StopMT P => //.
  - move=> s1 a ca r gl fv ELPI IH s A vA H.
    have H1 := elpi_to_tree_no_op _ (CutS _ _) _ vA H.
    apply: H1; auto => {}A fA {}vA {}H.
    case X: (step u p fv s A) => [[fv' r'] A'].
    have:= next_cut_s2l u p fv fA vA H => /=.
    move => -[H1 H2].
    have /= {IH}[b[v1]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
    have IA : incomplete A by move: H2; case: ifP => [_/incomplete_cut|_/incomplete_exp].
    case: r ELPI => [[s' a']|] ELPI.
      case: a' ELPI => [|x xs] ELPI; last first.
        move=> [t1[IH Z]].
        have S := StepT IA _ IH.
        move: H2; case: ifP => H2 ST;
        by eexists _, _, t1; split => //; apply: S ST.
      move: H2; case: ifP => CB H2 Hx;
      by eexists; eexists; apply: StepT H2 Hx.
    move: H2; case: ifP => //= CB ST IH; subst; repeat eexists;
    apply: StepT IH; eauto.
  - move=> s1 a g bs r t ca fv fv' ST ELPI IH s3 A vA H.
    have H1 := elpi_to_tree_no_op _ (CallS _ ST _) _ vA H.
    apply: H1; auto => {}A fA {}vA {}H.
    move: ST; rewrite/stepE; case B: bc => [fv2 rules] [??]; subst.
    have [] := next_callS_s2l u p fv fA vA H.
    rewrite B/= => H1.
    case H2 : step => /=[fvt A']?; subst.
    have /= {IH}[b[v1]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
    have IA := incomplete_exp H2.
    rewrite H2/=.
    case: r ELPI => [[s' a']|] ELPI.
      case: a' ELPI => [|x xs] ELPI.
        by move=> Hx; repeat eexists; apply: StepT H2 Hx.
      move=> [t'[IH Z]]; subst.
      repeat eexists; [|eassumption]; by apply: StepT H2 IH.
    move=> IH.
    by repeat eexists; apply: StepT H2 IH.
  + by move=> > vT H; repeat eexists; apply/FailT/tree_to_stack_nil_na/H.
Qed.

(*SNIPT: runt1 *)
Definition runT' p v s t r := 
  exists b v', runT p v s t r b v'.
(*ENDSNIPT: runt1 *)

(*SNIPT: tree_to_elpi *)
Theorem runT_to_runS:
  forall p t s r, let v := vars_tree t `|` vars_sigma s in
    sld_tree t -> runT' p v s t r -> 
      let r' := match r with
      | Zero => None
      | One s' => Some (s', [::])
      | Many s' t' => Some (s', tree_to_stack t' s [::]) 
      end in
        runS p v (tree_to_stack t s [::]) r'.
(*ENDSNIPT: tree_to_elpi *)
Proof. 
  move=> /= p t0 s0 r/= vt [b [fv H1]].
  have /= := tree_to_elpi_aux (fsubsetUl _ _) (fsubsetUr _ _) vt H1.
  by destruct r.
Qed.

(*SNIPT: elpi_to_tree *)
Theorem runS_to_runT:
  forall p v a r, runS p v a r -> 
    forall s t, sld_tree t -> tree_to_stack t s [::] = a ->
      match r with
      | None => runT' p v s t Zero
      | Some (s', [::]) => runT' p v s t (One s')
      | Some (s', a') => 
        exists t', runT' p v s t (Many s' t') /\ tree_to_stack t' s [::] = a'
      end.
(*ENDSNIPT: elpi_to_tree *)
Proof.
  move=> /= p v a r H1 s' t vt tl.
  have:= elpi_to_tree_aux H1 vt tl.
  move=> [b[v1]]; case: r H1 => [[x[|y ys H [t' [H1]]]]|]; repeat
  eexists; eauto.
Qed.


Print Assumptions runS_to_runT.
Print Assumptions runT_to_runS.

(*SNIPT: tree_to_elpi_call *)
Theorem runT_to_runSC:
  forall p t s r, let v := vars_tm t `|` vars_sigma s in
    runT' p v s (Unexplored (call t)) r -> 
      let r' := match r with
      | Zero => None
      | One s' => Some (s', [::])
      | Many s' t' => Some (s', tree_to_stack t' s [::]) 
      end in
        runS p v ((s, consG (call t, [::]) [::]) :: [::]) r'.
(*ENDSNIPT: tree_to_elpi_call *)
Proof.
  move=> /= p t s r R'.
  by have /= := @runT_to_runS p (Unexplored (call t)) s r isT R'.
Qed.

(*SNIPT: elpi_to_tree_call *)
Theorem runS_to_runTC:
  forall p t s r v, runS p v ((s, consG (call t, [::]) [::]) :: [::]) r -> 
      match r with
      | None => runT' p v s (Unexplored (call t)) Zero
      | Some (s', [::]) => runT' p v s (Unexplored (call t)) (One s')
      | Some (s', a') => 
        exists t', runT' p v s (Unexplored (call t)) (Many s' t') /\ tree_to_stack t' s [::] = a'
      end.
(*ENDSNIPT: elpi_to_tree_call *)
Proof.
  move=> p t s r v R.
  have:= runS_to_runT R.
  move=> /(_ s (Unexplored (call t)) isT erefl).
  rewrite//.
Qed.

(*SNIPT: runS_to_runTCZero *)
Theorem equiv_zero:
  forall p t s, let v := vars_tm t `|` vars_sigma s in
    runS p v ((s, consG (call t, [::]) [::]) :: [::]) None <-> 
    runT' p v s (Unexplored (call t)) Zero.
(*ENDSNIPT: runS_to_runTCZero *)
Proof.
  move=> /= p t s; split => R.
    have:= runS_to_runT R.
    by move=> /(_ s (Unexplored (call t)) isT erefl).
  by apply : runT_to_runSC R.
Qed.

(*SNIPT: runS_to_runTCOne *)
Theorem equiv_one:
  forall p t s s', let v := vars_tm t `|` vars_sigma s in
    runS p v ((s, consG (call t, [::]) [::]) :: [::]) (Some (s', [::])) <-> 
    runT' p v s (Unexplored (call t)) (One s').
(*ENDSNIPT: runS_to_runTCOne *)
Proof.
  move=> /= p t s s'; split => R.
    have:= runS_to_runT R.
    by move=> /(_ s (Unexplored (call t)) isT erefl).
  by apply : runT_to_runSC R.
Qed.

(*SNIPT: runS_to_runTCMany2 *)
Theorem sound_many:
  forall p t s s' x xs, let v := vars_tm t `|` vars_sigma s in
    runS p v ((s, consG (call t, [::]) [::]) :: [::]) (Some (s', x :: xs)) -> 
    exists t', runT' p v s (Unexplored (call t)) (Many s' t') /\ tree_to_stack t' s [::] = x :: xs.
(*ENDSNIPT: runS_to_runTCMany2 *)
Proof.
  move=> /= p t s s' x xs R.
  have:= runS_to_runT R.
  by move=> /(_ s (Unexplored (call t)) isT erefl)/=.
Qed.

(*SNIPT: runS_to_runTCMany1 *)
Theorem complete_many:
  forall p t s s' t', let v := vars_tm t `|` vars_sigma s in
    runT' p v s (Unexplored (call t)) (Many s' t') ->
    runS p v ((s, consG (call t, [::]) [::]) :: [::]) (Some (s', tree_to_stack t' s [::])).
(*ENDSNIPT: runS_to_runTCMany1 *)
Proof.
  move=> /= p t s s' t' R.
  by have /= := runT_to_runSC R.
Qed.


End NurEqiv.
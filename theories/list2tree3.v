From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Fixpoint a2t_ l :=
  match l with
  | no_alt => Bot
  | more_alt (s1, x) t =>
    Or Bot s1 (Or (gs2t_ x) empty (a2t_ t))
  end
with gs2t_ l :=
  match l with
  | no_goals => Top
  | more_goals x xs => 
    let tl := gs2t_ xs in
    match (g2t_ x) with
    | (x, None) => And x tl tl 
    | (x, Some bt) => 
        let bt' := (Or Top empty bt) in
        let tl' := And bt' Top tl in
        And x tl' tl'
    end
  end
with g2t_ l :=
  match l with
  | cut ca => (CutS, Some (a2t_ ca))
  | call p t => (CallS p t, None)
  end.

(* Definition a2t (l:alts) := a2t_ (rev (map (fun '(s,x) => (s, rev x)) l)). *)

Fixpoint of_goals l :=
  match l with
    | [::] => nilC
    | cut l :: xs => (cut l) ::: (of_goals xs)
    | (call _ _ as hd) :: xs => hd ::: (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => -nilCA
  | x :: xs => (empty, of_goals x) ::: (of_alt xs)
  end.

Section s.
  Variable p : program.
  Variable c1 : Callable.
  Variable c2 : Callable.
  Variable A B C D E F : Callable.
  Variable s : Sigma.
  Definition c := call p (c1).
  Definition q := call p (c2).

  Goal exists x, (a2t_ ((s, (c ::: (q:::nilC))) ::: nilC)) = x.
  Proof. move=> /=. Admitted.

  Goal exists x, a2t_ ((s, (c ::: nilC)) ::: ((s, (q ::: nilC)) ::: no_alt)) = x.
  Proof. move=> /=. Admitted.

  Goal
  (* original is (((! \/ A) \/ B)) /\ (D) *)
  (* produced is ((bot \/ !D) \/ AC) \/ BC *)
    exists x, 
    let f x := (CallS p x) in
      a2t_ ((of_alt [:: 
        [::cut (of_alt [:: [:: call p B; call p C]]); call p D];
        [:: call p A; call p C]; 
        [:: call p B; call p C]])) = x.
  Proof.
    simpl of_alt.
    move=>/=.
    set X:= And _ _ Top.
    set Y:= And _ _ X.
    set Z:= Or _ _ Bot.
    set W:= And _ _ Top.
    set T:= And _ _ W.
  Abort.

  Goal
  (* original (OK \/ A) /\_B OK *)
  (* produces is : (Bot \/ Top) \/ AB *)
  let f x := (CallS p x) in
  a2t_ (of_alt [::[::]; [::call p A; call p B]]) = 
    Or Bot empty
  (Or Top empty
     (Or Bot empty
        (Or
           (And (CallS p A) (And (CallS p B) Top Top)
              (And (CallS p B) Top Top))
           empty Bot))) .
  Proof.
    move=>/=.
    set X:= And _ _ Top.
    set Y:= And _ _ X.
    set Z:= Or _ _ Bot.
    move=>//.
  Qed.
End s.

Lemma expand_a2t {u ign1 L}: 
  expand u ign1 (a2t_ L) = Failure (a2t_ L).
Proof. case: L => //=-[]//. Qed.

Lemma expanded_a2t u ign1 L:
  expandedb u ign1 (a2t_ L) (Failed (a2t_ L)) false.
Proof. case: L => [|[s g]gs]/=; constructor => //. Qed.

(* Lemma runb_a2t {u ign1 L s r b}:
  runb u ign1 (a2t_ L) s r b -> b = false.
Proof.
  remember (a2t_ L) as a eqn:Ha => H.
  elim: H L Ha; clear.
  - move=> s1 s2 A B C b + _ L ?; subst.
    move=> /(expanded_consistent _ (expanded_a2t u s1 L)) []//.
  - move=> s1 s2 s3 A B C D b1 b2 b3 + _ _ H ? L ?; subst.
    move=> /(expanded_consistent _ (expanded_a2t u s1 L)) []// _ <-//.
    congruence.

  
  case: L => [|[s g]gs]/=; constructor => //. Qed. *)

Lemma run_a2t_ign {u s2 D b2 sIgn1 L} sIgn2:
  runb u sIgn1 (a2t_ L) s2 D b2 ->
    runb u sIgn2 (a2t_ L) s2 D b2.
Proof.
  inversion 1; subst.
  - have:= expanded_a2t u sIgn1 L.
    move=> /(expanded_consistent _ H0) []//.
  - apply: run_backtrack; (try eassumption) => //.
    have:= expanded_a2t u sIgn1 L.
    move=> /(expanded_consistent _ H0) []//[??]; subst.
    apply: expanded_a2t.
Qed.

Lemma run_success_add_ca_deep {u s s1 B D bt bt1 res b}:
  success B ->
    runb u s1 (a2t_ (state_to_list B s bt)) res D b ->
    exists D0 b0,
      runb u s1 (a2t_ (add_ca_deep bt1 (state_to_list B s bt))) res D0 b0 .
Proof.
  elim: B s s1 D bt bt1 res b => //=.
  - move=> s s1 D _ _ res b _.
    do 2 eexists; eassumption.
  - move=> A HA s0 B HB s s1 C bt bt1 res b.
    case: ifP => [dA sB|dA sA].
      rewrite state_to_list_dead//.
Admitted.

Lemma run_a2t_success {C} u s1 bt:
  success C ->
  exists D b2, runb u s1 (a2t_ (state_to_list C s1 bt)) (get_substS s1 C) D b2.
Proof.
  elim: C s1 bt => //=.
  - move=> s1 _; do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_fail => //.
    - move=> //=.
    - apply: run_done => //.
    - apply: expanded_step => //.
      apply: expanded_done => //.
  - move=> A HA s B HB s1 bt.
    case: ifP => [dA sB | dA sA].
    - rewrite state_to_list_dead//cat0s.
      have {HB HA} [D[b2]]:= HB s nilC sB; clear -sB.
      move=> /(run_a2t_ign s1) H.
      apply: run_success_add_ca_deep sB H.
    - rewrite add_ca_deep_cat.
      admit.
  - move=> A HA B0 _ B HB.
Admitted.

Lemma runb_a2t_expandedb {u s A s' B b bt}:
  valid_state A ->
  expandedb u s A (Done s' B) b ->
    exists C b2,
    runb u s (a2t_ (state_to_list A s bt)) s' C b2.
Proof.
  remember (Done _ _) as d eqn:Hd => +H.
  elim: H s' B Hd; clear => //=.
  - move=> s1 s2 A B HA s3 C [??]vA; subst.
    have [[??] sC]:= expand_solved_same _ HA; subst.
    apply: run_a2t_success sC.
  - move=> s1 s2 r A B b HA HB IH s3 C ? vA; subst.
    have /=vB := valid_state_expand _ vA HA.
    have {IH} := IH _ _ erefl vB.
    have [x[tl[[H1 H2] H3]]]:= s2l_CutBrothers _ s1 bt vA HA.
    rewrite H1 H2/=.
    move=> [C1[b2 IH]].
    inversion IH; subst; clear IH.
      inversion H => //.
    inversion H; subst; clear H => //.
    move: H8 => //[?]; subst.
    move: H0 => /=; rewrite andbF; case: ifP => //dx.
    case X: next_alt => [[s4 D]|]//[??]; subst.
    have [H5 H6]:= expand_cb_same_subst1 _ vA HA; subst.
    do 2 eexists.
    apply: run_backtrack => //.
    - apply: expanded_fail => //.
    - rewrite /=H6 X//.
    - apply: run_done => //.
      do 2 apply: expanded_step => //.
      apply: expanded_done => //=.
      rewrite 


Admitted.

Definition not_run A:= forall u s s' B b, runb u s A s' B b -> False.

Inductive equiv_run : state -> state -> Prop :=
  | equiv_run_fail A B : not_run A -> not_run B -> equiv_run A B
  | equiv_run_success u s1 s2 A B A' B' :
    run u s1 A s2 A' -> run u s1 B s2 B' -> equiv_run A' B' -> equiv_run A B.

Lemma xx u s1 s2 A B b1: 
  
  runb u s1 A s2 B b1 -> 
    exists C b2, runb u s1 (a2t_ (state_to_list A s1 nilC)) s2 C b2. (*/\ equiv_run B C*)
Proof.
  elim; clear.
  - move=> s s' A B _ b H _.
    apply: runb_a2t_expandedb H.
  - 
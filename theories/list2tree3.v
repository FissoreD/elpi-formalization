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

Lemma expand_a2t {u ign1 C s3 bt}: 
  expand u ign1 (a2t_ (state_to_list C s3 bt)) = Failure (a2t_ (state_to_list C s3 bt)).
Proof.
  case: C => //=.
  - move=> A s B.
    rewrite add_ca_deep_cat.
    generalize (state_to_list B s nilC) => L.
    generalize (state_to_list A s3 L) => L1; clear.
    case: L1 => [|[]]//; case: L => //-[]//.
  - move=> A B0 B.
    case X: state_to_list => //=[[sx x] xs].
    case Y: state_to_list => //=[|[sy y] ys].
    - set Z := state_to_list _ _ _.
      case: Z => //=-[]//.
    - set Z := (_ ++ _).
      case: ys Y => //=.
      case: Z => //-[]//.
Qed.

Lemma expanded_a2t_failed {u ign1 s1 bt b A r}:
  expandedb u ign1 (a2t_ (state_to_list A s1 bt)) r b ->
    r = Failed (a2t_ (state_to_list A s1 bt)).
Proof.
  remember (a2t_ _) as A2 eqn:HA2 => H.
  elim: H A s1 bt HA2; clear.
  - move=> s s' A B + C bt ? H2; subst; rewrite expand_a2t//.
  - move=> s1 A B + C bt ? s3; subst; rewrite expand_a2t//; congruence.
  - move=> s s' r A B b + HB IH C bt ? ign2; subst; rewrite expand_a2t//.
  - move=> s s' r A B b + HB IH C bt ? ign2; subst; rewrite expand_a2t//.
Qed.

Lemma expanded_a2t_ign {u ign1 s1 bt b A r} ign2:
  expandedb u ign1 (a2t_ (state_to_list A s1 bt)) r b ->
    (expandedb u ign2 (a2t_ (state_to_list A s1 bt)) r b).
Proof.
  remember (a2t_ _) as A2 eqn:HA2 => H.
  elim: H A s1 bt HA2 ign2; clear.
  - move=> s s' A B + C s3 bt ? H2; subst; rewrite expand_a2t//.
  - move=> s1 A B HA C s2 bt ? s3; subst; apply: expanded_fail.
    rewrite -HA !expand_a2t//.
  - move=> s s' r A B b + HB IH C s1 bt ? ign2; subst; rewrite expand_a2t//.
  - move=> s s' r A B b + HB IH C s1 bt ? ign2; subst; rewrite expand_a2t//.
Qed.

Lemma run_a2t_ign {u s1 s2 C D b2 sIgn1} sIgn2:
  runb u sIgn1 (a2t_ (state_to_list C s1 nilC)) s2 D b2 ->
    runb u sIgn2 (a2t_ (state_to_list C s1 nilC)) s2 D b2.
Proof.
  inversion 1; subst.
  - by have := expanded_a2t_failed H0.
  - apply: run_backtrack; (try eassumption) => //.
    apply: (expanded_a2t_ign sIgn2 H0).
Qed.

(* Lemma titi u s1 X B b1 bt:
  expandedb u s1 (a2t_ X) (Failed B) b1 ->
    exists B', expandedb u s1 (a2t_ (add_ca_deep bt X)) (Failed B') false. *)

Lemma run_success_add_ca_deep {u s s1 B D bt b2 res }:
  success B ->
  runb u s1 (a2t_ (state_to_list B s bt)) res D b2 ->
    exists D0 b0,
      runb u s1 (a2t_ (add_ca_deep bt (state_to_list B s bt))) res D0 b0.
Proof.
  remember (a2t_ _) as a eqn:Ha => + H.
  elim: H B s bt Ha; clear.
  - move=> s1 s2 A B _ b H _ C s3 bt ? sC; subst.
    by have [] := expanded_a2t_ign empty H.
  - move=> s1 s2 s3 A B C D b1 b2 b3 HA HB HC IH ? E s4 bt ? sE; subst.
    do 2 eexists.
    apply: run_backtrack => //.
    -  









Lemma gg u s1 C bt:
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
      move=> /(run_a2t_ign s1).
  


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
    remember (Done _ _) as D eqn:HD.
    {
      elim: H s' B HD; clear.
      - move=> s1 s2 A B H s3 C [??]; subst.
        have [[??] sC]:= expand_solved_same _ H; subst.
        do 2 eexists.
        apply: run_done _ erefl.
          apply: expanded_done.

      -
      -
      -
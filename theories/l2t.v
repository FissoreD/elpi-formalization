From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Fixpoint l2t_alts (a : alts) : state :=
  match a with
  | no_alt => Bot
  | more_alt (s,gl) a => Or Bot s (Or (l2t_goals gl) s (l2t_alts a))
  end
with l2t_goals gl :=
  match gl with
  | no_goals => Top
  | more_goals G gl => And (l2t_G G) Bot (l2t_goals gl)
  end
with l2t_G g :=
  match g with
  | call p c => CallS p c
  | cut _ => CutS
  end. *)

Lemma s2l_nil_is_ko {A s1 bt}:
  (* THIS IS WRONG: a valid state is (OK /\ KO), the list its empty but it is not is_ko *)
  valid_state A ->
  state_to_list A s1 bt = nilC ->
    is_ko A.
Proof.
  elim: A s1 bt => //=.
  - move=> A HA s B HB s1 bt; case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite (state_to_list_dead dA) => //.
      case X: state_to_list => [|[]]//= _.
      rewrite is_dead_is_ko//(HB s nilC)//.
    case X: state_to_list => [|[s2 y]ys]//.
    case Y: state_to_list => [|[s3 z]zs]//.
    rewrite (HA s1 (state_to_list B s nilC))//(HB s nilC)//bbOr_valid//.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA/eqP->{HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure it is s1*)
      move/orP: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case X: state_to_list => //=.
Abort.

Lemma s2l_nil_is_ko u {A s1 bt}:
  valid_state A ->
  state_to_list A s1 bt = nilC ->
    forall s, dead_run u s A.
Proof.
  elim: A s1 bt => //=.
  - move=> ???????? H.
    apply: is_ko_runb _ _ H => //.
  - move=> A HA s B HB s1 bt; case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead => //.
      case X: state_to_list => [|[]]// _ s2 s3 r b H.
      have [[A' [b' H1]]|[B'[b' H1]]]:= run_or_complete _ H.
        by apply: is_dead_runb dA H1.
      by apply: HB H1; eauto.
    case X: state_to_list => [|[]]//.
    case Y: state_to_list => [|[]]// _.
    move=> s2 s3 r b H.
    have [[A' [b' H1]]|[B'[b' H1]]]:= run_or_complete _ H.
      by apply: HA H1; eauto.
    by apply: HB H1; eauto; apply: bbOr_valid bB.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA/eqP->{HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure it is s1*)
      move/orPT: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case X: state_to_list => //= _ s2 s3 r b H1.
        have {}HB := HB _ _ vB X.
        have {}HB0 := HB0 empty no_alt (base_and_ko_valid bB) (base_and_ko_state_to_list bB).
        admit. (*should be ok: but B and B0 fail*)
      have [hd H]:= base_and_state_to_list bB; rewrite H/=.
      case X: state_to_list => //.
      case Y: state_to_list => [|[]]// _ s2 s3 r b H1.
      have {}HB := HB _ _ vB X.
      admit. (*should be ok: A success, B fails and A has no alternatives*)
    case: ifP => [fA bB|fA bB].
      case X: state_to_list => [|[s2 x]xs].
        move=> _ s3 s4 r b H.
        have [sm[r1[b1 H1]]]:= run_and_correct _ H.
        by apply: HA H1; eauto.
      move/orPT: bB => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case Y: state_to_list => //= _ s4 s5 r b H1.
        have {}HB := HB _ _ (base_and_ko_valid bB) Y.
        admit. (*should be ok: A is any, B and B0 (which is equal to B) fail*)
      have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
    case X: state_to_list => [|[s2 x]xs].
      move=> _ s3 s4 r b H.
      have [sm[r1[b1 H1]]]:= run_and_correct _ H.
      by apply: HA H1; eauto.
    have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
Admitted.


(* Lemma state_to_list_success {u A s s1 bt xs}:
  state_to_list A s bt = (s1, nilC) ::: xs ->
    Texists A', expandedb u s A (Done (get_substS s A) A') 0. (*TODO: specify better A'*)
Proof.
  elim: A s s1 bt xs => //=.
  - move=> s s1 _ []// _; eexists; apply: expanded_done => //.
  - move=> s s1 _ []// _; eexists; apply: expanded_step => //; apply: expanded_done => //.
  - move=> A HA s B HB s1 s2 bt xs.
    rewrite add_ca_deep_cat.
    case X: state_to_list => [|[s3 y]ys].
      rewrite cat0s.
      case Y: state_to_list => [|[s4 [|??]]zs]//[??]; subst.
      move: Y; fNilG; fConsA (s1, nilC) zs => Y.
      have {HA HB} [b1 H] := HB _ _ _ _ Y.
Abort. *)

Lemma s2l_add_ca {A s bt1 xs}:
  state_to_list A s bt1 = add_ca_deep bt1 xs ->
    forall bt2, state_to_list A s bt2 = add_ca_deep bt2 xs.
Proof.
  elim: A s bt1 xs => //=.
  - by move=> _ bt1 []//=[]//.
  - by move=> s bt1 []//=[]//a[]//[]//[]//.
  - by move=> s bt []//[]/=a []//=[]//[]//.
  - by move=> _ bt1 []//[]//.
  - by move=> p c s bt []//[]// a []//= []//= p1 c1 []//[]//[]//.
  - move=> s bt []//[]// s1 []// []//= [|[]]//=[]//[|[]]//; case: bt => //=.
Abort.

Definition add_ca_deep_lvl1 (bt:alts) (a: alts) : alts := 
  map (fun '(s,xs) => (s,map (apply_cut (fun ca => add_ca_deep bt ca)) xs)) a.

Lemma split_cat {x1 x2: alts} {F r}:
  x1 ++ x2 = map F r -> Texists p1 p2, p1 ++ p2 = r /\ x1 = map F p1 /\ x2 = map F p2.
Proof.
Admitted.

(* Lemma s2l_add_ca {A s xs bt1}:
  state_to_list A s bt1 = add_ca_deep_lvl1 bt1 xs ->
    forall bt2, state_to_list A s bt2 = add_ca_deep_lvl1 bt2 xs.
Proof.
  (* rewrite /add_ca_deep_lvl1. *)
  elim: A s xs bt1 => //=.
  - by move=> _ [|[]]//=.
  - by move=> s [|[]]//= s1 []//[|[]]//.
  - by move=> s []//[]s1 []//=[]//.
  - by move=> _ []//.
  - by move=> p c s []//= []s1 []//=[]//p1 c1[]//[]//.
  - by move=> s []//[]//=s1 []//= []//= [|[]]// []//[]//.
  - move=> A HA s1 B HB s2 xs bt1 + bt2.
    rewrite !add_ca_deep_cat.
    have:= HA s2 _ (state_to_list B s1 nilC) => /(_ _ _ IsList_alts).
    set X:= state_to_list A _ _.
    have:= HB s1 _ nilC => /(_ _ _ IsList_alts).
    set Z:= state_to_list B _ _.
    move=> {}HB {}HA.
    admit.
  - move=> A HA B0 HB0 B HB s1 xs bt1 + bt2.


Abort. *)

Lemma xx {u A s s1 bt xs}:
  valid_state A ->
  state_to_list A s bt = (s1, nilC) ::: xs ->
  Texists B n,
    runb u s A s1 B n 
    (* /\  *)
    (* state_to_list (odflt Bot B) s bt2 = add_ca_deep bt2 a *)
    .
Proof.
  elim: A s s1 bt xs => //=.
  - move=> s s1 bt [|[]]//= _ [->].
    repeat eexists; by apply: run_done.
  - move=> s s1 bt [|[]]//= _ [->].
    repeat eexists; apply: run_step => //; by apply: run_done.
  - move=> A HA s B HB s1 s2 bt xs.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead//.
      case X: state_to_list => //[[s3 [|??]]ys]//=[??]; subst.
      have [b1[n H]]:= HB _ _ _ _ vB X.
      repeat eexists.
      have [r[{}HB ?]]:= run_ko_left2 _ s1 (is_dead_is_ko dA) H; subst.
      rewrite dA in HB.
      eauto.
    rewrite add_ca_deep_cat.
    case X: state_to_list => [|[s3 [|??]]ys]//.
      case Y: state_to_list => //[[s3 [|??]]ys]//=[??]; subst.
      have [B'[n{}HB]] := HB _ _ _ _ (bbOr_valid bB) Y.
      have H := s2l_nil_is_ko u vA X s1.
      have:= H empty (Some A) n.
      (* this should? be ok: A \/ B with A fail and run B, 
         attention: if A has a superficial cut is B cut away? *)
      (* That is: can I have: (! /\ fail) \/ B*)
      (* It should not be a valid state! *)
      (* Therefore, in a lemma like  *)
      admit.
    rewrite /=cat_cons => -[??]; subst.
    have [A'[n H1]] := HA _ _ _ _ vA X.
    have [r' [{}H1]]:= run_or_correct_left _ s B H1.
    repeat eexists; eauto.
  - move=> A HA B0 HB0 B HB s1 s2 bt xs /and5P[_ vA _].
    case: ifP => /= [sA vB |sA /eqP -> {HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure of subst s1*)
      move=> /orPT []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        rewrite make_lB01_empty2 => H.
        have [r[n {}HB]] := HB _ _ _ _ vB H.
        admit. (*this is ok: A /\ B with success A and run B*)
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=make_lB01_empty2.
      case X: state_to_list => [|[sy [|??]]ys]//.
        case W: next_alt => //=[A'].
        case Y: state_to_list => //[[sw [|??]] ws]//=.
        case: hd H X => //H X[??]; subst.
        have:= HB0 empty empty no_alt no_alt (base_and_valid bB). (*TODO: not sure empty and no_alt*)
        rewrite H=> /(_ erefl) [r[n {}HB0]].
        admit. (*this is ok: A /\ B -> A success, B fails, 
                 but next_alt A exists and run B04*)
      move=> [??]; subst.
      have [r[n {}HB]] := HB _ _ _ _ vB X.
      (* this is ok: A /\ B, A success and run B *)
      admit.
    case X: state_to_list => //[[sy y]ys].
    case: ifP => [fA|fA bB].
      move=> /orPT []bB; last first.
        rewrite !base_and_ko_state_to_list//=.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=H/make_lB01 map_cons.
      case: y X => //; case: hd H => //H X [??]; subst.
      have [r[n {}HA]] := HA _ _ _ _ vA X.
      have [r'[n' {}HB]] := HB _ _ _ _ (base_and_valid bB) (H nilC empty).
      admit. (*this is ok: A /\ B with run A and run B and B0 = B*)
    have [hd H]:= base_and_state_to_list bB.
    rewrite H/=H/make_lB01 map_cons.
    case: y X => //; case: hd H => //H X [??]; subst.
    have [r[n {}HA]] := HA _ _ _ _ vA X.
    have [r'[n' {}HB]] := HB _ _ _ _ (base_and_valid bB) (H nilC empty).
    admit. (*this is ok: A /\ B with run A and run B and B0 = B*)
Admitted.

Search runb And.
    

Lemma two' {u s s1} {alts alts_left : alts} {andg : goals}  : 
  nur u s andg alts s1 alts_left -> forall t bt,
  valid_state t ->
  state_to_list t s bt = add_ca_deep bt ((s,andg) ::: alts) -> 
  Texists t1 n,
    runb u s t s1 t1 n
      (* /\ state_to_list (odflt Bot t1) s1 bt1 = add_ca_deep bt1 alts_left  *)
    .
Proof.
  elim; clear.

  - move=> s a t bt1 /= vt Ht.
    apply: xx vt Ht.
  - move=> s1 s2 a ca r gl H IH t bt H1.
    admit.
  - admit.
  - admit.
Admitted.


Lemma two'' {u s s1} {alts alts_left : alts} {andg : goals}  : 
  nur u s andg alts s1 alts_left -> forall t,
  valid_state t ->
  state_to_list t s nilC = ((s,andg) ::: alts) -> 
  Texists t1 n,
  (* state_to_list (odflt Bot t1) s1 nilC = alts_left /\  *)
  runb u s t s1 t1 n.
move=> H t vt H1.
have:= [elaborate (two' H t nilC vt)].
by rewrite !add_ca_deep_empty1; auto.
Qed.




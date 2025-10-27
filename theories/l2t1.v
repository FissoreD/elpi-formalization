From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Fixpoint will_ko A :=
  match A with
  | Dead | Bot => true
  | CutS | CallS _ _ | OK | Top => false
  | Or A _ B => 
    will_ko A && will_ko B
  | And A B0 B => 
    if success A then 
      will_ko B && (((next_alt true A) == None) || will_ko B0)
    else
    will_ko A || (will_ko B &&  will_ko B0)
  end.

Fixpoint will_succeed A :=
  match A with
  | Top | OK => true
  | CutS | CallS _ _ | Dead | Bot => false
  | Or A _ B => 
    if will_ko A then will_succeed B 
    else will_succeed A
  | And A B0 B =>
    will_succeed A && 
    if failed A then will_succeed B0
    else will_succeed B
  end.

Fixpoint will_cut A :=
  match A with
  | CutS => true
  | Top | OK | CallS _ _ | Dead | Bot => false
  | Or A _ B => 
    if will_ko A then will_cut B 
    else will_cut A
  | And A B0 B =>
    if success A then will_cut B
    else
      if failed A then
        (* THIS IS WRONG: may be will_cut A... *)
        if will_succeed A then will_cut B0
        else will_cut A
      else will_cut A
  end.

Lemma is_ko_will_ko {A}:
  is_ko A -> will_ko A.
Proof.
  elim: A => //=.
  - by move=> A HA _ B HB /andP[/HA]->/HB->.
  - by move=> A HA B0 _ B HB H; rewrite is_ko_success//HA//.
Qed.

Lemma will_koP {A s1 bt}:
  valid_state A ->
  state_to_list A s1 bt = nilC ->
    will_ko A.
Proof.
  elim: A s1 bt => //=.
  - move=> A HA s B HB s1 bt.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead//cat0s.
      case X: state_to_list => [|[]]//=.
      by rewrite (HB s nilC)// is_ko_will_ko //is_dead_is_ko.
    case X: state_to_list => [|[]]//=.
    case Y: state_to_list => [|[]]//=.
    rewrite (HA _ _ _ X)//(HB _ _ _ Y)//bbOr_valid//.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB|sA/eqP-> {B0 HB0}].
      rewrite (success_state_to_list empty)//=.
      move/orPT: bB => []bB; last first.
        rewrite base_and_ko_state_to_list//=make_lB01_empty2 => H.
        by rewrite (HB _ _ vB H) (is_ko_will_ko (base_and_ko_is_ko bB)) orbT.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/= make_lB01_empty2.
      case X: state_to_list => //.
      case Y: state_to_list => [|[]]//= _.
      rewrite (HB _ _ _ X)//.
      move: Y; case Z: next_alt => //=[A'].
      have [s'[x[xs]]]:= failed_state_to_list (valid_state_next_alt vA Z) (next_alt_failed Z) empty bt.
      by move=> ->.
    case: ifP => [fA bB|fA bB].
      case X: state_to_list => [|[sy y]ys].
        by rewrite (HA _ _ _ X).
      move/orPT: bB => []bB; last first.
        rewrite !base_and_ko_state_to_list//=.
        by rewrite (is_ko_will_ko (base_and_ko_is_ko bB)) orbT.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/=!H/=/make_lB01 map_cons//.
    case X: state_to_list => [|[sy y]ys].
      by rewrite (HA _ _ _ X).
    have [hd H]:= base_and_state_to_list bB.
    rewrite !H/=!H/=/make_lB01 map_cons//.
Qed.

Lemma will_koP1 {A s1 bt}:
  valid_state A ->
  will_ko A ->
  state_to_list A s1 bt = nilC.
Proof.
  elim: A s1 bt => //=.
  - move=> A HA s B HB s1 bt.
    case: ifP => [dA vB|dA /andP[vA bB]]/andP[wA wB].
      by rewrite state_to_list_dead//= HB//.
    by rewrite HA//HB//bbOr_valid.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP =>/= [sA vB bB /andP[wB]|sA /eqP->{B0 HB0}].
      rewrite (success_state_to_list empty)//=HB//=.
      move=> /orPT[]; last first.
        by move=> /HB0->//; rewrite bbAnd_valid.
      move/orPT: bB=>[]bB; last first.
        by rewrite base_and_ko_state_to_list//=.
      move=> /eqP H1.
      have [hd H]:= base_and_state_to_list bB.
      by rewrite H/= HB//H1//.
    move=> H /orPT[].
      by move=> /HA->.
    have vB: valid_state B.
      by move: H; case: ifP => [_ /bbAnd_valid| _ /base_and_valid]//.
    move=> /andP[wB _].
    case X: state_to_list => [|[sx x]xs]//.
    rewrite !HB//=.
Qed.

Lemma will_cutP {A s s2 bt ca gl a}:
  valid_state A ->
  state_to_list A s2 bt = (s, (cut ca) ::: gl) ::: a ->
  will_cut A.
Proof.
  elim: A s s2 ca gl a bt => //=.
  - move=> A HA s B HB s1 s2 ca gl a bt.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead//=.
      rewrite is_ko_will_ko ?is_dead_is_ko//.
      case X: state_to_list => [|[sx x]xs]//=; case: x X => //-[]//=ca' g/= X [????]; subst.
      by apply: HB X.
    case X: state_to_list => [|[sx [|[??|ca'] gs]]xs]//.
      rewrite (will_koP vA X).
      case Y: state_to_list => [|[sy [|[??|ca'] gs]] a']//=[????]; subst.
      by apply: HB (bbOr_valid bB) Y.
    move=> [????]; subst.
    rewrite (HA _ _ _ _ _ _ _ X)//.
    case: ifP => // H.
    rewrite will_koP1// in X.
  - move=> A HA B0 _ B HB s1 s2 ca gl a bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB|sA /eqP->{B0}].
      rewrite (success_state_to_list empty)//=.
      move/orPT: bB=>[]bB; last first.
        rewrite base_and_ko_state_to_list//=make_lB01_empty2 => H.
        by apply: HB H.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/= make_lB01_empty2.
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


Lemma valid_state_nil_run {u A s s1 bt xs}:
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


(* HYP: A is not failed *)
Fixpoint next_cut (A: state) :=
  match A with
  | Or A s B =>
    (* HERE THE PROBLEM: should not next_cut on is_ko but on is_dead A *)
    if is_ko A then (false, Or (if is_dead A then A else dead1 A) s (next_cut B).2)
    else 
      let '(b1, A') := next_cut A in
      (false, Or A' s (if b1 then cutr B else B))
  | And A B0 B =>
    if success A then
      let '(c, B') := next_cut B in
      (c, And (if c then cutl A else A) (if c then cutl B0 else B0) B')
    else
    let '(b1, A') := next_cut A in
    (b1, And A' B0 B)
    (* IF the input is (KO \/ Top) /\_Cut  \/ blibli
       next_alt should be (KO\/OK) /\_Cut \/ OK

       IF the input is (KO \/ p) /\_Cut \/ blibli
       next_alt should be (KO\/OK) /\_Cut \/ OK
    *)
    (* (b1, And A' B0 (if failed A then B0 else B)) *)
  | CutS => (true, OK)
  | Top | OK | CallS _ _ | Dead | Bot => (false, A)
  end.

  Lemma next_cut_success {A B}: success A -> next_cut A = B -> success B.2.
Proof.
  move=> + <- {B}; elim: A => //=.
  - move=> A HA s B HB; case: ifP => [dA sB|dA sA].
      rewrite is_dead_is_ko//=dA HB//.
    rewrite success_is_ko//.
    move: HA; case: next_cut => //=b A' /(_ sA) sA'.
    rewrite success_is_dead//.
  - move=> A + B0 _ B + /andP[sA sB] => - /(_ sA) + /(_ sB).
    case: next_cut => //=b A' sA'.
    rewrite sA.
    case: next_cut => //=b' B' ->.
    by rewrite fun_if success_cut sA if_same.
Qed.

Lemma next_alt_is_and {A B}:
  is_and A -> next_cut A = B -> is_and B.2.
Proof.
  move=> + <- {B}; elim: A => //-[]//=.
  - move=> _ B HB C HC /HC; case: next_cut => //= a b; rewrite if_same//.
  - move=> A s B _ C HC D HD /[dup] aD /HD; case: next_cut => //= b E aE.
    (repeat case: ifP => //=).
      case: next_cut => //=b' F; case: ifP => //.
    case: next_cut => //=b' F; case: ifP => //.
  - move=> A B0 B _ C HC D HD/[dup] aD /HD.
    case: next_cut => //= b E.
    case: next_cut => //=??.
    case: next_cut => //=??.
    repeat case: ifP => //=.
Qed.

Lemma next_alt_is_or {A B}:
  is_or A -> next_cut A = B -> is_or B.2.
Proof.
  move=> + <- {B}; elim: A => //-[]//=.
  - move=> A s B _ C s1 D _.
    repeat case: ifP => //.
    case: next_cut => //.
  - move=> A B0 B _ s1 D HD _.
    repeat case: ifP => //.
    case: next_cut => // ???.
    case: next_cut => //.
Qed.

Lemma next_cut_valid {A B}: 
  valid_state A -> next_cut A = B -> valid_state B.2.
Proof.
  move=> + <-; clear B.
  elim: A => //=.
  - move=> A HA s B HB.
    case: ifP => [dA vB|dA /andP[vA bB]].
      by rewrite is_dead_is_ko//=dA HB.
    case: ifP => kA/=.
      by rewrite is_dead_dead HB//bbOr_valid.
    move: (HA vA).
    case X: next_cut => [b A']/= vA'.
    rewrite valid_state_dead1//=vA'.
    case: ifP; rewrite//= bbOr_cutr//.
  - move=> A HA B0 _ B HB /and5P[oA vA aA].
    case: ifP => /=[sA vB bB|sA /eqP->{B0}].
      move: (HA vA) (HB vB) => {HA HB}.
      case X: next_cut => //= [b A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      rewrite (fun_if success) success_cut if_same.
      have sA' := next_cut_success sA X.
      rewrite (fun_if is_or) (fun_if valid_state) (fun_if bbAnd)/=.
      rewrite valid_state_cut// vB'.
      rewrite (next_alt_is_and aA Y) bB /bbAnd bbAnd_cutl// orbT.
      have /= oA' := next_alt_is_or oA X.
      by rewrite is_or_cutl//sA/=vA oA if_same//.
    case: ifP => fA bB.
      have {HB} :=  HB (bbAnd_valid bB).
      have {HA} :=  HA vA.
      case X: next_cut => //= [bA A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      have /= oA':= next_alt_is_or oA X.
      have /= aB':= next_alt_is_and aA Y.
        rewrite vA' oA' bbAnd_is_and// bbAnd_valid// eqxx if_same//=bB.
        admit.
    have {HB} :=  HB (base_and_valid bB).
    have {HA} :=  HA vA.
    case X: next_cut => //= [bA A'].
    case Y: next_cut => //= [b' B'] vA' vB'.
    have /= oA':= next_alt_is_or oA X.
    have /= aB':= next_alt_is_and aA Y.
    by rewrite vA' oA' base_and_is_and// base_and_valid// eqxx if_same//=bB /bbAnd bB if_same.
Abort.

Lemma next_cut_valid {A B}: 
  failed A = false -> valid_state A -> next_cut A = B -> valid_state B.2.
Proof.
  move=> ++ <-; clear B.
  elim: A => //=.
  - move=> A HA s B HB.
    case: ifP => [dA fB vB|dA fA /andP[vA bB]].
      by rewrite is_dead_is_ko//=dA HB.
    case: ifP => kA/=.
      by rewrite is_ko_failed in fA.
    move: (HA fA vA).
    case X: next_cut => [b A']/= vA'.
    rewrite valid_state_dead1//=vA'.
    case: ifP; rewrite//= bbOr_cutr//.
  - move=> A HA B0 _ B HB + /and5P[oA vA aA].
    case fA: failed => //=.
    case: ifP => /=[sA fB vB bB|sA _ /eqP->{B0}].
      move: (HA fA vA) (HB fB vB) => {HA HB}.
      case X: next_cut => //= [b A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      rewrite (fun_if success) success_cut if_same.
      have sA' := next_cut_success sA X.
      rewrite (fun_if is_or) (fun_if valid_state) (fun_if bbAnd)/=.
      rewrite valid_state_cut// vB'.
      rewrite (next_alt_is_and aA Y) bB /bbAnd bbAnd_cutl// orbT.
      have /= oA' := next_alt_is_or oA X.
      by rewrite is_or_cutl//sA/=vA oA if_same//.
    move=> bB.
    have {HB} :=  HB (base_and_failed bB) (base_and_valid bB).
    have {HA} :=  HA fA vA.
    case X: next_cut => //= [bA A'].
    case Y: next_cut => //= [b' B'] vA' vB'.
    have /= oA':= next_alt_is_or oA X.
    have /= aB':= next_alt_is_and aA Y.
    by rewrite vA' oA' base_and_is_and// eqxx base_and_valid///bbAnd bB !if_same.
Qed.


(* Lemma next_cut_s2l {b A A' s bt s1 ca gl a}:
  failed A = false -> valid_state A ->
    clean_ca_suffix bt (state_to_list A s bt) = (s1, (cut ca) ::: gl) ::: a ->
    next_cut A = (b, A') ->
      clean_ca_suffix bt (state_to_list A' s bt) = (s1, gl) ::: ca.
Proof.
  elim: A b A' s bt s1 ca gl a => //.
  - 
Admitted. *)


Lemma two'' {u s1 s2} {alts alts_left : alts} {andg : goals}  : 
  nur u s1 andg alts s2 alts_left -> forall s t,
  valid_state t ->
  state_to_list t s nilC = ((s1,andg) ::: alts) -> 
  Texists t1 n,
  (* state_to_list (odflt Bot t1) s1 nilC = alts_left /\  *)
  runb u s t s2 t1 n.
elim; clear.
- move=> s a s1 A vA H.
  apply: valid_state_nil_run vA H.
- move=> s s1 a ca r gl ELPI IH s2 A vA H.
  (* TODO: I need to find the state A' to satisfy the hyp in IH... *)



move=> H t vt H1.
have:= [elaborate (two' H t nilC vt)].
by rewrite !add_ca_deep_empty1; auto.
Qed.


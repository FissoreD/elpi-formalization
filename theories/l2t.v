From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

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
      rewrite (success_state_to_list s1)//=.
      move/orPT: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case X: state_to_list => //= _ s2 s3 r b H1.
        have {}HB := HB _ _ vB X.
        have {}HB0 := HB0 empty no_alt (base_and_ko_valid bB) (base_and_ko_state_to_list bB).
        have [sm[r1[b1[H2 [b2[r2 [H3|[sm' H3]]]]]]]] := run_and_correct _ H1.
          by apply: HB; eauto.
        by apply: HB0; eauto.
      have [hd H]:= base_and_state_to_list bB; rewrite H/=.
      case X: state_to_list => //.
      case Y: state_to_list => [|[]]// _ s2 s3 r b H1.
      have {}HB := HB _ _ vB X.
      have [sm[r1[b1[H2 [b2[r2 [H3|[sm' H3]]]]]]]] := run_and_correct _ H1.
        by apply: HB H3.
      admit. (*should be ok: A success, B fails and A has no alternatives*)
    case: ifP => [fA bB|fA bB].
      case X: state_to_list => [|[s2 x]xs].
        move=> _ s3 s4 r b H.
        have [sm[r1[b1 [H1 H2]]]]:= run_and_correct _ H.
        by apply: HA H1; eauto.
      move/orPT: bB => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case Y: state_to_list => //= _ s4 s5 r b H1.
        have {}HB := HB _ _ (base_and_ko_valid bB) Y.
        have [sm[r1[b1[H2 [b2[r2 [H3|[sm' H3]]]]]]]] := run_and_correct _ H1.
          by apply: HB H3.
        by apply: HB H3.
      have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
    case X: state_to_list => [|[s2 x]xs].
      move=> _ s3 s4 r b H.
      have [sm[r1[b1 [H1 H2]]]]:= run_and_correct _ H.
      by apply: HA H1; eauto.
    have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
Admitted.

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


Lemma add_ca_deep_map bt1 xs:
  map (fun '(s, xs0) => (s, (add_ca_deep_goals bt1 xs0))) xs =
    add_ca_deep bt1 xs
with add_ca_deep_goals_map bt1 x:
  map (add_ca_deep_g bt1) x = add_ca_deep_goals bt1 x.
Proof.
  - case: xs => [|[sx x] xs]; [reflexivity|].
    by rewrite !map_cons add_ca_deep_map /=.
  - case: x => [|g gs]; [reflexivity|].
    by rewrite map_cons add_ca_deep_goals_map.
Qed.

Fixpoint clean_ca_suffix (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, clean_ca_goals_suffix bt xs) ::: (clean_ca_suffix bt tl)
  end
with clean_ca_goals_suffix bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (clean_ca_G_suffix bt hd) ::: (clean_ca_goals_suffix bt tl)
  end
with clean_ca_G_suffix bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut ((take (size ca - size bt) (clean_ca_suffix bt ca)))
  end.

Lemma clean_ca_suffix_cat {bt L1 L2}:
  clean_ca_suffix bt (L1 ++ L2) = clean_ca_suffix bt (L1) ++ clean_ca_suffix bt L2.
Proof. by elim: L1 bt L2 => //= [[s g] gs] IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_goals_suffix_cat {bt L1 L2}:
  clean_ca_goals_suffix bt (L1 ++ L2) = clean_ca_goals_suffix bt (L1) ++ clean_ca_goals_suffix bt L2.
Proof. by elim: L1 bt L2 => //= g gs IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_add_ca {bt1 L}:
  clean_ca_suffix bt1 (add_ca_deep bt1 L) = L
with clean_ca_goals_add_ca_goal bt1 x:
  clean_ca_goals_suffix bt1 (add_ca_deep_goals bt1 x) = x.
Proof.
  - by case: L => /=//-[s1 x] xs/=; rewrite clean_ca_add_ca clean_ca_goals_add_ca_goal.
  - case: x => /=//g gs; rewrite clean_ca_goals_add_ca_goal.
    case: g => //= a.
    congr ((cut _) ::: _).
    rewrite size_cat addnK clean_ca_suffix_cat clean_ca_add_ca.
    by rewrite take_size_cat// size_add_ca_deep.
    Guarded.
Qed.

Lemma clean_ca_suffix_nil {L}: clean_ca_suffix nilC L = L
with clean_ca_goals_nil {L}: clean_ca_goals_suffix nilC L = L
with clean_ca_G_nil {L}: clean_ca_G_suffix nilC L = L.
Proof.
  - case: L => /=// [[sx x]xs]; rewrite clean_ca_goals_nil clean_ca_suffix_nil//.
  - case: L => /=// g gs; rewrite clean_ca_goals_nil clean_ca_G_nil//.
  - case: L => /=// ca; rewrite clean_ca_suffix_nil subn0 take_size//.
Qed.


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
      have {}HB:= run_ko_left2 _ s1 (is_dead_is_ko dA) H; subst.
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
      (* That is: can I have: (! /\ fail) \/ B ?*)
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

Lemma add_ca_deep_inj {bt a1 a2}:  
  add_ca_deep bt a1 = add_ca_deep bt a2 -> a1 = a2
with add_ca_deep_goals_inj {bt g1 g2}:
  add_ca_deep_goals bt g1 = add_ca_deep_goals bt g2 -> g1 = g2
with add_ca_deep_g_inj {bt g1 g2}:
  add_ca_deep_g bt g1 = add_ca_deep_g bt g2 -> g1 = g2.
Proof.
  - case: a1 => [|[]].
      case: a2 => [|[]]//.
    case: a2 => [|[]]//s1 x xs s2 y ys[?] /add_ca_deep_goals_inj ? /add_ca_deep_inj ?; by subst.
  - case: g1; case: g2 => //= x xs y ys []/add_ca_deep_g_inj? /add_ca_deep_goals_inj?; by subst.
  - by case: g1; case: g2 => //xs ys [] /append_sameR /add_ca_deep_inj->.
Qed.

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


Lemma next_cut_s2l u {A B s bt s1 ca gl a}:
  failed A = false -> valid_state A ->
    clean_ca_suffix bt (state_to_list A s bt) = (s1, (cut ca) ::: gl) ::: a ->
    next_cut A = B ->
      clean_ca_suffix bt (state_to_list B.2 s bt) = (s1, gl) ::: ca /\
      if B.1 then expand u s A = CutBrothers s1 B.2
      else expand u s A = Expanded s1 B.2.
Proof.
  elim: A B s bt s1 ca gl a => //=.
  - move=> [b B] s bt s1 c gl a _ _ [????][??]; subst => //.
  - move=> A HA s B HB [b C] s1 bt s2 c gl a.
    case: ifP => [dA fB vB|dA fA /andP[vA bB]].
      rewrite state_to_list_dead => //=.
      rewrite is_dead_is_ko//=.
      case X: state_to_list => [|[sx [|[p' c'|ca'] ys]] xs]//[????][??]; subst.
      case Y: next_cut => [b' B']/=.
      rewrite state_to_list_dead//=.
      rewrite -(@clean_ca_suffix_nil (state_to_list B s nilC)) in X.
      have /=[{}HB H] := HB _ _ _ _ _ _ _ fB vB X Y.
      rewrite clean_ca_suffix_nil in HB.
      rewrite HB/= size_cat addnK clean_ca_suffix_cat take_size_cat//; last first.
        by rewrite clean_ca_add_ca size_add_ca_deep.
      split => //; case: b' H Y => //->//.
    have [s'[x[xs H]]] := [elaborate failed_state_to_list vA fA s1 (state_to_list B s nilC)].
    rewrite H/=; case: x H => //[[p c'|ca']gs]// H [????]; subst.
    rewrite failed_is_ko//; case X: next_cut => //[b' A'][??]; subst.
    have {HA HB} := HA _ s1 (state_to_list B s no_alt) _ _ _ _ fA vA _ X.
    rewrite H/= => /(_ _ _ _ _ erefl).
    fNilA.
    case: b' X => // X [+H1].
      have [x[tl[H2 [H3 H4]]]]:= [elaborate s2l_CutBrothers _ s1 (state_to_list B s nilC) vA H1].
      move: H;rewrite !H2 => -[????]; subst; rewrite sub0n take0.
      rewrite !H3/= => -[Hx]; rewrite Hx state_to_list_cutr_empty//?bbOr_valid//.
      rewrite cat0s// subnn take0 add_ca_deep_empty2; repeat split.
      rewrite H1//.
    have [[[Hx fA' ?]]] := s2l_Expanded_cut _ vA H1 H; subst.
    move=> []Hy; rewrite Hy/=size_cat addnK clean_ca_suffix_cat !clean_ca_add_ca take_size_cat ?size_add_ca_deep//.
      move=> []Hz.
      have:= [elaborate f_equal size Hz].
      rewrite size_cons; lia.
    move=> Hz; repeat split.
    by rewrite H1.
  - move=> A HA B0 _ B HB [b C] s bt s1 ca gl a + /and5P[_ vA _].
    case fA: failed => //=.
    case: ifP => //=[sA fB vB bB|sA _ /eqP-> {B0} bB]; subst => /=.
      case Y: next_cut => [b' B']/=.
      rewrite (success_state_to_list empty)//=.
      move/orPT: bB => []bB; last first.
        rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H [??]; subst => /=.
        have /=[{}HB H1] := HB _ _ _ _ _ _ _ fB vB H Y.
        rewrite succes_is_solved//.
        case: b Y H1 => //= Y H1; rewrite H1; repeat split.
          have vcl := valid_state_cut vA.
          rewrite -success_cut in sA. 
          rewrite (success_state_to_list empty)//=.
          have bcl := base_ko_and_cutl bB.
          rewrite base_and_ko_state_to_list//=.
          by rewrite make_lB01_empty2 ges_subst_cutl HB.
        rewrite (success_state_to_list empty)//=.
        by rewrite base_and_ko_state_to_list//=  make_lB01_empty2 HB.
      have [h H]:= base_and_state_to_list bB.
      rewrite H/= make_lB01_empty2/=.
      rewrite clean_ca_suffix_cat.
      set ml:= make_lB0 _ _.
      have [s2[x[xs H1]]] := [elaborate failed_state_to_list vB fB (get_substS s A) (ml ++ bt)].
      rewrite H1/=.
      case: x H1 => //[[]]// ca' gs H1 [????][??]; subst.
      have:= HB _ (get_substS s A) (ml ++ bt) _ _ _ _ fB vB _ Y.
      move=> /(_ _ IsList_alts).
      rewrite H1/= => /(_ _ _ _ _ erefl) [{}HB H2].
      rewrite succes_is_solved//=.
      case: b Y H2 => Y H2; rewrite H2; repeat split.
        have vcl := valid_state_cut vA.
        rewrite -success_cut in sA. 
        rewrite (success_state_to_list empty)//=.
        have bcl := base_and_cutl bB.
        rewrite base_and_ko_state_to_list//=.
        rewrite make_lB01_empty2 ges_subst_cutl.
        replace bt with (ml ++ bt) by admit.
        rewrite HB//.
      rewrite (success_state_to_list empty)//=.
      rewrite H/=.
      rewrite -/ml make_lB01_empty2 clean_ca_suffix_cat.
      admit.
    case Y: next_cut => [b' A']/= + [??]; subst => /=.
    case Z: (next_cut B) => [b'' B'].
    have [s2[x[xs H]]] := failed_state_to_list vA fA s bt.
    have [h H1]:= base_and_state_to_list bB.
    rewrite H/=H1/=!H1/=.
    case: x H => //=.
      move=> H.
      case: h H1 => //-[]//ca' gs H1[????]; subst.
      have:= HB _ s no_alt _ _ _ _ (base_and_failed bB) (base_and_valid bB) _ Z.
      rewrite H1 => /= /(_ _ _ _ _ erefl).
      move=> [].
Admitted.


Lemma two' {u s1 s2} {alts alts_left : alts} {andg : goals}  : 
  nur u s1 andg alts s2 alts_left -> forall s t,
  valid_state t ->
  (state_to_list t s nilC) = ((s1,andg) ::: alts) -> 
  Texists t1 n,
    runb u s t s2 t1 n
      (* /\ state_to_list (odflt Bot t1) s1 bt1 = add_ca_deep bt1 alts_left  *)
    .
Proof.
  elim; clear.
  - move=> s a A s1 vA /= Ht.
    (* rewrite (s2l_clean_ca vt erefl) => Ht. *)
    apply: valid_state_nil_run vA Ht.
    {
      move=> s1 s2 a ca r gl ELPI IH s A vA H.
      case fA: (failed A). (*here we have some Bot before reaching cut*)
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_state_to_list vA fA nA) in H.
        case X: (next_cut A') => [b A''].
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_state_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' X.
        rewrite (failed_next_alt_some_state_to_list _ vA fA nA) in H.
        rewrite -(@clean_ca_suffix_nil (state_to_list A' s nilC)) in H.
        have [H1 H2] := next_cut_s2l u fA' vA' H X.
        rewrite clean_ca_suffix_nil/= in H1.
        have /= [t1[n {}IH]] := IH _ _ vA'' H1.
        case: b X H2 => /= X H2.
          repeat eexists.
          apply: run_fail nA _.
            apply: failed_expand fA.
          apply: run_cut H2 IH.
        repeat eexists.
        apply: run_fail nA _.
          apply: failed_expand fA.
        apply: run_step H2 IH.
      case X: (next_cut A) => [b A'].
      rewrite -(@clean_ca_suffix_nil (state_to_list A s nilC)) in H.
      have /= [H1 H2] := next_cut_s2l u fA vA H X.
      have /= vA':= next_cut_valid fA vA X.
      rewrite (clean_ca_suffix_nil) in H1.
      have /= [t1[n {}IH]] := IH _ _ vA' H1.
      case: b X H2 => /= X H2.
        repeat eexists.
        apply: run_cut H2 IH.
      repeat eexists.
      apply: run_step H2 IH.
    }
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
by have:= [elaborate (two' H _ t vt H1)].
Qed.




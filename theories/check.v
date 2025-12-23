From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import ctx tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap.
From det Require Import tree_valid_cut.


Require Import FunInd.
Functional Scheme expand_ind := Induction for step Sort Prop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope fset_scope.

Notation "A <= B" := (minD A B = A).
Notation "B <= A" := (minD A B = B).
Notation "A <== B" := (minD A B == A) (at level 1000).
Notation "B <== A" := (minD A B == B) (at level 1000).
(* Notation "A <= B" := (min A B = A).
Notation "B <= A" := (min A B = B). *)
(* Notation "A <= B" := (minD A B == A).
Notation "B <= A" := (minD A B == B).
Notation "A <= B" := (min A B == A).
Notation "B <= A" := (min A B == B). *)

Ltac foo tcA IH := by move=> [<-<-]; case tcA: tc_tree_aux => [BA BI];
  (try rewrite maxD_comm in tcA); rewrite IH tcA maxD_refl merge_refl.

(* Lemma all_det_nfa_big_and {sP sV l r} p: 
  (check_atoms sP sV l r) = tc_tree_aux sP sV (big_and p l) r.
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [dA sVA].
  case: A X => //=[|c]; rewrite is_ko_big_and.
  case YY : A X => //=[|c]; first by foo tcA IH.
  rewrite/check_callable.
  case X: check_tm => //[d b]//=.
  case: d X => /=[[|d]|m f a] C; cycle 1; [|foo tcA IH..].
  destruct b; last by foo tcA IH.
  case CH: get_callable_hd_sig => [v|]; last by foo tcA IH.
  rewrite (@maxD_comm r) -maxD_assoc maxD_refl.
  case dt: tc_tree_aux => [[]][??]; subst; rewrite merge_refl;
  by rewrite IH dt maxD_refl.
Qed. *)

Definition good_assignment sP SV vk :=
  let (S, b1) := check_tm sP empty_ctx vk in
  let SS := if b1 then S else weak S in
  compat_type SS SV && incl SS SV.

Lemma incl_good_assignment sP s s' v :
  incl s s' ->
  compat_type s s' ->
  good_assignment sP s v ->
  good_assignment sP s' v.
move=> i c; rewrite /good_assignment; case E: check_tm => [sk []]; rewrite ?valPE/=.
  move=> /andP[comp_sk isk]; rewrite (compat_type_trans comp_sk)  //.
  by rewrite (incl_trans isk) // in2_more_precise.
 move=> /andP[comp_sk isk]; rewrite (compat_type_trans comp_sk)  //.
  by rewrite (incl_trans isk) // in2_more_precise.
Qed.



Definition sigP (sP:sigT) (s: sigS) (sV: sigV) :=
  (* (domf s `<=` domf sV) && *)
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then good_assignment sP SV vk
    else SV == weak SV].

Lemma sigP_more_precise sP s N O:
  more_precise N O -> sigP sP s N -> sigP sP s O.
Proof.
  move=> MP /forallP H; apply/forallP=> -[k kO].
  have kN := fsubsetP (more_precise_sub MP) k kO.
  have /={H} := H (Sub k kN).
  have [kS|bkS] := fndP.
    rewrite !valPE/=; apply: incl_good_assignment (in2_more_precise MP _ _) _.
    by rewrite compat_type_comm more_precise_same_type.
  rewrite ?valPE/= => /eqP def_N; have ino := in2_more_precise MP kO kN.
  have /comp_weak wON := more_precise_same_type MP kO kN.
  by rewrite -eq_incl weak_incl wON -def_N ino.
Qed.

(* Lemma next_alt_sigP {u sP sV A r s d} ... *)
Lemma expand_sigP u sP sV A r s d : (* rename step *)
  closed_inT sV A ->
    sigP sP s sV ->
        step u s A = r -> 
        let A' := get_tree r in
        let s' := get_substS s A' in
        let (_,sV') := tc_tree_aux sP sV A' d in
           sigP sP s' sV'.
Proof.
  move=> ++ <-.
  elim: A u sP sV s => //.
  (* - move=> p c u sP sV s clo /forallP/(_ (Sub (_:V) _))  H; apply/forallP=> -[k kV].
    move: (H k kV); rewrite valPE/= {H}.
    have [kS|nkS] := fndP.
      admit. (* more instantiated, interesting branch *)
    have [kS'|nkS'] := fndP.
      admit. (* assigned, interesting branch *)
    by []. untouched *)
Admitted.

Axiom deref_rigid: forall {s t rc p},
  tm2RC (deref s (Callable2Tm t)) = Some rc ->
    get_tm_hd (Callable2Tm (t)) = inr (inl p) ->
      get_tm_hd (Callable2Tm (RCallable2Callable rc)) = inr (inl p).

Lemma get_sig_hd_strong a1:
  b (get_sig_hd (strong a1)) = strong (b (get_sig_hd a1))
with get_sig_hd_weak a1:
  b (get_sig_hd (weak a1)) = weak (b (get_sig_hd a1)).
Proof. all: case: a1 => [[|[]]|[]]//=. Qed.

Lemma check_tm_func sP O t b1 s:
  check_tm sP O t = (s, b1) ->
    match get_tm_hd_sig sP O t with
    | None => true
    | Some X => incl (b (get_sig_hd X)) (b(get_sig_hd s))
    end.
Proof.
  rewrite /get_tm_hd_sig.
  elim: t s b1 => //=.
  - move=> k s b1; case: fndP => [kf [<-] _| ]//.
  - move=> _ s _ [<- _]//.
  - move=> v s b1; case: fndP => [kf[<-]|]//.
  - move=> f Hf a Ha s b1.
    case cf: check_tm => [[|[]/= f1 a1] B]; cycle 2.
    - move=> [??]; subst; apply: Hf cf.
    - move=> [??]; subst; have:= Hf _ _ cf.
      case: get_tm_hd => [|[P|V]]//=; case: fndP => //= k; rewrite pred_is_max//.
    have:= Hf _ _ cf; case: get_tm_hd => [D|[P|V]]/=;
    case X: check_tm => [S1 B1]; [|case: fndP => //= kf..];
    (case: ifP; [congruence|]) => _ H [<-] _; rewrite get_sig_hd_weak;
    by apply: incl_weakr.
Qed.

Definition mutual_exclusion :=
  forall pr S sP O u t s, (get_tm_hd_sig sP O (Callable2Tm t)) = Some S ->
    get_sig_hd S = d Func ->
     F u pr t s = [::] \/ (forall PREF LAST, F u pr t s = rcons PREF LAST ->
        forall s1 x, (s1, x) \in PREF ->
          seq.head ACut x.(premises) = ACut).


Lemma all_weak_sigP_empty {sV sP}:
  all_weak sV -> sigP sP empty sV.
Proof.
  move=> /forallP/= H.
  apply/forallP => /= k.
  by case: fndP => //=.
Qed.

Definition will_succeed B := is_ko B = false.

Lemma data_is_pred_exp t D sP O S b1:
  get_tm_hd t = inl D ->
    check_tm sP O t = (S, b1) ->
      S = b (d Pred) \/ S = b (Exp).
Proof.
  elim: t S b1 D => //=; [right; congruence|].
  move=> f Hf a Ha S b1 D gf.
  case C: check_tm => [[|m f1 a1] B1]; [left; congruence|].
  case: m C => //=; move=> /Hf-/(_ _ gf)[]//.
Qed.

Definition get_sig_hd_ X :=
(odflt Pred (omap (fun x => match get_sig_hd x with Exp => Pred | d X => X end) X)).

Definition get_sig_hd_1 sP O t:=
  get_sig_hd_ (get_tm_hd_sig sP O (Callable2Tm t)).

Lemma get_tm_hd_RCF hd e:
  get_tm_hd (Callable2Tm (RCallable2Callable hd)) = inl e -> False.
Proof. elim: hd e => //=. Qed.

Lemma sigtm_rev_Exp t: sigtm_rev t (b Exp) = [::].
Proof. case: t => //=. Qed.

Lemma assume_tm_nil sP O t: assume_tm sP O t [::] = O.
Proof. case: t => //=. Qed.

Ltac foo1 tc := subst; rewrite maxD_comm; split => //; by apply: more_precise_tc_tree_aux1 tc.

Lemma check_callable_main {u sP O N D s pr t d0 d1 dB N' sr1 r1 rs}:
  sigP sP s O ->
  closed_in O (Callable2Tm t) ->
    mutual_exclusion ->
    check_program sP ->
    check_callable sP O t d0 = (D, N) ->
      F u pr t s = (sr1, r1) :: rs ->
        tc_tree_aux sP O (big_or_aux pr (premises r1) rs) d1 = (dB, N') ->
          (minD (maxD d0 D) d1 = d1 -> minD (maxD d0 D) (maxD d1 dB) = (maxD d1 dB)) /\
          more_precise N' N
    .
Proof.
  move=> SP CO ME CP + F tc.
  rewrite/check_callable.
  case X: check_tm => [S []]; last by case: S X => [[|[]]| m f a] _ [??]; foo1 tc.
  case: S X => [|m f a _ [??]]; last by foo1 tc.
  move=> [_ [??]|]; first by foo1 tc.
  move=> d CT; rewrite/get_callable_hd_sig/get_tm_hd_sig.
  case thd: get_tm_hd => /=[data|p].
    have []// := data_is_pred_exp thd CT.
    destruct d => //= _ [??]; subst.
    rewrite maxD_comm/=; repeat split.
    apply: more_precise_trans (more_precise_tc_tree_aux1 tc) _.
    rewrite/assume_call sigtm_rev_Exp assume_tm_nil//.
  case: p thd => [p|v]; (case: fndP; last by move=> _ _ [??]; foo1 tc).
  - (*predicate case*)
    move=> pP tmHD [??]; subst.
    split.
      destruct d0, d, d1, dB => //=.
      exfalso.
      (* iF t is well called then tc returns Func  *)
      admit.
    (* apply: more_precise_trans (more_precise_tc_tree_aux1 CO tc) _. *)
    admit. (*this is hard*)
  - move=> pP tmHD [??]; subst.
    move: F.
    split.
      destruct d0, d, d1, dB => //=.
      exfalso.
      (* IF t is well called then tc returns Func  *)
      admit.
    (* apply: more_precise_trans (more_precise_tc_tree_aux1 CO tc) _. *)
    admit. (*this is hard*)
Admitted.

Lemma tc_tree_OR_Pred_Pred sP O N A s B d0 d1:
    is_ko A && is_ko B = false ->
    tc_tree_aux sP O (Or A s B) d0 = (d1, N) -> minD d0 d1 = d0.
Proof.
  move=> /=.
  (do 2 case:ifP => //=) => kA kB _.
    rewrite [tc_tree_aux _ _ _ _]surjective_pairing.
    by move=> [<- _]; destruct d0.
  rewrite [tc_tree_aux _ _ _ _]surjective_pairing.
  case: ifP => //=; first by destruct d0 => //=; congruence.
  rewrite [tc_tree_aux _ _ _ _]surjective_pairing.
  by move=> {}kB[<-_]; destruct d0 => //=; rewrite if_same.
Qed.

Lemma success_OR_is_ko {A s B}:
  success (Or A s B) -> is_ko A && is_ko B = false.
Proof. by move=> /=; case: ifP => dA /success_is_ko ->//; rewrite andbF. Qed.

Lemma success_Pred_Pred sP O N A d0 d1:
  success A -> tc_tree_aux sP O A d0 = (d1, N) -> minD d0 d1 = d0.
Proof.
  elim: A d0 d1 O N => //.
  - move=> d0 d1 O N  _/= [<-]//.
  - move=> A HA s B HB d0 d1 O N /success_OR_is_ko sA /tc_tree_OR_Pred_Pred ->//.
  - move=> A HA B0 HB0 B HB d0 d1 O N /=/andP[sA sB].
    rewrite !success_is_ko//.
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB].
    case tB0: tc_tree_aux => [DA' SA'].
    move=> [??]; subst.
    have H1 := HB _ _ _ _ sB tB.
    have H2 := HA _ _ _ _ sA tA.
    destruct d0, DA, DA' => //=.
Qed.

  Lemma change_only_in_extends X N N':
    more_precise X N -> extends N N' -> extends X N'.
  Proof.
    move=> /andP[/eqP dBA /forallP/= H].
    (* rewrite/extends {1}dBA; f_equal. *)
    (* apply/forallP; case:ifP => /=.
      move=> /forallP/= H1 [k kN'].
      rewrite valPE [val _]/=.
      have {H1}/= := H1 (Sub k kN').
      rewrite {1}dBA valPE.
      case:ifP => kX /eqP.
        rewrite in_fnd => -[->].
        have kN: k \in domf N by rewrite dBA.
        rewrite in_fnd.
        have {H}:= H (Sub k kX) => /=.
        rewrite valPE in_fnd/=.
        rewrite valPE.
    apply/forallP.
    apply/fsetP. *)
Abort.

(* Lemma step_mp {u sP A r s O N O' N' d0 d1 d0' d1'} : 
  check_program sP -> mutual_exclusion ->
  sigP sP s O -> valid_tree A -> more_precise O' N ->
      step u s A = r -> 
      closed_inT O A -> closed_inT O' (get_tree r) ->
      tc_tree_aux sP O  A            d0 =  (d1 , N ) ->
      tc_tree_aux sP O' (get_tree r) d0' = (d1', N') -> 
        will_succeed (get_tree r) ->
          more_precise N' N.
Proof.
  rewrite/will_succeed.
  move=> CkP ME.
  elim: A r s O N O' N' d0 d1 d0' d1' => //=; only 1, 2, 4:
    by move=> r s O N O' N' d0 d1 d0' d1'/= _ _ MP <- _ _ [??][??]; subst.
  - move=> p c r s O N O' N' d0 d1 d0' d1' SP _ MP <-/= C1 C2.
    {
      case CC: check_callable => [D B] [??]; subst.
      rewrite/big_or/=.
      case X: F => [|[sr1 r1] rs]//= .
      rewrite is_ko_big_or_aux/=.
      case T: tc_tree_aux => [D1 S1] [??]; subst.
      (* by have [] := check_callable_main SP C ME CkP CC X T. *)
      admit.
    }
  - move=> A HA smid B HB r s O N O' N' d0 d1 d0' d1' SO + MP <- /closed_inT_orP[cA cB].
    case: ifP => [deadA vB|ndeadA /andP[vA bB]].
      rewrite is_dead_is_ko//=.
      case: ifP => kB.
        by rewrite get_tree_Or /= is_dead_is_ko// is_ko_step kB.
      case tcB: tc_tree_aux => [D S].
      rewrite get_tree_Or => /closed_inT_orP [CA'] + [??]; subst => /=.
      rewrite is_dead_is_ko//=.
      case: ifP; first by [].
      case tcB': tc_tree_aux => [D1 S1] kB' cB' [??] _; subst.
      have HH : sigP sP smid O by admit.
      by apply: HB erefl cB cB' tcB tcB' kB'.
    case kA: is_ko.
      rewrite is_ko_step//= kA/= => /closed_inT_orP[cA' cB'] ++ kB.
      rewrite kB.
      case tcB: tc_tree_aux => [D S] [??]; subst.
      case tcB1: tc_tree_aux => [D1 S1] [??]; subst.
      have [] := more_precise_tc_tree_aux cB tcB tcB1 MP.
    case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
    case eA: step => [A'|A'|A'|A'] => /= /closed_inT_orP[cA' cB'].
    - have fA:= step_not_failed _ eA notF.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA']; subst.
      case dtB: (tc_tree_aux _ _ B) => [DB sVB]; subst.
      have/= {}HA := HA _ _ _ _ _ _ _ _ _ _ SO vA MP eA cA cA' dtA dtA'.
      case: ifP => kB.
        move=> [??]; subst.
        rewrite andbT => + kA'.
        by rewrite kA' => -[??]; subst; auto.
      move=> ++ _.
      case dtB': (tc_tree_aux _ _ B) => [DB' sVB'][??]; subst.
      rewrite andbF/=.
      (* have [? M] := tc_tree_aux_func2 dtB dtB'; subst. *)
      case: (ifP (is_ko _)) => kA' [??]; subst.
        move: dtA'; rewrite is_ko_tc_tree_aux => //-[??]; subst.
        apply: more_precise_trans.
          by apply: more_precise_tc_tree_aux1 dtB'.
        by apply extends_mp.
      (* have:= . *)
      have MP := HA (extends_trans _ E) kA'.
      Search extends merge_sig.
      (* apply: more_precise_merge2 (CO) _ _ _ _ => //;
        apply: more_precise_tc_tree_aux1; eauto. *)
      admit.
    - have fA:= step_not_failed _ eA notF.
      have kA' := (expand_CB_is_ko eA).
      rewrite kA' is_ko_cutr.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA'] + [??] _; subst.
      have /=MP := HA _ _ _ _ _ _ _ _ _ cA vA SP eA dtA dtA' kA'.
      case: ifP => kB.
        by move=> [??]; subst.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      case:ifP => //CA[??]; subst.
      (* rewrite merge_comm; apply: more_precise_mergeR (CO) _ _ MP;
      apply: more_precise_tc_tree_aux1; eauto. *)
        admit.
      admit.
    - have [? fA] := expand_failed_same _ eA; subst A'.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' sVA']//=.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
      case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
      have [? M2] := tc_tree_aux_func2 dtB1 dtB2; subst.
      rewrite kA.
      case: ifP => kB [??][??] _; subst; by [].
    - have [? sA]:= expand_solved_same _ eA; subst A'.
      rewrite (success_is_ko sA)//=.
      rewrite success_has_cut//=.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' sVA']//=.
      have [? {}HA] := tc_tree_aux_func2 dtA dtA'; subst.
      case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
      case dtB': (tc_tree_aux _ _ B) => /=[DB2 sVB2]//= ++ _.
      have [? {}HB] := tc_tree_aux_func2 dtB dtB'; subst.
      by case:ifP => kB [??] [??]; subst.
  - move=> A HA B0 HB0 B HB s O N N' r dA dB d0 d1 /closed_inT_andP[cA cB0 cB] /and4P[vA +++] SP <-.
    case: (ifP (is_ko _)) => kA; first by rewrite is_ko_success// is_ko_failed// is_ko_step//=kA//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA SA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB SB]//=.
    case eA: step => [A'|A'|A'|A'].
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0 cB0}.
      rewrite dtB base_and_is_ko// => -[??]; subst.
      case:ifP => kA'//.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??] _; subst.
      rewrite !merge_refl.
      have MP := HA _ _ _ _ _ _ _ _ _ cA vA SP eA dtA dtA' kA'.
      have CA : closed_inT SA B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
      by have [] := more_precise_tc_tree_aux CA dtB dtB' MP.
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0 cB0}.
      rewrite base_and_is_ko// dtB => -[??]; subst.
      rewrite (expand_CB_is_ko eA)/=.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??] _; subst.
      rewrite !merge_refl.
      have CA : closed_inT SA B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
      have MP := HA _ _ _ _ _ _ _ _ _ cA vA SP eA dtA dtA' (expand_CB_is_ko eA).
      by have [->] := more_precise_tc_tree_aux CA dtB dtB' MP.
    - have [? fA]:= expand_failed_same _ eA; subst A'.
      rewrite failed_success//= fA=> /eqP -> {B0 HB0 cB0} bB _.
      rewrite dtB kA.
      move/orP: bB => []bB.
        rewrite base_and_is_ko// => -[??]; subst.
        case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
        have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
        case dtB': (tc_tree_aux _ _ B) => /=[DB' sVB']//=[??] _; subst.
        by have [? M2] := tc_tree_aux_func2 dtB dtB'; subst.
      have kB:= base_and_ko_is_ko bB.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      by move: dtB; rewrite kB !is_ko_tc_tree_aux// => -[??][??][??]; subst.
    - have [? sA] := expand_solved_same _ eA; subst A'.
      rewrite sA/= => vB bB ckB.
      case: ifP => kB.
        move: dtB; rewrite is_ko_step//=is_ko_tc_tree_aux//=.
        case dtB0: (tc_tree_aux _ _ B0) => [DB0 SB0].
        rewrite success_is_ko//=kB.
        case dtA': tc_tree_aux => [DA' SA'];
        case dtB0': tc_tree_aux => [DB0' SB0'].
        move=> [??][??][??]; subst.
        have [? M1]:= tc_tree_aux_func2 dtA dtA'; subst.
        have [? M2]:= tc_tree_aux_func2 dtB0 dtB0'; subst.
        by destruct dA, d1, dB, DA, DA',d0 => //=; auto; try congruence.
      case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//= [??]; subst.
      have ? := success_det_tree_same_ctx cA sA dtA; subst SA.
      case eB: step => //=[B'|B'|B'|B'];
      case dtA': tc_tree_aux => [DA' SA'];
      case dtB': (tc_tree_aux _ _ B') => [DB' SB'];
      case dtB0': tc_tree_aux => [DB0' SB0'] + _; cycle 1;
      [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); rewrite kA; subst..].
      - move: (dtA') (dtB0'); rewrite cutl_tc_tree_aux//= cutr_tc_tree_aux.
        move=> [??][??]; subst SB0' DB0' SA' DA'.
        have /= SP1 := expand_sigP dA cA SP eA.
        rewrite dtA in SP1.
        rewrite success_is_ko?success_cut//(expand_CB_is_ko eB)  => -[??]; subst.
        have MP := HB _ _ _ _ _ _ _ _ _ cB vB SP1 eB dtB dtB' (expand_CB_is_ko eB).
        have MP2 := more_precise_tc_tree_aux1 dtB'.
        rewrite merge_comm.
        rewrite more_precise_merge//; last first.
          have /andP[/eqP H _] := (change_only_in_tree_tc_tree_aux dtB').
          by rewrite H.
        admit.
      - have [? fB] := expand_failed_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
        by have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
      - have [? sB] := expand_solved_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst SB'.
        by have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
      - have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
        have /= SP1 := expand_sigP dA cA SP eA.
        rewrite dtA in SP1.
        have /= {}HB := HB _ _ _ _ _ _ _ _ _ cB vB SP1 eB dtB dtB'.
        case kB': (is_ko B') => -[??]; subst.
          move: dtB'; rewrite is_ko_tc_tree_aux//= => -[??]; subst.
          (* apply: more_precise_mergeR (CO) _ _ (more_precise_refl _); *)
          (* apply: more_precise_tc_tree_aux1; eauto. *)
          admit.
        have MP:= HB kB'.
        (* by apply: more_precise_merge2 (CO) (more_precise_tc_tree_aux1 _ _) (more_precise_tc_tree_aux1 _ _) _ (more_precise_refl _); eauto. *)
        admit. 
Admitted. *)

(*Lemma step_Exp_Pred_Func u sP A r s O N O' N' dB: 
  check_program sP -> mutual_exclusion ->
    closed_inT O A -> valid_tree A ->
      step u s A = Expanded r -> more_precise O' N ->
      tc_tree_aux sP O A Pred = (Func, N) ->
        tc_tree_aux sP O' r Pred = (dB, N') ->
          dB = Func.
Proof.
  move=> CkP ME.
  elim: A r s O N O' N' dB => //.
  - move=> p c A r s O N O' N' dB _ [<-]{A} MP/=.
    case CC: check_callable => [D B] [??]//.
  - move=> A HA smid B HB r s O N O' N' dB _ _ eA _ dt.
    have /= H := (step_is_ko _ eA notF).
    by have:= tc_tree_OR_Pred_Pred H dt.
  - move=> A HA B0 HB0 B HB r s O N O' N' dB /= /closed_inT_andP[cA cB0 cB]/= /and4P[vA].
    case eA: step => //=[A'|A'].
      rewrite (step_not_failed _ eA notF) (expand_not_solved_not_success _ eA notF)/=.
      move=> /eqP -> {HB0 B0 cB0} bB _ [<-{r}] MP.
      rewrite (step_is_ko _ eA notF)/= (base_and_is_ko bB).
      case tA: tc_tree_aux => [DA SA].
      case tB: tc_tree_aux => [DB SB].
      case tA': tc_tree_aux => [DA' SA'].
      case tB': tc_tree_aux => [DB' SB'].
      rewrite 2!maxD_refl => -[??]; subst.
      case: ifP => kA' [??]; subst; first by  [].
      have {}HA := HA _ _ _ _ _ _ _ cA vA eA _ _ tA'.
      have MP1 := (more_precise_tc_tree_aux1 tA).
      have CB := (closed_inT_mp cB MP1).
      rewrite merge_refl in MP.
      suffices : dB <= Func by destruct dB.
      have MP2 : more_precise SA' SA.
        apply: more_precise_trans (more_precise_tc_tree_aux1 tA') _.
        apply: more_precise_trans MP (more_precise_tc_tree_aux1 tB).
      have MP3 : more_precise O' SA.
        by apply: more_precise_trans MP (more_precise_tc_tree_aux1 tB).
      have [_ -> //] := more_precise_tc_tree_aux CB tB tB' MP2.
      destruct DA, DA' => //=.
      by have:= HA _ MP3 tA.
    have [? sA] := expand_solved_same _ eA; subst A'.
    rewrite sA/= => vB bB ckB + MP.
    case eB: step => //=[B'][<-{r}].
    rewrite (step_is_ko _ eB)//= success_is_ko//.
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB].
    case tB0: tc_tree_aux => [DB0 SB0].
    case tA': tc_tree_aux => [DA' SA'] [??]; subst.
    case tB0': tc_tree_aux => [DB0' SB0'].
    case tB': tc_tree_aux => [DB' SB'].
    destruct DB0, DB => //=.
    have MOO: more_precise O' O.
      apply: more_precise_trans MP _.
      apply: more_precise_trans (more_precise_tc_tree_aux1 tA).
      apply: more_precise_mergeL; apply: more_precise_tc_tree_aux1; eauto.
    have [M /(_ minD_refl) DDA] := more_precise_tc_tree_aux cA tA tA' MOO.
    have := more_precise_tc_tree_aux _ tB0 tB0' M.
    have dOA:= change_only_in_vars_same_domain (change_only_in_tree_tc_tree_aux tA).
    rewrite -(close_inT_dom _ dOA).
    move=> []// MP1.
    move=> /(_ DDA).
    destruct DB0' => //= _.
    case: ifP => kB' [<-{dB}]// _.
    destruct DA; first by have:= success_Pred_Pred sA tA.
    destruct DA'; first by have:= success_Pred_Pred sA tA'.
    have ? := success_det_tree_same_ctx cA sA tA; subst.
    have ? := success_det_tree_same_ctx (closed_inT_mp cA MOO) sA tA'; subst.
    clear tA tA' tB0 tB0' HA HB0.
    apply: HB (cB) (vB) (eB) _ (tB) (tB').
    admit.
Admitted.
*)


Lemma step_min_max {u sP A r s O N N' d0 d1 dA dB} : 
  check_program sP -> mutual_exclusion ->
    closed_inT O A -> sigP sP s O -> valid_tree A ->
      step u s A = r -> 
      (* more_precise O' N -> *)
      tc_tree_aux sP O  A            d0 = (dA, N) ->
      tc_tree_aux sP O (get_tree r) d1 = (dB, N') ->
            (minD dA d1 = d1 -> minD dA dB = dB).
Proof.
  (*rewrite/will_succeed.
  move=> CkP ME.
  (* move: O N N' r dA dB d0 d1. *)
  elim: A r s O N O' N' d0 d1 dA dB => //=; only 1, 2, 4: 
    by move => r s O N O' N' d0 d1 dA dB _ _ _ <- MP [??][??]; subst; auto.
  - move=> p c r s O N O' N' d0 d1 dA dB cO SP _ <- MP.
    {
      case CC: check_callable => [D B] [??]; subst.
      rewrite/big_or/=.
      case X: F => [|[sr1 r1] rs]//=; first by move=> [<-]; destruct d0, D.
      rewrite is_ko_big_or_aux/=.
      case T: tc_tree_aux => [D1 S1] [??]; subst.
      (* by have [] := check_callable_main SP C ME CkP CC X T. *)
      admit.
    }
  - move=> A HA smid B HB r s O N O' N' d0 d1 dA dB /closed_inT_orP [cA cB] SP + <- MP.
    case: ifP => [deadA vB|ndeadA /andP[vA bB]].
      rewrite is_dead_is_ko//=.
      case: ifP => kB.
        move=> [??]; subst => /=.
        rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
        by rewrite is_ko_step//=kB => -[??]//.
      case tB: tc_tree_aux => [D S] [??]; subst.
      rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
      case: ifP; first by move=> ksB [<-]; destruct d0, D.
      case tB': tc_tree_aux => [D1 S1] kO [??]; subst.
      have HH : sigP sP smid O by admit.
      have:= HB _ _ _ _ _ _ _ _ _ _ cB HH vB erefl MP tB tB'.
      by destruct d0, D, d1.
    case kA: is_ko.
      rewrite is_ko_step//= kA/=; case: ifP => kB; first by destruct dA, dB.
      case tcB: tc_tree_aux => [D S] [??]; subst.
      case tcB1: tc_tree_aux => [D1 S1] [??]; subst.
      have MP1 : more_precise O' O.
        apply: more_precise_trans _ (more_precise_tc_tree_aux1 tcB).
        (* apply: extends_mp. *)
        auto.
      have [_] := more_precise_tc_tree_aux cB tcB tcB1 MP1.
      by destruct d0, d1, D, D1 => //=; congruence.
    case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
    have MP2 := more_precise_trans MP _.
    case eA: step => [A'|A'|A'|A'] => /=.
    - have fA:= step_not_failed _ eA notF.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA']; subst.
      case dtB: (tc_tree_aux _ _ B) => [DB sVB]; subst.
      have {}HA := HA _ _ _ _ _ _ _ _ _ _ cA SP vA eA _ dtA dtA'.
      case: ifP => kB.
        move=> [??]; subst.
        rewrite andbT; case: ifP => kA'; first by destruct dB, d0, DA.
        rewrite kA' => -[??]; subst.
        by destruct d0, DA, d1 => //; auto.
      case dtB': (tc_tree_aux _ _ B) => [DB' sVB'][??]; subst.
      have H := more_precise_tc_tree_aux cB dtB dtB'.
      have MP3 : more_precise (merge_sig sVA sVB) O by apply: more_precise_mergeL; apply: more_precise_tc_tree_aux1; eauto. 
      have {}H := H (MP2 _ _).
      case: (ifP (is_ko _)) => kA' [??]; subst.
        move: dtA'; rewrite is_ko_tc_tree_aux => //-[??]; subst.
        case: ifP => //= CA.
        destruct d0, DA, DB => //=?; subst.
        by have [] := H MP3; clear; auto.
      rewrite (step_keep_cut eA)//=.
      case: ifP => //= CA.
      destruct d0, DA, DB => //=?; subst.
      have {H MP2}[] := H MP3.
      move=> H1 /(_ minD_refl) H2.
      destruct DA', DB' => //=.
      apply: HA minD_refl.
      admit.
    - have fA:= step_not_failed _ eA notF.
      have kA' := (expand_CB_is_ko eA).
      rewrite kA' is_ko_cutr.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA'] + [??]; subst.
      have {}HA := HA _ _ _ _ _ _ _ _ _ _ cA SP vA eA _ dtA dtA'.
      case: ifP => kB.
        move=> [??]; subst.
        have:= HA (MP2 _ (more_precise_refl _)) .
        by destruct d0, DA, d1 => //.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      move=> [??]; subst.
      case: ifP => CA; last by [].
      destruct d1, d0, DA', DA, DB => //=.
      move=> _; apply: HA => //.
      have : more_precise (merge_sig sVA sVB) sVA by admit.
      move=> /HA.
      by destruct d0, DA, DB, d1 => //=.
    - have [? fA] := expand_failed_same _ eA; subst A'.
      case dtA': (tc_tree_aux _ _ A) => [DA' sVA'].
      case dtB1: (tc_tree_aux _ _ B) => [DB1 sVB1].
      case dtB2: (tc_tree_aux _ _ B) => [DB2 sVB2].
      have:= more_precise_tc_tree_aux cA dtA dtA'.
      have:= more_precise_tc_tree_aux cB dtB1 dtB2.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      have [? M2] := tc_tree_aux_func2 dtB1 dtB2; subst.
      rewrite kA.
      case: ifP => kB [??][??]; subst.
        move: dtB2 dtB1; rewrite !is_ko_tc_tree_aux// => -[??][??]; subst.
        by destruct d0, DA', d1, DA => //=; congruence.
      case:ifP => //=CA.
      destruct d0, DA, DB1 => //?; subst => /=.
      by destruct d1, DA', DB2 => //=; try congruence.
    - have [? sA]:= expand_solved_same _ eA; subst A'.
      rewrite (success_is_ko sA)//=.
      rewrite success_has_cut//=.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' sVA']//=.
      have [? {}HA] := tc_tree_aux_func2 dtA dtA'; subst.
      case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
      case dtB': (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
      have [? {}HB] := tc_tree_aux_func2 dtB dtB'; subst.
      case:ifP => kB [??] [??]; subst; last by [].
      by destruct d0, DA, d1, DA' => //=; congruence.
  - move=> A HA B0 HB0 B HB s O N N' r dA dB d0 d1 /closed_inT_andP[cA cB0 cB] /and4P[vA +++] SP <-.
    case: (ifP (is_ko _)) => kA; first by rewrite is_ko_success// is_ko_failed// is_ko_step//=kA//=; destruct dA, dB.
    case dtA: (tc_tree_aux _ _ A) => /=[DA SA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB SB]//=.
    case eA: step => [A'|A'|A'|A'].
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0 cB0}.
      rewrite dtB base_and_is_ko// => -[??]; subst.
      case:ifP => kA'//; first by destruct dB, DB.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??]; subst.
      rewrite !maxD_refl.
      (* have CA : closed_in SA by apply: closed_in_mp CO (more_precise_tc_tree_aux1 CO dtA). *)
      have {}HA := HA _ _ _ _ _ _ _ _ _ cA vA SP eA dtA dtA'.
      have MP := step_mp CkP cA ME vA SP eA dtA dtA' kA'.
      have CAB: closed_inT SA B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
      have [] := more_precise_tc_tree_aux CAB dtB dtB' MP.
      destruct DB => //=?; subst.
      by destruct DA, DA', ddB => //=; auto.
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0 cB0}.
      rewrite base_and_is_ko// dtB => -[??]; subst.
      rewrite (expand_CB_is_ko eA)/=.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??]; subst.
      rewrite !maxD_refl.
      (* have CA : closed_in SA by apply: closed_in_mp CO (more_precise_tc_tree_aux1 CO dtA). *)
      have {}HA := HA _ _ _ _ _ _ _ _ _ cA vA SP eA dtA dtA'.
      have MP := step_mp CkP cA ME vA SP eA dtA dtA' (expand_CB_is_ko eA).
      have CAB: closed_inT SA B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
      have [] := more_precise_tc_tree_aux CAB dtB dtB' MP.
      destruct DB => //=?; subst.
      by destruct DA, DA', ddB => //=; auto.
    - have [? fA]:= expand_failed_same _ eA; subst A'.
      rewrite failed_success//= fA=> /eqP -> {B0 HB0 cB0} bB _.
      rewrite dtB kA.
      move/orP: bB => []bB.
        rewrite base_and_is_ko// => -[??]; subst.
        case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
        have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
        case dtB': (tc_tree_aux _ _ B) => /=[DB' sVB']//=[??]; subst.
        have [? M2] := tc_tree_aux_func2 dtB dtB'; subst.
        rewrite !maxD_refl.
        by destruct DB, d1, DB', DA, DA', d0 => //=; congruence.
      have kB:= base_and_ko_is_ko bB.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      by move: dtB; rewrite kB !is_ko_tc_tree_aux// => -[??][??][??]; subst.
    - have [? sA] := expand_solved_same _ eA; subst A'.
      rewrite sA/= => vB bB ckB.
      case: ifP => kB.
        move: dtB; rewrite is_ko_step//=is_ko_tc_tree_aux//=.
        case dtB0: (tc_tree_aux _ _ B0) => [DB0 SB0].
        rewrite success_is_ko//=kB.
        case dtA': tc_tree_aux => [DA' SA'];
        case dtB0': tc_tree_aux => [DB0' SB0'].
        move=> [??][??][??]; subst.
        have [? M1]:= tc_tree_aux_func2 dtA dtA'; subst.
        have [? M2]:= tc_tree_aux_func2 dtB0 dtB0'; subst.
        by destruct dA, d1, dB, DA, DA',d0 => //=; auto; try congruence.
      case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//= [??]; subst.
      have ? := success_det_tree_same_ctx cA sA dtA; subst SA.
      case eB: step => //=[B'|B'|B'|B'];
      case dtA': tc_tree_aux => [DA' SA'];
      case dtB': (tc_tree_aux _ _ B') => [DB' SB'];
      case dtB0': tc_tree_aux => [DB0' SB0']; cycle 1;
      [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); rewrite kA; subst..].
      - move: (dtA') (dtB0'); rewrite cutl_tc_tree_aux//= cutr_tc_tree_aux.
        move=> [??][??]; subst SB0' DB0' SA' DA'.
        have /= SP1 := expand_sigP d0 cA SP eA.
        rewrite dtA in SP1.
        rewrite success_is_ko?success_cut//(expand_CB_is_ko eB)  => -[??]; subst.
        have {}HB := HB _ _ _ _ _ _ _ _ _ cB vB SP1 eB dtB dtB'.
        by destruct DB, DB0 => //=?; subst; destruct DB'; auto.
      - have [? fB] := expand_failed_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
        have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
        destruct DB0, DB => //= ?; subst; destruct DB0', DB', DA, DA', d0; auto; try congruence.
      - have [? sB] := expand_solved_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst SB'.
        have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
        destruct DB0, DB => //=?; subst.
        destruct DB0', DB', DA', DA, d0 => //=; auto; try congruence.
      - have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
        have /= SP1 := expand_sigP d0 cA SP eA.
        rewrite dtA in SP1.
        have CAB:  closed_inT SA' B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
        have /= {}HB := HB _ _ _ _ _ _ _ _ _ CAB vB SP1 eB dtB dtB'.
        case kB': (is_ko B') => -[??]; subst.
          move: dtB'; rewrite is_ko_tc_tree_aux//= => -[??]; subst.
          destruct DB0, DB, d1, dB, DA, DA', d0 => //=; try congruence.
        destruct DB0, DB => //=?; subst.
        move: m m2; rewrite !(@minD_comm _ Func)/=.
        destruct DA'; simpl in *.
          have ? := HB erefl; subst.
          destruct DA => /=; last by move=> _ <-.
          move=> _ _; by destruct DB0' => //; congruence.
        rewrite !(@minD_comm _ Pred)/=.
        rewrite eqxx => + _.
        destruct DA.
          by destruct d0 => //=; congruence.
        move=> _.
        destruct DB0'; [|by congruence] => /=.
        destruct DB' => //.
        by have := step_Exp_Pred_Func CkP CAB ME vB SP1 eB dtB dtB'.*)
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A (Some s') B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_inT sV A -> valid_tree A ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n ->
        next_alt false B = None /\ sigP sP s' sV'.
Proof.
  rewrite/is_det.
  move=> ckP ME ++++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV'; clear -ckP ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' H1 vA SP H2.
    have /=-> := success_det_tree_next_alt vA sA H2.
    have ? := success_det_tree_same_ctx H1 sA H2; subst.
    have /= := expand_sigP Func H1 SP (succes_is_solved _ _ sA).
    rewrite H2 => ->//.
    apply: Build_Unif; move=> *; apply: None.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 vA SP dtA; subst.
    have WS : will_succeed B.
      rewrite/will_succeed; case KB: is_ko => //.
      by have [] := run_consistent _ R (is_ko_runb _ KB).
    case TC: (tc_tree_aux sP sV B Func) => [X Y].
    have /=? := step_min_max ckP ME H1 SP vA eA dtA TC erefl; subst.
    have [->] := IH _ erefl _ _ (closed_inT_step_CB H1 eA) (valid_tree_expand vA eA) SP TC.
    move=> H.
    split => //.
    apply: sigP_more_precise H.
    (* destruct X. *)
    (* have [->] := IH _ erefl _ _ (closed_inT_step_CB H1 eA) (valid_tree_expand vA eA) SP TC. *)
    (* have MP := step_mp ckP ME _ _ _ _ eA dtA TC WS. *)
    (* have ? := step_min_max ckP H1 ME vA SP eA dtA TC erefl; subst. *)
    (* destruct X => //=. *)
    (* have cB := closed_inT_step_CB H1 eA. *)
    (* have [Hx Hy] := IH _ erefl _ _ cB (valid_tree_expand vA eA) SP TC. *)
    (* split => //. *)
    (* by apply: sigP_more_precise MP Hy. *)
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 vA SP dtA; subst.
    have WS : will_succeed B.
      rewrite/will_succeed; case KB: is_ko => //.
      by have [] := run_consistent _ R (is_ko_runb _ KB).
    case TC: (tc_tree_aux sP sV B Func) => [X Y].
    have MP := step_mp ckP H1 ME vA SP eA dtA TC WS.
    have ? := step_min_max ckP H1 ME vA SP eA dtA TC erefl; subst.
    destruct X => //=.
    have [] := IH _ erefl _ _ _ (valid_tree_expand vA eA) SP TC; last first.
      move=> Hx Hy.
      split => //.
      by apply: sigP_more_precise MP Hy.
    replace B with (get_tree (step u s1 A)) by rewrite eA//.
    (* by apply: @closed_inT_step . *)
    admit.
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C vA SP TC; subst.
    have := failed_det_tree_next_alt vA C TC nA.
    move => [[]// [N [? X MP]]]//.
    have [] := IH _ erefl _ _ _ (valid_tree_next_alt vA nA) SP X; last first.
      move=> H INV.
      split; first by [].
      by apply: sigP_more_precise MP INV.
    by apply: closed_in_next_alt nA.
Admitted.

Lemma run_is_detP1 {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_inT sV A ->
    sigP sP s sV -> valid_tree A ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None.
Proof.
  move=> CkP ME C S vA TC u s' B n R.
  by have [] := run_is_det CkP ME C vA S TC R.
Qed.

Definition typ_func (A: (_ * sigV)%type) := match A with (Func, _) => true | _ => false end.
Definition det_tree sP sV A := typ_func (tc_tree_aux sP sV A Func).

Lemma main {sP p t sV}:
  check_program sP -> mutual_exclusion ->
    closed_in sV (Callable2Tm t) ->  all_weak sV ->
      det_tree sP sV (CallS p t) -> 
        is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det.
  move=> /= CP ME CV F.
  case C: check_callable => [[] S]//= _.
  move=> u s' B n H.
  apply: run_is_detP1 H; eauto; last rewrite/=C//.
  by apply: all_weak_sigP_empty.
Qed.

Print Assumptions  main.

Module elpi.
  From det Require Import elpi elpi_equiv.
  From det Require Import tree t2l_prop tree_valid_state tree_prop.

  Definition is_det g := forall u s' a',
    nur u empty g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c ign sV}: 
    check_program sP -> mutual_exclusion ->
    closed_in sV (Callable2Tm c) -> all_weak sV ->
      check_callable sP sV c Func = (Func, ign) -> 
      is_det ((call p c):::nilC).
  Proof.
    move=> CkP ME CV F C u s' a'.
    move=> /elpi_to_tree /(_ _ (CallS p c))/=.
    move=> /(_ _ isT erefl) [t1'[n [H3]]].
    have {}CV: closed_inT sV (CallS p c) by move=> //.
    have /= := run_is_det CkP ME CV.
    rewrite C.
    move=> /(_ _ empty isT (all_weak_sigP_empty F) erefl _ _ _ _ H3) [].
    have:= valid_tree_run _ _ H3 => /(_ isT).
    move=> []; first by move=> ->; rewrite t2l_dead//is_dead_dead//.
    move=> vt1' H.
    have ft1':= next_alt_None_failed H.
    have:= failed_next_alt_none_t2l vt1' ft1' H.
    by move=> ->.
  Qed.

End elpi.

(* Print Assumptions tail_cut_is_det. *)

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

Lemma is_ko_big_and p A : is_ko (big_and p A) = false.
Proof. elim: A => //=-[]//. Qed.

Lemma is_ko_big_or_aux p x xs : is_ko (big_or_aux p x xs) = false.
Proof. elim: xs x => //=[|[s r] rs IH] x/=; rewrite is_ko_big_and//. Qed.

Lemma base_and_is_ko A: base_and A -> is_ko A = false.
Proof. move=> bA; rewrite failed_is_ko//base_and_failed//. Qed.

Lemma base_and_ko_is_ko A: base_and_ko A -> is_ko A.
Proof. case: A => //= -[]//. Qed.


Ltac foo tcA IH := by move=> [<-<-]; case tcA: tc_tree_aux => [BA BI];
  (try rewrite maxD_comm in tcA); rewrite IH tcA maxD_refl merge_refl.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  (check_atoms sP sV l r) = tc_tree_aux sP sV (big_and p l) r.
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [dA sVA].
  rewrite is_ko_big_and.
  case YY : A X => //=[|c]; first by foo tcA IH.
  rewrite/check_callable.
  case X: check_tm => //[d b]//=.
  case: d X => /=[[|d]|m f a] C; cycle 1; [|foo tcA IH..].
  destruct b; last by foo tcA IH.
  case CH: get_callable_hd_sig => [v|]; last by foo tcA IH.
  rewrite (@maxD_comm r) -maxD_assoc maxD_refl.
  case dt: tc_tree_aux => [[]][??]; subst; rewrite merge_refl;
  by rewrite IH dt maxD_refl.
Qed.

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
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then good_assignment sP SV vk
    else SV == weak SV].

Lemma eq_incl x y : (incl x y && incl y x) = (x == y).
Proof.
  apply/andP/eqP => [[]|-> //].
    elim: x y => [[|[]]|[] s_ IHs t IHt] [[|[]]|[] s' t']; try by [rewrite /incl/min /=].
    by rewrite !incl_arr /= => /andP[? /IHt HT] /andP[/IHs HS ?]; rewrite -HS // -HT.
  by rewrite !incl_arr/= => /andP[? /IHt HT] /andP[/IHs HS ?]; rewrite -HS // -HT.
Qed.

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

Lemma expand_sigP {u sP sV A r s} : 
  closed_in sV ->
    sigP sP s sV ->
        step u s A = r -> 
           sigP sP (get_substS s (get_tree r)) sV.
Proof.
  move=> ++ <-.
  elim: A u sP sV s => //.
  - move=> p c u sP sV s clo /forallP/(_ (Sub (_:V) _))  H; apply/forallP=> -[k kV].
    move: (H k kV); rewrite valPE/= {H}.
    have [kS|nkS] := fndP.
      admit. (* more instantiated, interesting branch *)
    have [kS'|nkS'] := fndP.
      admit. (* assigned, interesting branch *)
    by []. (* untouched *)
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

Definition all_weak (sV:sigV):= [forall k : domf sV, sV.[valP k] == weak (sV.[valP k]) ].

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

(* Lemma sig_hd_exp S:
  get_sig_hd S = Exp -> S = b Exp.
Proof.
  elim: S => //=[|[] f Hf a Ha ]; [congruence|..]. *)

Lemma xx sP t O u pr s S D1 N1 sV (s1:Sigma) (r1:R):
  closed_in O ->
  sigP sP s O ->
  mutual_exclusion ->
  check_program sP ->
    check_tm sP O (Callable2Tm t) = (S, true) ->
      let sig_hd := get_sig_hd_1 sP O t in
      (s1, r1) \in F u pr t s -> 
        check_atoms sP sV r1.(premises) Func = (D1, N1) ->
          minD D1 sig_hd = D1.
Proof.
  move=> CO SP ME /(_ pr) /allP/= ckP.
  rewrite/F.
  case TM: tm2RC => //=[rc].
  rewrite /get_rcallable_hd.
  case tm_hd : get_tm_hd => [//|[p|//]].
  case: fndP => //= ppr ckt inS.
  have:= select_in_rules u rc (get_modes_rev rc (sig pr).[ppr]) (rules pr) s.
  move=> /allP/=.
  move=> /(_ _ inS) /ckP/=; rewrite /check_rule/RCallable_sig.
  case: r1 inS => /= hd pm inS.
  rewrite/get_tm_hd_sig/=.
  case X: get_tm_hd => //=[e|[ps|v]]; [by have:= get_tm_hd_RCF X|case:fndP => //..].
  move=> pP.
  case ckA: check_atoms => [D B].
  rewrite/is_det_sig.
  case: ifP => //= H4 CHD.
  rewrite/get_sig_hd_1 /get_tm_hd_sig.
  move: H4.
  have ?: ps = p.
    (*the head has the same head as the call: X + inS + tm_hd*)
    move: X inS tm_hd.
    admit.
  subst ps. 
  case shd: get_sig_hd => [|[]]//=.
  - move: ckA.
    move: shd.
    admit.
  - destruct D; [move=> _|by []].
    case thd : get_tm_hd => [d1|[p1|v1]].
    - admit.
    - move: tm_hd; rewrite (deref_rigid TM thd) => -[?]; subst p1.
      rewrite (in_fnd pP)/get_sig_hd_/=shd.
      rewrite !(@minD_comm _ Func)/=.
      admit. (*should be true using ckA*)
    - rewrite (in_fnd (CO _))/get_sig_hd_/=.
      admit.
  - move=> _.
    case thd : get_tm_hd => [d1|[p1|v1]].
    - admit.
    - move: tm_hd; rewrite (deref_rigid TM thd) => -[?]; subst p1.
      rewrite (in_fnd pP)/get_sig_hd_/=shd.
      rewrite !(@minD_comm _ Pred)//=.
    - rewrite (in_fnd (CO _))/get_sig_hd_/=.
      admit.
Admitted.

Lemma sigtm_rev_Exp t: sigtm_rev t (b Exp) = [::].
Proof. case: t => //=. Qed.

Lemma assume_tm_nil sP O t: assume_tm sP O t [::] = O.
Proof. case: t => //=. Qed.

Ltac foo1 tc := subst; rewrite maxD_comm; split => //; by apply: more_precise_tc_tree_aux1 tc.

Lemma check_callable_main {u sP O N D s pr t d0 d1 dB N' sr1 r1 rs}:
  sigP sP s O ->
  closed_in O ->
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
    apply: more_precise_trans (more_precise_tc_tree_aux1 CO tc) _.
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

Lemma expand_det_tree {u sP O N A r s d0 d1 dA dB N'} : 
  check_program sP -> closed_in O -> mutual_exclusion ->
    valid_tree A ->
    sigP sP s O ->
      step u s A = r -> 
      tc_tree_aux sP O A d0 = (dA, N) ->
        tc_tree_aux sP O (get_tree r) d1 = (dB, N') ->
          will_succeed (get_tree r) ->
            [/\ (minD dA d1 = d1 -> minD dA dB = dB) & more_precise N' N].
Proof.
  rewrite/will_succeed.
  move=> CkP + ME.
  move: O N N' r dA dB d0 d1.
  elim: A s => //=.
  - move=> s O N N' r dA dB d0 d1 CO _ SP <- [<-<-]/=[<-<-]//.
  - move=> s O N N' r dA dB d0 d1 CO _ SP <- [<-<-]/=[<-<-]//.
  - move=> p c s O N N' r dA dB d0 d1 C _ SP <-.
    {
      case CC: check_callable => [D B] [??]; subst.
      rewrite/big_or/=.
      case X: F => [|[sr1 r1] rs]//= + _.
      rewrite is_ko_big_or_aux/=.
      case T: tc_tree_aux => [D1 S1] [??]; subst.
      by apply: check_callable_main X T.
    }
  - move=> s O N N' r dA dB d0 d1 CO _ SP <- [<-<-]/=[<-<-]//.
  - move=> A HA smid B HB s O N N' r dA dB d0 d1 CO + SP <-.
    case: ifP => [deadA vB|ndeadA /andP[vA bB]].
      rewrite is_dead_is_ko//=.
      case: ifP => kB.
        move=> [??]; subst => /=.
        rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
        by rewrite is_ko_step//=kB => -[??]//.
      case tcB: tc_tree_aux => [D S] [??]; subst.
      rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
      case: ifP; first by move=> ksB [??].
      case tcB': tc_tree_aux => [D1 S1] kO [??] _; subst.
      have HH : sigP sP smid O by admit.
      have [m MP] := HB _ _ _ _ _ _ _ _ _ CO vB HH erefl tcB tcB' kO.
      split; last (by []); by destruct d0, D, d1.
    case kA: is_ko.
      rewrite is_ko_step//= kA/= => ++ kB.
      rewrite kB.
      case tcB: tc_tree_aux => [D S] [??]; subst.
      case tcB1: tc_tree_aux => [D1 S1] [??]; subst.
      have [? M] := tc_tree_aux_func2 tcB tcB1; subst.
      by destruct d0, d1, D, D1 => //=; congruence.
    case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
    case eA: step => [A'|A'|A'|A'] => /=.
    - have fA:= step_not_failed _ eA notF.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA']; subst.
      case dtB: (tc_tree_aux _ _ B) => [DB sVB]; subst.
      have /={}HA := HA _ _ _ _ _ _ _ _ _ CO vA SP eA dtA dtA'.
      case: ifP => kB.
        move=> [??]; subst.
        rewrite andbT => + kA'.
        rewrite kA' => -[??]; subst.
        have [{}HA MP] := HA kA'.
        by destruct d0, DA, d1 => //.
      move=> ++ _.
      case dtB': (tc_tree_aux _ _ B) => [DB' sVB'][??]; subst.
      have [? M] := tc_tree_aux_func2 dtB dtB'; subst.
      case: (ifP (is_ko _)) => kA' [??]; subst.
        move: dtA'; rewrite is_ko_tc_tree_aux => //-[??]; subst.
        split; last by apply: more_precise_mergeR (CO) _ _ (more_precise_refl _);
          apply: more_precise_tc_tree_aux1; eauto.
        case: ifP => //= cA.
        destruct d0, DA, DB => //=?; subst.
        destruct DB' => //=; congruence.
      have [{}HA MP] := HA kA'.
      split; last by apply: more_precise_merge2 (CO) _ _ _ _ => //;
        apply: more_precise_tc_tree_aux1; eauto.
      case: ifP => //= cA.
      rewrite (step_keep_cut eA)//cA.
      destruct d0, DA, DB => //=?; subst.
      by destruct DA', DB' => //=; try congruence; auto.
    - have fA:= step_not_failed _ eA notF.
      (* case: ifP => kA; first by rewrite is_ko_step in eA. *)
      have kA' := (expand_CB_is_ko eA).
      rewrite kA' is_ko_cutr.
      case dtA': (tc_tree_aux _ _ A') => [DA' sVA'] + [??] _; subst.
      have /=[{}HA MP] := HA _ _ _ _ _ _ _ _ _ CO vA SP eA dtA dtA' kA'.
      case: ifP => kB.
        move=> [??]; subst.
        split; last by [].
        by destruct d0, DA, d1 => //.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      case:ifP => //cA[??]; subst.
        split; first by by destruct d0, DA, DB, d1 => //=.
        rewrite merge_comm.
        apply: more_precise_mergeR (CO) _ _ MP;
        apply: more_precise_tc_tree_aux1; eauto.
      split => //.
      rewrite merge_comm.
      apply: more_precise_mergeR (CO) _ _ MP;
      apply: more_precise_tc_tree_aux1; eauto.
    - have [? fA] := expand_failed_same _ eA; subst A'.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' sVA']//=.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
      case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
      have [? M2] := tc_tree_aux_func2 dtB1 dtB2; subst.
      rewrite kA.
      case: ifP => kB [??][??] _; subst.
        split; last by []; destruct d0, DA', d1, DA => //=; congruence.
      case:ifP => //=cA.
      split => //=.
      destruct d0, DA, DB1 => //?; subst => /=.
      by destruct d1, DA', DB2 => //=; try congruence.
    - have [? sA]:= expand_solved_same _ eA; subst A'.
      rewrite (success_is_ko sA)//=.
      rewrite success_has_cut//=.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' sVA']//=.
      have [? {}HA] := tc_tree_aux_func2 dtA dtA'; subst.
      case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
      case dtB': (tc_tree_aux _ _ B) => /=[DB2 sVB2]//= ++ _.
      have [? {}HB] := tc_tree_aux_func2 dtB dtB'; subst.
      case:ifP => kB [??] [??]; subst; split => //=.
      by destruct d0, DA, d1, DA' => //=; congruence.
  - move=> A HA B0 HB0 B HB s O N N' r dA dB d0 d1 CO /and4P[vA +++] SP <-.
    case: (ifP (is_ko _)) => kA; first by rewrite is_ko_success// is_ko_failed// is_ko_step//=kA//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA SA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB SB]//=.
    case eA: step => [A'|A'|A'|A'].
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0}.
      rewrite dtB base_and_is_ko// => -[??]; subst.
      case:ifP => kA'//.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??] _; subst.
      rewrite !merge_refl !maxD_refl.
      have CA : closed_in SA by apply: closed_in_mp CO (more_precise_tc_tree_aux1 CO dtA).
      have [{}HA MP] := HA _ _ _ _ _ _ _ _ _ CO vA SP eA dtA dtA' kA'.
      have [->] := more_precise_tc_tree_aux CA dtB dtB' MP.
      split => //.
      destruct DB => //=?; subst.
      by destruct DA, DA', ddB => //=; auto.
    - have fA:= step_not_failed _ eA notF.
      have sA:= expand_not_solved_not_success _ eA notF.
      rewrite fA sA/= => /eqP-> bB _ {B0 HB0}.
      rewrite base_and_is_ko// dtB => -[??]; subst.
      rewrite (expand_CB_is_ko eA)/=.
      case dtA': (tc_tree_aux _ _ A') => /=[DA' SA']//=.
      case dtB' : tc_tree_aux => [ddB sB] [??] _; subst.
      rewrite !merge_refl !maxD_refl.
      have CA : closed_in SA by apply: closed_in_mp CO (more_precise_tc_tree_aux1 CO dtA).
      have [{}HA MP] := HA _ _ _ _ _ _ _ _ _ CO vA SP eA dtA dtA' (expand_CB_is_ko eA).
      have [->] := more_precise_tc_tree_aux CA dtB dtB' MP.
      split => //.
      destruct DB => //=?; subst.
      by destruct DA, DA', ddB => //=; auto.
    - have [? fA]:= expand_failed_same _ eA; subst A'.
      rewrite failed_success//= fA=> /eqP -> {B0 HB0} bB _.
      rewrite dtB kA.
      move/orP: bB => []bB.
        rewrite base_and_is_ko// => -[??]; subst.
        case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
        have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
        case dtB': (tc_tree_aux _ _ B) => /=[DB' sVB']//=[??] _; subst.
        have [? M2] := tc_tree_aux_func2 dtB dtB'; subst.
        rewrite !maxD_refl.
        by destruct DB, d1, DB', DA, DA', d0 => //=; congruence.
      have kB:= base_and_ko_is_ko bB.
      case dtA': (tc_tree_aux _ _ A) => /=[DA' SA']//=.
      have [? M1] := tc_tree_aux_func2 dtA dtA'; subst.
      by move: dtB; rewrite kB !is_ko_tc_tree_aux// => -[??][??][??]; subst.
    - have [? sA] := expand_solved_same _ eA; subst A'.
      rewrite sA/= => vB bB cB.
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
      have ? := success_det_tree_same_ctx CO sA dtA; subst SA.
      case eB: step => //=[B'|B'|B'|B'];
      case dtA': tc_tree_aux => [DA' SA'];
      case dtB': (tc_tree_aux _ _ B') => [DB' SB'];
      case dtB0': tc_tree_aux => [DB0' SB0'] + _; cycle 1;
      [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); rewrite kA; subst..].
      - move: (dtA') (dtB0'); rewrite cutl_tc_tree_aux//= cutr_tc_tree_aux.
        move=> [??][??]; subst SB0' DB0' SA' DA'.
        have /= SP1 := expand_sigP CO SP eA.
        rewrite success_is_ko?success_cut//(expand_CB_is_ko eB)  => -[??]; subst.
        have [{}HB MP] := HB _ _ _ _ _ _ _ _ _ CO vB SP1 eB dtB dtB' (expand_CB_is_ko eB).
        split; first by destruct DB, DB0 => //=?; subst; destruct DB'; auto.
        have MP2 := more_precise_tc_tree_aux1 CO dtB'.
        rewrite merge_comm.
        rewrite more_precise_merge//.
        admit.
      - have [? fB] := expand_failed_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
        have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
        split => //=.
        destruct DB0, DB => //= ?; subst; destruct DB0', DB', DA, DA', d0; auto; try congruence.
      - have [? sB] := expand_solved_same _ eB; subst B'.
        rewrite kB => -[??]; subst.
        have [? m1] := tc_tree_aux_func2 dtB dtB'; subst SB'.
        have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
        split; last by [].
        destruct DB0, DB => //=?; subst.
        destruct DB0', DB', DA', DA, d0 => //=; auto; try congruence.
      - 
        (* move: dtB0' dtB0. *)
        (* rewrite dtB0. *)
      
        have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst SB0'.
        (* have eA' := succes_is_solved u (get_substS s A) sA. *)
        have /= SP1 := expand_sigP CO SP eA.
        have /= {}HB := HB _ _ _ _ _ _ _ _ _ CO vB SP1 eB dtB dtB'.
        case kB': (is_ko B') => -[??]; subst; last first.
          have [{}HB MP]:= HB kB'.
          split; last by apply: more_precise_merge2 (CO) (more_precise_tc_tree_aux1 _ _) (more_precise_tc_tree_aux1 _ _) _ (more_precise_refl _); eauto.
          destruct DB0, DB => //=?; subst.
          move: m m2; rewrite !(@minD_comm _ Func)/=.
          destruct DA'; simpl in *.
            have ? := HB erefl; subst.
            destruct DA => /=; last by move=> _ <-.
            move=> _ _; by destruct DB0' => //; congruence.
          (* qui sono già morto: l'ipotesi HB è la sola che fissa DB', senza non deduco niente *)
          rewrite !(@minD_comm _ Pred)/=.
          rewrite eqxx => + _.
          destruct DA.
            by destruct d0 => //=; congruence.
          move=> _.
          destruct DB0'; [|by congruence] => /=.
          (* QUI il CASINO *)
          admit.
        move: dtB'; rewrite is_ko_tc_tree_aux//= => -[??]; subst.
        (* example here:
           A := ((OK \/ BLI) /\B0 ((Bot \/ f X) /\ !)) con B0 = (g X /\ !)
           si unfolda in `(OK /\ (Bot \/ f X) /\ !)) \/ (BLI /\ (g X /\ !))` con il cut che è superficiale
           simao nel caso in cui `f X` non ha regole da usare, quindi
           lo stato diventerebbe `(OK /\ (Bot \/ Bot) /\ !)) \/ (BLI /\ (g X /\ !))`
        *)
        split.
          destruct DB0, DB, d1, dB, DA, DA', d0 => //=; try congruence.
        apply: more_precise_mergeR (CO) _ _ (more_precise_refl _);
        apply: more_precise_tc_tree_aux1; eauto.
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A (Some s') B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_in sV -> valid_tree A ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None /\ 
        sigP sP s' sV'.
Proof.
  rewrite/is_det.
  move=> ckP ME ++++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV'; clear -ckP ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' H1 vA SP H2.
    have /=-> := success_det_tree_next_alt vA sA H2.
    have ? := success_det_tree_same_ctx H1 sA H2; subst.
    have /=->// := expand_sigP H1 SP (succes_is_solved _ _ sA).
    apply: Build_Unif; move=> *; apply: None.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 vA SP dtA; subst.
    have WS : will_succeed B.
      rewrite/will_succeed; case KB: is_ko => //.
      by have [] := run_consistent _ R (is_ko_runb _ KB).
    case TC: (tc_tree_aux sP sV B Func) => [X Y].
    have/= [+ MP] := expand_det_tree ckP H1 ME vA SP eA dtA TC WS; subst.
    move=> /(_ erefl) ?; subst.
    have [Hx Hy] := IH _ erefl _ _ H1 (valid_tree_expand vA eA) SP TC.
    split => //.
    apply: sigP_more_precise MP Hy.
    apply: closed_in_mp H1 (more_precise_tc_tree_aux1 H1 dtA).
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 vA SP dtA; subst.
    have WS : will_succeed B.
      rewrite/will_succeed; case KB: is_ko => //.
      by have [] := run_consistent _ R (is_ko_runb _ KB).
    case TC: (tc_tree_aux sP sV B Func) => [X Y].
    have/= [+ MP] := expand_det_tree ckP H1 ME vA SP eA dtA TC WS; subst.
    move=> /(_ erefl) ?; subst.
    have [Hx Hy] := IH _ erefl _ _ H1 (valid_tree_expand vA eA) SP TC.
    split => //.
    apply: sigP_more_precise MP Hy.
    apply: closed_in_mp H1 (more_precise_tc_tree_aux1 H1 dtA).
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C vA SP TC; subst.
    have := failed_det_tree_next_alt vA C TC nA.
    move => [[]// [N [? X MP]]]//.
    have [{}IH INV] := IH _ erefl _ _ C (valid_tree_next_alt vA nA) SP X.
    split; first by [].
    apply: sigP_more_precise (closed_in_mp C (more_precise_tc_tree_aux1 C TC)) MP INV.
Qed.

Lemma run_is_detP1 {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_in sV ->
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
    closed_in sV ->  all_weak sV ->
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
    closed_in sV -> all_weak sV ->
      check_callable sP sV c Func = (Func, ign) -> 
      is_det ((call p c):::nilC).
  Proof.
    move=> CkP ME CV F C u s' a'.
    move=> /elpi_to_tree /(_ _ (CallS p c))/=.
    move=> /(_ _ isT erefl) [t1'[n [H3]]].
    have /= := run_is_det CkP ME CV.
    move => /(_ _ _ (CallS p c))/=.
    rewrite C => /(_ _ empty isT (all_weak_sigP_empty F) erefl _ _ _ _ H3).
    move=> [].
    have:= valid_tree_run _ _ H3 => /(_ isT).
    move=> []; first by move=> ->; rewrite t2l_dead//is_dead_dead//.
    move=> vt1' H.
    have ft1':= next_alt_None_failed H.
    have:= failed_next_alt_none_t2l vt1' ft1' H.
    by move=> ->.
  Qed.

End elpi.

(* Print Assumptions tail_cut_is_det. *)

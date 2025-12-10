From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import ctx tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap.

Require Import FunInd.
Functional Scheme expand_ind := Induction for step Sort Prop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope fset_scope.

Ltac foo tcA IH := by move=> [<-<-]; case tcA: tc_tree_aux => [BA BI];
  (try rewrite maxD_comm in tcA); rewrite IH tcA maxD_refl merge_refl.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  (check_atoms sP sV l r) = tc_tree_aux sP sV (big_and p l) r.
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [dA sVA].
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
          (minD (maxD d0 D) d1 = d1 -> minD (maxD d0 D) dB = dB) /\
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
      destruct d0, d, d1, dB => //=; exfalso.
      admit.
    
    apply: more_precise_trans (more_precise_tc_tree_aux1 CO tc) _.


Admitted.

Lemma step_Exp_det u sP O s B B' N N' sVA' P:
  check_program sP -> closed_in O -> mutual_exclusion ->
  sigP sP s O ->
  tc_tree_aux sP sVA' B Pred = (Func, N) ->
    step u s B = Expanded B' ->
       tc_tree_aux sP sVA' B' Pred = (P, N') ->
        P = Func.
Admitted.


Lemma expand_det_tree {u sP O N A r s d0 d1 dA dB N'} : 
  check_program sP -> closed_in O -> mutual_exclusion ->
    sigP sP s O ->
      tc_tree_aux sP O A d0 = (dA, N) ->
        step u s A = r -> 
          will_succeed (get_tree r) ->
            tc_tree_aux sP O (get_tree r) d1 = (dB, N') ->
          [/\ (minD dA d1 = d1 -> minD dA dB = dB) & more_precise N' N].
Proof.
  rewrite/will_succeed.
  move=> CkP + ME.
  move: O N N' r dA dB d0 d1.
  pattern u, s, A, (step u s A).
  apply: expand_ind; clear -CkP ME.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] ?; subst=>/=; repeat eexists.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] <-/= _ [??]; subst=>/=; repeat eexists.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] ?; subst=>/=; repeat eexists; rewrite ?minD_refl//.
  - (*here the checker comes into the game*)
    move=> /=s A pr t HA O N N' _ dA dB d0 d1 C SP + <-/=.
    {
      case CC: check_callable => [D B] [??]; subst.
      rewrite/big_or/=.
      case X: F => [|[sr1 r1] rs]//= _.
      by apply: check_callable_main X.
    }
  - move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] <-/= _ [??] ; subst=>/=; repeat eexists => //=.
  - move=> s INIT A sB B HINIT deadA IH O N N' r dA dB d0 d1 CO /=.
    rewrite is_dead_is_ko//=?deadA => SP.
    move=> tcA <-/=.
    rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
    apply: IH; eauto.
    admit.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-/={r}.
    rewrite ?(step_not_dead _ deadA eA) ?deadA => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA.
      rewrite andbT => /[dup] kA' -> tcA'.
      by have:= IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' tcA'.
    have fA:= step_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    rewrite (expand_Exp_has_cut eA).
    case kA' : (is_ko A').
      rewrite failed_has_cut?is_ko_failed//=.
      move=> [??] _ dtB'; subst.
      repeat eexists.
      have ? := more_precise_tc_tree_aux1 CO dtB.
      have [? _] := tc_tree_aux_func2 dtB dtB'; subst.
      have ? := more_precise_tc_tree_aux1 CO dtA.
      by apply: more_precise_mergeR.
    move=> [??] _; subst.
    case dtA2: (tc_tree_aux _ _ A') => [DA2 sVA2].
    case dtB1: (tc_tree_aux _ _ B) => [DB2 sVB2].
    move=> [??]; subst.
    have /=[H1 MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA2.
    have /=[? ] := tc_tree_aux_func2 dtB dtB1; subst.
    split.
      case: ifP => cA/=; last by [].
      destruct DA', DB => //=?; subst.
      have {H1}/=? := H1 erefl; subst.
      destruct d0 => //=; congruence.
    by apply: more_precise_merge2 (CO) _ _ MP (more_precise_refl _);
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    have kA' := (expand_CB_is_ko eA).
    rewrite kA' is_ko_cutr.
    case: ifP => kB.
      move=> dtA /= _ tcA'.
      by apply: IH eA _ _; eauto.
    have fA:= step_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> [??]; subst => /= _ dtA'.
    have /=[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    split.
      case:ifP => cA/=; last by [].
      by destruct DA', DB, d1, dB.
    rewrite merge_comm.
    by apply: more_precise_mergeR (CO) _ _ MP;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    have [? fA] := expand_failed_same _ eA; subst A'.
    case: ifP => kA.
      move=> dtB /= kB tcB.
      have [? M] := tc_tree_aux_func2 dtB tcB; subst.
      split => //=; destruct d1, dA, dB, d0 => //=; congruence.
    case: ifP => kB; first by move=> dtA1 _; apply: IH eA _; eauto.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA1 dtA2; subst.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
    have [? HB] := tc_tree_aux_func2 dtB1 dtB2; subst.
    by rewrite failed_has_cut//= => -[??] _ [??]; subst.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite success_has_cut//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA': (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA dtA'; subst.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB': (tc_tree_aux _ _ B) => /=[DB2 sVB2]//= + _.
    have [? HB] := tc_tree_aux_func2 dtB dtB'; subst.
    have /=[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA (success_is_ko sA) dtA'.
    by case:ifP => kB [??][??]; subst; repeat split.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have fA:= step_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=?sA => SP.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??] kA'; subst.
    rewrite kA'.
    case dtA': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    case dtB' : tc_tree_aux => [ddB sB].
    case dtB0' : tc_tree_aux => [ddB0 sB0].
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA1 by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    (case: ifP => sA'; first (case nA': next_alt => [v|])) => -[??]; subst; split.
      destruct DB01, DB1 => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
      destruct DB01, DB1, dB, DA1 => //=?; subst; auto.
        rewrite merge_comm.
      apply: more_precise_mergeR (CA) _ _ MP1;
      apply: more_precise_tc_tree_aux1; eauto.
    destruct DB01, DB1, DA1, d1, ddB0, ddB => //=?; subst; auto.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have fA:= step_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=?sA => SP.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??] kA'; subst.
    rewrite kA'.
    case dtA': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    case dtB' : tc_tree_aux => [ddB sB].
    case dtB0' : tc_tree_aux => [ddB0 sB0].
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA1 by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    (case: ifP => sA'; first (case nA': next_alt => [v|])) => -[??]; subst; split.
      destruct DB01, DB1 => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
      destruct DB01, DB1, dB, DA1 => //=?; subst; auto.
        rewrite merge_comm.
      apply: more_precise_mergeR (CA) _ _ MP1;
      apply: more_precise_tc_tree_aux1; eauto.
    destruct DB01, DB1, DA1, d1, ddB0, ddB => //=?; subst; auto.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have [? fA]:= expand_failed_same _ eA; subst A'.
    rewrite ?failed_success//= => SP.
    case:ifP => kA.
      by move=> [??]; subst; repeat eexists; rewrite ?minD_refl.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=[??]; subst.
    case dtA': (tc_tree_aux _ _ A) => /=[DA1 sVA1].
    case dtB': (tc_tree_aux _ _ B) => /=[DB1 sVB1].
    case dtB0': (tc_tree_aux _ _ B0) => /=[DB01 sVB01] _ [??]; subst.
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    split.
      destruct DB0, DB => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT HL A' eA HR O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have [? sA] := expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite ?sA.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> SP.
    have ? := success_det_tree_same_ctx CO sA dtA; subst sVA.
    case eB: step => //=[B'|B'|B'|B']; rewrite success_is_ko//?success_cut//;
    case dtA': tc_tree_aux => [DA2 sVA'];
    case dtB': tc_tree_aux => [DB2 sVB'];
    case dtB0': tc_tree_aux => [DB02 sVB0']; cycle 1; rewrite sA?nA;
    [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); subst..].
    - rewrite next_alt_cutl => /= + _ [??]; subst.
      move: (dtA') (dtB0'); rewrite cutl_tc_tree_aux//=cutr_tc_tree_aux.
      move=> [??][??]; subst sVB0' DB02 sVA' DA2.
      have /= SP1 := expand_sigP CO SP eA.
      have /=[H MP] := HR _ _ _ _ _ _ _ _ CO SP1 dtB eB (expand_CB_is_ko eB) dtB'.
      case nA: next_alt => [v|][??]; subst; last by [].
      split; first by destruct DB0, DB => //=?; subst.
      have MP2 := more_precise_tc_tree_aux1 CO dtB'.
      rewrite merge_comm.
      apply: more_precise_mergeR (CO) _ _ MP;
      apply: more_precise_tc_tree_aux1; eauto.
    - have [? fB] := expand_failed_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
      case nA: next_alt => [v|][??] _ [??]; subst.
        repeat eexists; last by [].
        destruct DB0, DB => //=?; subst.
        by destruct DB02, DB2, DA', DA2, d0 => //=; congruence.
      repeat eexists; last by [].
      destruct dA, dB, d1 => //=?; subst.
      destruct DA', DA2, d0; simpl in *; try congruence.
    - have [? sB] := expand_solved_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst sVB'.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst sVB0'.
      case nA: next_alt => [v|][??] _ [??]; subst.
        repeat eexists; last by [].
        destruct DB0, DB => //=?; subst.
        by destruct DB02, DB2, DA', DA2, d0 => //=; congruence.
      repeat eexists; last by [].
      destruct dA, dB, d1 => //=?; subst.
      destruct DA', DA2, d0; simpl in *; try congruence.
    - have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst sVB0'.
      have eA' := succes_is_solved u (get_substS s A) sA.
      have/=[H MP] := HL _ _ _ _ _ _ _ _ CO SP dtA eA (success_is_ko sA) dtA'.
      case kB': (is_ko B').
        move: dtB'.
        rewrite is_ko_tc_tree_aux// => -[??]; subst DB2 sVB'.
        case nA: next_alt => [v|][??] _ [??]; subst.
        (* split. *)
          (* TODO: here *)
          (* destruct DB0, DB => //=?; subst.
          simpl in *; destruct DA2, DB02, DA', d0 => //=; auto; try congruence.
            by have:= step_Exp_det CkP CO ME SP1 dtB eB dtB'.
          by have:= step_Exp_det CkP CO ME SP1 dtB eB dtB'. *)

          admit.
        admit.
      have /= SP1 := expand_sigP CO SP eA.
      have {HR}/= [H1 MP2] := HR _ _ _ _ _ _ _ _ CO SP1 dtB eB kB' dtB'.
      case nA: next_alt => [v|][??] _ [??]; subst.
        split.
          destruct DB0, DB => //=?; subst.
          simpl in *; destruct DA2, DB2, DB02, DA', d0 => //=; auto; try congruence.
            by have:= step_Exp_det CkP CO ME SP1 dtB eB dtB'.
          by have:= step_Exp_det CkP CO ME SP1 dtB eB dtB'.
        by apply: more_precise_merge2 (CO) (more_precise_tc_tree_aux1 _ _) (more_precise_tc_tree_aux1 _ _) _ (more_precise_refl _); eauto.
      split; last by [].
      destruct dA, d1, DA2, dB, DA' => //= _; simpl in *.
      by have:= step_Exp_det CkP CO ME SP1 dtB eB dtB'.
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A (Some s') B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_in sV ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None /\ 
        sigP sP s' sV'.
Proof.
  rewrite/is_det.
  move=> ckP ME +++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV'; clear -ckP ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' H1 SP H2.
    have /=-> := success_det_tree_next_alt sA H2.
    have ? := success_det_tree_same_ctx H1 sA H2; subst.
    have /=->// := expand_sigP H1 SP (succes_is_solved _ _ sA).
    apply: Build_Unif; move=> *; apply: None.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 SP dtA; subst.
    suffices WS : will_succeed B.
      case TC: (tc_tree_aux sP sV B Func) => [X Y].
      have/= [+ MP] := expand_det_tree ckP H1 ME SP dtA eA WS TC; subst.
      move=> /(_ erefl) ?; subst.
      have [Hx Hy] := IH _ erefl _ _ H1 SP TC.
      split => //.
      by apply: sigP_more_precise MP Hy.
    rewrite/will_succeed.
    case KB: is_ko => //.
    by have [] := run_consistent _ R (is_ko_runb _ KB).
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 SP dtA; subst.
    suffices WS : will_succeed B.
      case TC: (tc_tree_aux sP sV B Func) => [X Y].
      have/= [+ MP] := expand_det_tree ckP H1 ME SP dtA eA WS TC; subst.
      move=> /(_ erefl) ?; subst.
      have [Hx Hy] := IH _ erefl _ _ H1 SP TC.
      split => //.
      by apply: sigP_more_precise MP Hy.
    rewrite/will_succeed.
    case KB: is_ko => //.
    by have [] := run_consistent _ R (is_ko_runb _ KB).
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C SP TC; subst.
    have := failed_det_tree_next_alt C TC nA.
    move => [[]// [N [? [X MP]]]]//.
    have [-> H]:= IH _ erefl _ _ C SP X.
    split => //=.
    by apply: sigP_more_precise MP H.
Qed.

Lemma run_is_detP1 {sP sV sV' s A}: 
  check_program sP -> mutual_exclusion ->
  closed_in sV ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None.
Proof.
  move=> CkP ME C S TC u s' B n R.
  by have [] := run_is_det CkP ME C S TC R.
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
    rewrite C => /(_ _ empty (all_weak_sigP_empty F) erefl _ _ _ _ H3).
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

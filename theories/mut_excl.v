From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars fresh unif.

Section mut_excl.
  Variable u : Unif.

  (* returns if all inputs can be unified *)
  (* inputs come before outputs *)
  (* outputs are neutral for this function *)
  Fixpoint H_head (sP:sigT) (q : Tm) (h: Tm) : option S :=
  match q,h with
  | Tm_P p, Tm_P p' => 
    if p == p' then sP.[?p] 
    else None
  | Tm_App f a, Tm_App f' a' =>
    if H_head sP f f' is Some (arr m _ r) then
      if (m == output) || lang.unify u f f' fmap0 then Some r
      else None
    else None
  | _, _ => None
  end.

  Lemma H_headP sP t1 t2 r: H_head sP t1 t2 = Some r -> 
    [/\ get_tm_hd t1 = get_tm_hd t2, term_arg t1 = term_arg t2 &
      exists p, exists2 pP : p \in sP, get_tm_hd t1 = inl p & eat_ty (term_arg t1) sP.[pP] = Some r]
    .
  Proof.
    elim: t1 t2 r => //=[p|f Hf a _] [p'|d|v|f' a']//=r.
      case: eqP => //<-; case: fndP => //=pP[<-]; split => //.
      by exists p, pP.
    case H: H_head => [[|m tl tr]|]//=.
    case: ifP => []// _ [<-{r}].
    have /=[Hx Hy [p [pP H1 H2]]] := Hf _ _ H.
    rewrite Hx Hy; split => //; rewrite -Hy -Hx.
    exists p, pP => //.
    move: H2; case: sP.[pP] => //=; first by case: term_arg.
    clear => md tf ta; apply: eat_ty_arr.
  Qed.

  Fixpoint select_head (sP:sigT) (q: Tm) (rules: list R) : seq R :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head sP q rules in
      if H_head sP q rule.(head) then rule :: tl else tl
    end.

  Definition mut_excl_head (sig:sigT) (r:R) rules :=
    ~~ tm_is_det sig r.(head) ||
    let query := r.(head) in
    (* TODO: the check is done only on deterministic predicate *)
    all_but_last (fun x => has_cut_seq x.(premises)) (r :: select_head sig query rules).

  Fixpoint mut_excl_aux sig rules :=
    match rules with
    | [::] => true
    | x :: xs => mut_excl_head sig x xs && mut_excl_aux sig xs
    end.

  Fixpoint all_mode dfl m :=
    match m with b _ => true | arr m _ r => (m == dfl) && all_mode dfl r end.

  Definition all_out := all_mode output.
  Definition all_inp := all_mode input.

  Fixpoint good_mode m :=
    match m with
    | b _ => true
    | arr input _ r => good_mode r
    | arr output _ r => all_out r
    end.

  Definition good_modes (s: sigT) := [forall x : domf s, good_mode s.[valP x]].

  Lemma good_modes_in p sP (pP: p  \in domf sP):
    good_modes sP -> good_mode sP.[pP].
  Proof. by move=> GM; have:= forallP GM [`pP]; rewrite valPE. Qed.

  Definition mut_excl pr :=
    let: (fv, rules) := fresh_rules fset0 pr.(rules) in
    good_modes pr.(sig) && mut_excl_aux pr.(sig) rules.

  Lemma callable_ren m hd p:
    get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. by elim: hd => //= [q|d|v|f Hf a Ha]. Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed.

  Lemma is_det_cder s s1 c: tm_is_det s c -> tm_is_det s (deref s1 c).
  Proof. elim: c s => //=[p|f Hf a Ha] s; rewrite ?deref_P//. Qed.

  Lemma is_det_lookup p c s (pP: p \in domf s):
    get_tm_hd c = inl p -> tm_is_det s c -> is_det_sig s.[pP].
  Proof. by elim: c p s pP => //=p1 p2 s pP [->]; rewrite/tm_is_det/=in_fnd//. Qed.

  Lemma count_tm_ag_deref s c p: 
    get_tm_hd c = inl p -> count_tm_ag (deref s c) = count_tm_ag c.
  Proof. elim: c p s => //f Hf a Ha q s/= H; rewrite (Hf _ _ H)//. Qed.

  (* Lemma all_inp_cons x xs: all_out (x::xs) -> all_out xs.
  Proof. by move=> /andP[]. Qed. *)

  Definition vars_tms t := varsU (map vars_tm t).

  Lemma vars_tms_cons x xs: vars_tms (x::xs) = vars_tm x `|` vars_tms xs.
  Proof. by []. Qed.
End mut_excl.

(* Lemma H_head_comm sP t1 t2: H_head u sP t1 t2 = H_head u sP t2 t1.
Proof.
  elim: t1 t2 => [p|d|v|f Hf a _] [p'|d'|v'|f' a']//=.
    by rewrite eq_sym; case: eqP => //?; subst.
  rewrite Hf; case: H_head => //[[|[]]]//= _ s.
  Search unify.
  Search montanari "comm".
  rewrite /unify/montanari_deref. unif_pair_comm. *)
  

Lemma all_out_good_mode l: all_out l -> good_mode l.
Proof. elim: l => //= -[]//. Qed.

Lemma all_out_good_modeM m tl:
  match m with
  | output => all_out tl
  | input => good_mode tl
  end -> good_mode tl.
Proof. by case: m => ///all_out_good_mode. Qed.

Lemma vars_tms_rcons f a: 
  vars_tms (rcons f a) = vars_tm a `|` vars_tms f.
Proof. by elim: f a => //= x xs IH a; rewrite !vars_tms_cons IH fsetUA (fsetUC (vars_tm x)) fsetUA. Qed.

Lemma vars_tms_flatten_term hd': 
  vars_tms (flatten_term hd') `<=` vars_tm hd'.
Proof. elim: hd' => //= f Hf a Ha; rewrite vars_tms_rcons fsetUC fsetSU//. Qed.

Lemma fdisjoint_ftl s q : [disjoint vars_tm s & q] -> [disjoint vars_tms (flatten_term s) & q].
Proof. by apply/fdisjointWl/vars_tms_flatten_term. Qed.

Lemma fdisjoint_ftr s q : [disjoint q & vars_tm s] -> [disjoint q & vars_tms (flatten_term s)].
Proof. by apply/fdisjointWr/vars_tms_flatten_term. Qed.

Lemma fdisjoint_ft2 s q : [disjoint vars_tm q & vars_tm s] -> 
  [disjoint vars_tms (flatten_term q) & vars_tms (flatten_term s)].
Proof. by move=> H; apply/fdisjointWr/fdisjoint_ftl/H/vars_tms_flatten_term. Qed.

Definition u := mk_Unif unify matching.

Lemma not_in_deref_L s l:
  domf s # vars_tms l -> map (deref s) l = l.
Proof.
  elim: l => //= x xs H; rewrite vars_tms_cons fdisjointXU => /andP[D1 /H->].
  by rewrite not_in_deref//.
Qed.

Lemma eat_ty_inp n t m t1 t2 t3:
  good_mode t ->
  eat_ty n t = Some (arr m t1 (arr input t2 t3)) ->
  m = input.
Proof.
  elim: n t m t1 t2 t3 => [[//|]|n IH]//=.
    by move=> m ?? m' > + [???]; subst; case: m' => //.
  by move=> [|[]]//= _ s m t1 t2 t3 /all_out_good_mode; apply: IH.
Qed.

Lemma H_all_inp_v2 sP v1 t1 t2 tf tr s1 s2 v2:
  good_modes sP ->
  H u sP v1 t1 t2 s1 = Some (tf --i--> tr, s2, v2) -> v2 = v1 `|` vars_tm t1.
Proof.
  move=> GM.
  elim: t1 t2 s1 s2 v1 v2 tf tr => [p|//|//|f Hf a _] [p'|//|//|f' a']//= s1 s2 v1 v2 tf tr.
    case: eqP => //=; case: fndP => //=pP _ [H ??]; subst.
    by rewrite fsetU0.
  case H: H => [[[[|m tf' tr'] s1' v1']]|]//=.
  case I:  (_ s1') => //= -[???]; subst.
  have /=[hff' aff' [p[pP H1 E]]] := HP H.
  have := forallP GM [`pP]; rewrite valPE => {}GM.
  have ? := eat_ty_inp GM E; subst => /=.
  simpl in I.
  have ? := Hf _ _ _ _ _ _ _ H; subst.
  by rewrite fsetUA.
Qed.

Lemma fdisjoint_rem (K: choiceType) (qa qf:{fset K}) :
  (qa `\` qf) # qf.
Proof. by apply/fdisjointP => k; rewrite !inE => /andP[]. Qed.

Lemma H_all_inp sP v1 query head tf tr s1 s2 v2:
  acyclic_sigma s1 ->
  good_modes sP ->
  fdisjoint (domf s1) (vars_tm query) ->
  fdisjoint (vars_tm query) (vars_tm head) ->
  H u sP v1 query head s1 = Some (tf --i--> tr, s2, v2) ->
  matching (v1 `|` v2) head query s1 = Some s2.
Proof.
  move=> + GM.
  elim: query head s1 s2 v1 v2 tf tr => [p|//|//|qf Hf qa _] [p'|//|//|hf ha]//= s1 s2 v1 v2 tf tr Ac.
    by case: eqP => //<- _ _; case: fndP => //= pP [_ <- _]; rewrite matching_refl.
  case H: H => [[[[|m tf' ta'] s1'] v1']|]//=.
  rewrite !fdisjointUX !fdisjointXU -!andbA.
  move=> /andP[s1f s1a].
  move=> /and4P[ff' fa' af' aa'].
  case I: (_ s1') => [r|]//= [???]; subst.
  have [Hh Ha [p[pP fp A]]] := HP H.
  have:= forallP GM [`pP]; rewrite valPE => GM'.
  have ?:= eat_ty_inp GM' A; subst.
  have {Hf} M1 := Hf _ _ _ _ _ _ _ Ac s1f ff' H.
  rewrite/= in I *.
  have ? := H_all_inp_v2 GM H; subst.
  rewrite !fsetUA fsetUid in M1 *.
  case: (boolP (hf == qf)) => /eqP hfqf; subst.
    rewrite /matching/montanari_deref/montanari_pair in I.
    move: M1; rewrite matching_refl => -[?]; subst.
    rewrite /matching/montanari_deref/montanari_pair 2!montanari_equation/=.
    rewrite montanari_equation eqxx I.
    case: eqP => //=-[D].
    by move: I; rewrite 2!montanari_equation/= D eqxx.
  
  have:= matching_ext1 M1.
Admitted.

(* Definition get_sigP f sP t :=
  get_tm_hd  *)

(* TODO: refactor this lemma: 
   prove an auxiliary lemma saying that H a b -> H a c -> H b c
   under some conditions of about disjointness
   then prove that H a b -> H_head a b
*)
Lemma SHS sP fv1 fv2 query hd2 hd1 (s1 s2:Sigma):
  good_modes sP ->
  acyclic_sigma s1 -> acyclic_sigma s2 ->
  [disjoint vars_sigma s1 & vars_tm hd2] -> 
  [disjoint vars_sigma s2 & vars_tm hd1] -> 
  [disjoint vars_tm hd1 & vars_tm hd2] ->
  [disjoint vars_tm query & vars_tm hd1] ->
  [disjoint vars_tm query & vars_tm hd2] ->
  [disjoint domf s1 & vars_tm query] ->
  [disjoint domf s2 & vars_tm query] ->
  H u sP fv1 query hd1 s1 ->
  H u sP fv2 query hd2 s2 ->
  H_head u sP hd1 hd2.
Proof.
  move=> GM.
  elim: query fv1 fv2 hd1 hd2 s1 s2 => //=[p|f Hf a _];
  move=> fv1 fv2 [p1|d1|v1|f1 a1]//[p2|d2|v2|f2 a2]//=  s1 s2 A1 A2.
    by move=> _ _ _ _ _ _ _; case: eqP => //<-; case: eqP =>//; case: fndP.
  rewrite 2!fdisjointXU => /andP[V1 V2] /andP[V3 V4].
  rewrite ?fdisjointUX !fdisjointXU.
  move=> /andP[/andP[f1f2 f1a2] /andP[a1f2 a1a2]].
  move=> /andP[/andP[ff1 fa1] /andP[af1 aa1]].
  move=> /andP[/andP[ff2 fa2] /andP[af2 aa2]].
  (* move=> /andP[Da Db] /andP[Dc Dd]. *)
  move=> /andP[s1f s1a] .
  move=> /andP[s2f s2a] .
  case H1 : H => //=[[[[//|m1 tf1 ta1] s1' fv1']]].
  case H2 : H => //=[[[[//|m2 tf2 ta2] s2' fv2']]].
  have {Hf} := Hf _ _ _ _ _ _ A1 A2 V1 V3 f1f2 ff1 ff2 s1f s2f (isSomeP H1) (isSomeP H2).
  case HH: H_head => //=[ty'] _.
  have [hh1 ha1 [p[pP hf1 he]]] := HP H1.
  have:= HP H2.
  rewrite hh1 ha1 => -[hh2 ha2 [p'[pP']]].
  rewrite -hh1 hf1 => /esym [?]; subst.
  rewrite (bool_irrelevance pP' pP) -ha1 he => -[???]; subst.
  case I1: (_ s1') => //=[r1]. 
  case I2: (_ s2') => //=[r2] _ _.
  have [Hx Hy [p'[{}pP']]] := H_headP HH.
  rewrite -hh1 hf1 => -[?]; subst.
  rewrite -ha1 (bool_irrelevance pP' pP) he => -[?]; subst.
  rewrite ifT => //.
  case: m2 I1 I2 H1 H2 he HH => //= _ _ H1 H2 he HH.
  have ->// : unify f1 f2 empty.
  have:= forallP GM [`pP]; rewrite valPE => GM'.
  (* have: codom_vars s1 # vars_tm f1. *)
  have:= isSomeP (H_all_inp A2 GM s2f ff2 H2).
  have:= isSomeP (H_all_inp A1 GM s1f ff1 H1).
  apply: matching_unify_trans => //=.
    by rewrite fdisjoint_sym.
    by rewrite fdisjoint_sym.
    by have ? := H_all_inp_v2 GM H1; subst; rewrite fsubsetU// fsubsetUr orbT.
  by have ? := H_all_inp_v2 GM H2; subst; rewrite fsubsetU// fsubsetUr orbT.
Qed.

Lemma vars_tm_take_sub n a: vars_tms (take n a) `<=` vars_tms a.
Proof.  
  elim: n a => // [|n IH] t; first by rewrite take0.
  by destruct t => //=; rewrite !vars_tms_cons; apply/fsetUS/IH.
Qed.

Lemma disjoint_takel n a b:
  [disjoint vars_tms a & b] -> [disjoint vars_tms (take n a) & b].
Proof. by apply/fdisjointWl/vars_tm_take_sub. Qed.

Lemma disjoint_taker n a b:
  [disjoint b & vars_tms a] -> [disjoint b & vars_tms (take n a)].
Proof. by rewrite !(fdisjoint_sym b); apply: disjoint_takel. Qed.

Lemma disjoint_take2 m n a b:
  [disjoint vars_tms b & vars_tms a] -> [disjoint vars_tms (take m b) & vars_tms (take n a)].
Proof. by move=> H; apply/disjoint_takel/disjoint_taker. Qed.

Lemma disjoint_takeLr T n a f (b: seq T):
  [disjoint a & vars_tms (map f b)] -> [disjoint a & vars_tms (map f (take n b))].
Proof.
  move=> H; apply/fdisjointWr/H.
  elim: n b {H} => [|n IH] b; first by rewrite take0.
  by case: b => //=x xs; rewrite !vars_tms_cons; apply/fsetUS/IH.
Qed.

Definition v_prog pr := varsU (map varsU_rule pr).

Lemma v_prog_cons x xs: v_prog (x::xs) = varsU_rhead x `|` varsU_rprem x `|` v_prog xs.
Proof. by []. Qed.


Lemma HSH sP fv rules hd query s: 
  good_modes sP ->
  acyclic_sigma s ->
  [disjoint domf s & vars_tm query] ->
  [disjoint vars_tm hd & v_prog rules] ->
  [disjoint vars_tm query & v_prog rules] ->
  [disjoint vars_tm query & vars_tm hd] ->
  [disjoint vars_sigma s & v_prog rules] ->
  [disjoint vars_sigma s & vars_tm hd] ->
  H u sP fv query hd s ->
  select_head u sP hd rules = [::] ->
  (select u sP query rules s).2 = [::].
Proof.
  move=> GM.
  elim: rules query s hd fv => //=-[hd bo] rs IH/= query s h' fv AS D.
  rewrite !v_prog_cons /varsU_rhead /varsU_rprem/=.
  rewrite !fdisjointXU -!andbA => /and3P[hh' hb' hr'] /and3P[ch cb cr] ch' ++ H1.
  move=> /and3P[Dh Db Dr] Dh'.
  (* case:eqP => //=; last by move=> _; apply:IH. *)
  (* move=> /esym Hd. *)
  case HH: H_head => //= S1.
  have {S1} IH := IH _ _ _ _ AS D hr' cr ch' Dr Dh' H1 S1.
  case H2: H => [[[ty s' fv']]|]//{IH}.
  have {}HH := isNoneP HH.
  exfalso; apply: negP HH; rewrite negbK.
  by apply: SHS H1 (isSomeP H2).
Qed.

Lemma flatten_term_ren z q:
  flatten_term (ren z q) = map (ren z) (flatten_term q).
Proof. by elim: q => [p|d|v|f Hf a Ha]; rewrite//= map_rcons Hf. Qed.

Lemma boolI T (b1 b2: option T): b1 -> b2 -> isSome b1 = isSome b2.
Proof. case: b1; case: b2 => //. Qed.

Lemma H_head_ren_aux sP hd q x y z w:
  (refresh_for y) hd -> (refresh_for x) hd ->
  (refresh_for z) q -> (refresh_for w) q ->
  [disjoint codomf z & codomf x] ->
  [disjoint codomf w & codomf y] ->
  (H_head u sP (ren z q) (ren x hd)) = H_head u sP (ren w q) (ren y hd).
Proof.
  move=> ++++ D2 D3.
  elim: q hd => //=[p|f Hf a _] [p'|//|//|f' a']//=.
  rewrite/refresh_for/= !fsubUset -!andbA.
  move => /and3P[f'y a'y iy] /and3P[f'x a'x ix] /and3P[fz az iz] /and3P[fw aw iw].
  have {Hf} := Hf f'.
  rewrite /refresh_for ?(f'y, iy, f'x, ix, fz, iz, fw, iw)// .
  move=> /(_ isT isT isT isT) ->.
  case HH: H_head => [[|[]]|]//=.
  have ->// : isSome (unify (ren z f) (ren x f') empty) = isSome (unify (ren w f) (ren y f') empty).
  have:= @unif_ren x y z w f f'.
  rewrite/refresh_for ?(f'y, iy, f'x, ix, fz, iz, fw, iw).
  have H: vars (ren z f) # vars (ren x f').
    apply: fdisjointWl (vars_tm_ren_sub fz) _.
    by apply: fdisjointWr (vars_tm_ren_sub f'x) _.
  move=> /(_ isT isT isT isT H).
  case U1: unify => //=; first by move=> /(_ isT)->.
  have:= @unif_ren y x w z f f'.
  rewrite/refresh_for ?(f'y, iy, f'x, ix, fz, iz, fw, iw).
  have H': vars (ren w f) # vars (ren y f').
    apply: fdisjointWl (vars_tm_ren_sub fw) _.
    by apply: fdisjointWr (vars_tm_ren_sub _) _.
  move=> /(_ isT isT isT isT H').
  by rewrite U1; case: unify => //= _ /(_ isT).
Qed.

Lemma good_ren_fresh s t q: 
  vars_tm t `<=` vars_tm q -> vars_tm q `<=` s -> refresh_for (fresh_tm s empty q).2 t.
Proof.
  move=> Hx H.
  have:= @fresh_tm_def s empty q.
  rewrite/refresh_for.
  rewrite /=fsub0set injectiveb0 => /(_ isT H isT).
  move=> [x [H1 HH I1 D1]]; rewrite cat0f in H1; subst.
  apply/andP; split => //.
  by apply/fsubset_trans/fresh_tm_sub1.
Qed.

Lemma good_ren_fresh_all s t q: 
  vars_tms t `<=` vars_tm q -> vars_tm q `<=` s ->
    all (refresh_for (fresh_tm s empty q).2) t.
Proof.
  move=> + Hx.
  elim: t => //=x xs IH.
  rewrite vars_tms_cons fsubUset => /andP[H1 H2].
  rewrite IH// andbT.
  apply/good_ren_fresh => //.
Qed.

Lemma H_head_ren sP fv1 fv2 t xs fx fy q:
  (lang.rename (fresh_rules fv1 xs).1 t empty).1.1 `<=` fx ->
  (lang.rename (fresh_rules fv2 xs).1 t empty).1.1 `<=` fy ->
  H_head u sP ((lang.rename fx q empty).2) ((lang.rename (fresh_rules fv1 xs).1 t empty).2) =
  H_head u sP ((lang.rename fy q empty).2) ((lang.rename (fresh_rules fv2 xs).1 t empty).2).
Proof.
  rewrite/lang.rename!push/=.
  set X:= fresh_tm _ _ _.
  set Y:= fresh_tm _ _ _.
  set W:= fresh_tm _ _ _.
  set Z:= fresh_tm _ _ _.
  move=> H1 H2.
  apply: H_head_ren_aux => //; only 1-4:
    by apply: good_ren_fresh; rewrite //?(vars_tms_flatten_term, fsubsetUl)//.
  apply: fdisjointWr (disj_codom0R _ _).
  apply: fsubset_trans (fresh_tm_codom2 _ _ _) _.
  rewrite codomf0 fset0U//.
  apply: fdisjointWr (disj_codom0R _ _).
  apply: fsubset_trans (fresh_tm_codom2 _ _ _) _.
  rewrite codomf0 fset0U//.
Qed.

Lemma callable_rename1 p fv1 hd mp: 
  (get_tm_hd (lang.rename fv1 hd mp).2 == inl p) = (get_tm_hd hd == inl p).
Proof.
  case:eqP; case:eqP => //= H1 H2.
    by move/callable_rename: H1 => /(_ _ _ H2).
  by have:= H2 (proj2 (callable_rename _ _ _ _) _); auto.
Qed.

Lemma select_head_ren sP rs fx fy fv1 fv2 hd:
  let FRS1 := fresh_rules fv1 rs in
  let FRS2 := fresh_rules fv2 rs in
  (* get_tm_hd hd = inl p -> *)
  FRS1.1 `<=` fx ->
  FRS2.1 `<=` fy ->
  select_head u sP ((lang.rename fx hd empty).2) FRS1.2 = [::] ->
  select_head u sP ((lang.rename fy hd empty).2) FRS2.2 = [::].
Proof.
  elim: rs fx fy fv1 fv2 hd => //= x xs IH fx fy fv1 fv2 hd; rewrite !push/=.
  move=> H2 H3.
  rewrite !(head_fresh_rule).
  (* case: eqP => //= Hd; last first.
    apply: IH.
      by apply/fsubset_trans/H2/fresh_rule_sub.
    by apply/fsubset_trans/H3/fresh_rule_sub. *)
  case H: H_head => //=.
  rewrite /fresh_rule!push/= in H2 H3.
  have {}H2' := fsubset_trans (fresh_atoms_sub _ _ _) H2.
  have {}H3' := fsubset_trans (fresh_atoms_sub _ _ _) H3.
  have {}H2' := fsubset_trans (vars_tm_rename _ _) H2'.
  have {}H3' := fsubset_trans (vars_tm_rename _ _) H3'.
  rewrite (@H_head_ren _ _ fv1 _ _ _ fx)//=.
    by rewrite H//=; apply: IH; (apply:fsubset_trans; first apply: fresh_rule_sub); rewrite/fresh_rule?push//=.
  by apply: fsubset_trans H3; apply: fsubset_trans (fresh_atoms_sub _ _ _).
  by apply: fsubset_trans H2; apply: fsubset_trans (fresh_atoms_sub _ _ _).
Qed.

Lemma build_and (a b: bool): a -> b -> a && b. by move=> ??; apply/andP. Qed.

Lemma mut_exclP p fv c s1:
  mut_excl u p -> 
    tm_is_det p (deref s1 c) ->
      all_but_last (fun x => has_cut_seq x.2) (bc u p fv c s1).2.
Proof.
  rewrite/bc.
  case: p => [rs sP]/=+TD.
  case: ifP => //= /negbFE AS.
  (* case DR: get_tm_hd => //=[p]. *)
  (* case: fndP => //= pP. *)
  rewrite/mut_excl !push/=.
  move=> /andP[GM].
  elim: rs c s1 fv TD AS => [|[hd bo] rs IH]//= c s1 fv TD AS.
  rewrite !push/=.
  move=> /andP[+ ME].
  have:= IH _ _ _ TD AS ME.
  set FRS1 := fresh_rules _ _.
  set FRS2 := fresh_rules _ _.
  set FS1 := fresh_rule _ _.
  set FS2 := fresh_rule _ _.
  move=> {}IH.
  case H: H => [s2|]//=; rewrite?push/={}IH//=andbT.
  move: H; rewrite/FS2.
  rewrite/FS1 head_fresh_rule/=/fresh_rule/=!push/=.
  rewrite/mut_excl_head/=.
  set FC2:= lang.rename _ _ _.
  set FC1:= lang.rename _ _ _.
  move=> H/=.
  (* apply isSomeP in H. *)
  rewrite !has_cut_seq_fresh.
  case CS: has_cut_seq; first by case: select => [?[|[]]].
  rewrite/FC1.
  move: TD; rewrite/tm_is_det.
  case X: get_tm_hd => [p|]//=; case: fndP => //pP DP.
  rewrite (proj2 (callable_rename _ hd p empty))//; last first.
    apply/eqP.
    have [Hx Hy [p' [pP']]] := HP H.
    rewrite X => -[?]; subst.
    rewrite (bool_irrelevance pP' pP) => HX.
    rewrite -(callable_rename1 _ FRS2.1 _ empty) -Hx.
    by apply/eqP.
  rewrite in_fnd//= DP/=.
  case S: select_head => //= _.
  have ->// : (select u sP (deref s1 c) FRS2.2 s1).2 = [::].
  have /(_  (vars_sigma s1 `|` vars_tm (deref s1 c) `|` fv)) := select_head_ren (fsubset_refl _) (fsubset_refl _) S.
  rewrite -/FRS2-/FC2 => HS.
  apply: HSH (isSomeP H) HS => //=.
  - by apply: acyclic_deref_disjoint.
  - by apply: disjoint_varsU.
  - by apply/fdisjointWl/disjoint_varsU1; rewrite fsubsetU// fsubsetUr.
  - rewrite fdisjoint_sym; apply/fdisjointWr/vars_tm_rename_disjoint.
    by apply/fsubset_trans/fresh_rules_sub; rewrite fsubsetU// fsubsetUr.
  - by apply: fdisjointWl (disjoint_varsU1 _ _); rewrite -fsetUA fsubsetUl.
  - rewrite fdisjoint_sym; apply: fdisjointWr (vars_tm_rename_disjoint _ _).
    by apply: fsubset_trans (fresh_rules_sub _ _); rewrite -fsetUA fsubsetUl.
Qed.

Print  Assumptions  mut_exclP.


Definition all_rs_cut rs := all (fun p => has_cut_seq p.(premises)) rs.

Definition all_cut p :=  all_rs_cut (rules p).

Lemma all_all_but_last {T} P (L: seq T) : all P L -> all_but_last P L.
Proof. by elim: L => //= x xs IH /andP[->/IH->]; case: xs {IH}. Qed.

Lemma all_cut_select_head sP t rs fv:
  all_rs_cut rs ->
  all_rs_cut (select_head u sP t (fresh_rules fv rs).2).
Proof.
  elim: rs fv t => //=[[hd bo]]/= rs IH fv t /andP[H1 H2].
  rewrite !push/= head_fresh_rule/=; case: ifP; last by eauto.
  by rewrite/= premises_fresh_rule IH//has_cut_seq_fresh /= H1.
Qed.

Lemma all_cut_mut_excl p: good_modes p.(sig) -> all_cut p -> mut_excl u p.
Proof.
  rewrite/all_cut/mut_excl push/= => ->/=.
  case: p => /= + s.
  elim => //= [[hd bo]] rs/= IH; rewrite !push/=.
  move=> /andP[HBO] H; rewrite IH// andbT.
  rewrite/fresh_rule !push/=/mut_excl_head/=.
  case X: tm_is_det => //=.
  set R1 := lang.rename _ _ _.
  case S: select_head => //=[r' rs'].
  rewrite has_cut_seq_fresh HBO/=.
  have:= all_cut_select_head s R1.2 fset0 H.
  by rewrite S/= => /andP[->/all_all_but_last->]; destruct rs'.
Qed.



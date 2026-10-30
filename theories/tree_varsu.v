From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang ctx.
From det Require Import tree tree_prop fresh unif tree_vars.
From det Require Import min_max_disj.
Open Scope fmap_scope.
Open Scope fset_scope.

Lemma vars_sigma_next_subst_incl s A:
  vars_sigma (next_subst s A) `<=` vars_tree A `|` vars_sigma s.
Proof.
  rewrite/next_subst; elim_tree A s => /=; only 1, 2: by rewrite fsubsetUr.
  - by case: t => [|t]; rewrite fsubsetUr.
  - by rewrite (fsubset_trans (HA _))// fsetSU// -fsetUA fsubsetUl.
  - by rewrite (fsubset_trans (HB _)) //fsetUC fsubsetUl.
  - rewrite push; case: eqP => /= H.
      rewrite (fsubset_trans (HB _))//fsubUset (fsubset_trans (HA _))//.
        by rewrite (fsetUC _ (vars_tree B)) -!fsetUA fsubsetUl.
      by rewrite fsetSU// -fsetUA fsubsetUl.
    by rewrite (fsubset_trans (HA _))// fsetSU// -fsetUA fsubsetUl.
Qed.

Lemma vars_eq_subsll (A : choiceType) (s : {fset A}) l:
  s `<=` l -> s `|` l = l.
Proof.
  move=> H; apply/fsetP => x; rewrite in_fsetU orbC.
  by case xl: (x \in l) => //=; apply/contraFF/xl; have:= fsubsetP H x.
Qed.

Lemma vars_eq_sublsl (A : choiceType) (s : {fset A}) l:
  s `<=` l -> l `|` s = l.
Proof. by rewrite fsetUC; apply/vars_eq_subsll. Qed.


Fixpoint vars_disj (t1 t2: Tm) :=
  if t1 == t2 then fset0
  else
  match t1, t2 with
  | Tm_App f1 a1, Tm_App f2 a2 =>
    vars_disj f1 f2 `|` vars_disj a1 a2
  | x, y => vars x `|` vars y
  end.

Definition varsL_eq l : fvS := 
  varsU (map (fun '(x,y) => vars_disj x y) l).

Lemma vars_disjxx x: vars_disj x x = fset0.
Proof. by case x => //=>; rewrite eqxx. Qed.

Lemma vars_disjC: commutative vars_disj.
Proof.
  elim => [p|v|f Hf a Ha]/= [p'|v'|f' a']//=; rewrite?(fsetU0,fset0U,if_same)//.
    by rewrite eq_sym fsetUC.
    by rewrite fsetUC.
    by rewrite fsetUC.
  by rewrite eq_sym Hf Ha.
Qed.

Lemma vars_deref_in x v t t':
  x <> v -> x  \notin vars t ->
  x  \in vars (deref [fmap].[v <- t] t') = (x  \in vars t').
Proof.
  move=> xv xt.
  elim: t' => //[v'|f Hf a Ha].
    rewrite deref_V; case: fndP => //kv.
    rewrite ffunE/= not_fnd//=; move: kv.
    by rewrite /= fsetU0 !in_fset1 => /eqP->{v'}; rewrite eqxx (negbTE xt); case: eqP.
  by rewrite deref_App/= !in_fsetU Hf Ha.
Qed.

Lemma vars_sigma_deref_sigma v t s: v  \notin domf s ->
  vars_sigma (deref_sigma v t s) = v |` vars t `|` vars_sigma s.
Proof.
  rewrite/deref_sigma/vars_sigma/=codom_vars_set => vs.
  apply/fsetP => x; rewrite !inE; case: eqP => //=xv.
  case: (boolP (_ \in _)) => xs; rewrite ?(orbT,orbF)//=.
  rewrite orbC; case: (boolP (_ \in _)) => xt//=.
  case: (boolP (_ \in _)) => xC; apply/esym.
    apply/codom_varsP.
    move/codom_varsP: xC => [z[zP]].
    move: (zP); rewrite domf_rem/= !inE in zP.
    move: zP => /andP[zv zs] zP H.
    have H1 : [fmap x => derefkv v t s.[valP x]].[& domf s `\ v] [` zP] = deref [fmap].[v <- t] s.[zs].
      by apply: add_some; rewrite -!in_fnd fnd_restrict !inE zv zs !in_fnd ffunE valPE.
    by rewrite {zP}H1 in H; exists z, zs; rewrite vars_deref_in in H.
  apply: contraNF xC. move => /codom_varsP[k[ks xV]].
  apply/codom_varsP.
  have kv : k != v by case: eqP => //kv; subst; rewrite ks in vs.
  have H: k \in domf [fmap x : domf s => derefkv v t s.[valP x]].[& domf s `\ v].
    by rewrite domf_rem/= !inE ks kv.
  eexists _, H.
  have H1 : [fmap x => derefkv v t s.[valP x]].[& domf s `\ v] [` H] = deref [fmap].[v <- t] s.[ks].
    by apply: add_some; rewrite -!in_fnd fnd_restrict !inE ks kv !in_fnd ffunE valPE.
  by rewrite {H}H1 vars_deref_in.
Qed.

Lemma varsU_deref_list_eq v t l:
  [fset v] `|` vars t `|` varsU [seq vars_disj x y  | '(x, y) <- deref_list v t l] =
  [fset v] `|` vars t `|` varsU [seq vars_disj x y  | '(x, y) <- l].
Proof.
  elim: l => //=[x xs IH]. rewrite push (fsetUC (vars_disj _ _)) fsetUA {}IH.
  rewrite (fsetUC _ (varsU _)) -fsetUA fsetUC !fsetUA; f_equal.
Admitted.

Lemma disjoint_L_app s f1 f2 a1 a2 l:
  disjoint_L s ((Tm_App f1 a1, Tm_App f2 a2) :: l) =
  disjoint_L s [:: (f1, f2), (a1, a2) & l].
Proof. by rewrite !disjoint_L_cons/= !fdisjointXU; do 4 case: fdisjoint. Qed.

Lemma disjoint_L_comm s x y xs:
  disjoint_L s ((x,y)::xs) = disjoint_L s ((y,x)::xs).
Proof. by rewrite !disjoint_L_cons/=; do 2 case: fdisjointP. Qed.

Lemma montanari_limits s s' froz l: idempotent s -> disjoint_L s l ->
  montanari s froz l = Some s' ->
  vars_sigma s' = vars_sigma s `|` varsL_eq l.
Proof.
  rewrite/varsL_eq.
  move: s'; montanari_ind s froz l => //=s' I.
  - by move=> _ [<-]; rewrite fsetU0.
  - by rewrite disjoint_L_cons => /and3P[_ _] D; move=> /IH->//; rewrite vars_disjxx fset0U.
  - by rewrite disjoint_L_app => H{}/IH->; rewrite//EQ/= !fsetUA.
  - rewrite disjoint_L_cons/= !fdisjointX1 => /and3P[vs vs'] DL.
    move=> {}/IH->; last first.
      by apply: disjoint_deref_sigma_deref_list; rewrite//= (in_fset1,fdisjointX1)// eq_sym.
      by apply: idempotent_deref_sigma; rewrite//(in_fset1,fdisjointX1)// eq_sym.
    rewrite eqV (negbTE EQ) !fsetUA vars_sigma_deref_sigma// (fsetUC _ (vars_sigma _)) -fsetUA.
    by rewrite varsU_deref_list_eq (fsetUC [fset v']) -3!fsetUA.
  - rewrite disjoint_L_cons/= fdisjointX1 => /and3P[vs st dl].
    move=> {}/IH->; last first.
      by apply: disjoint_deref_sigma_deref_list; rewrite//= in_fset1 eq_sym.
      by apply: idempotent_deref_sigma; rewrite//in_fset1 eq_sym.
    rewrite EQ !fsetUA //vars_sigma_deref_sigma// (fsetUC _ (vars_sigma _)) -fsetUA.
    by rewrite varsU_deref_list_eq -3!fsetUA//.
  - by rewrite disjoint_L_comm; move=> H {}/IH->; rewrite //vars_disjC.
Qed.

Lemma idempotent_query_head sP fv q hd s1 r:
  idempotent s1 ->
    query_head u sP fv q hd s1 = Some r ->
      idempotent r.2.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a Ha] fv [p'|//|f' a']// s1 r.
    by case: eqP => //= _ A; case: fndP => //=pP[<-].
  move=> A.
  case H: query_head => [[[|[] tyl tyr] s1']|]//=.
    case M: matching => //= [s1''][?]; subst.
    by apply: matching_idempotent M; apply: Hf H.
  case M: unify => //= [s1''][?]; subst.
  by apply: unif_idempotent M; apply: Hf H.
Qed.

Lemma varsL_eq_cons x xs: varsL_eq (x::xs) = (vars_disj x.1 x.2) `|` varsL_eq xs.
Proof. by rewrite/varsL_eq/=push. Qed.

Lemma varsL_eq_nil: varsL_eq [::] = fset0. Proof. by []. Qed.

Lemma varsL_eq_fdisjoint q h:
  vars q # vars h -> (vars_disj q h)  = vars q `|` vars h.
Proof.
  elim: q h => [p|v|f Hf a Ha]/=h.
    by rewrite fset0U; case: eqP => //=<-.
    by case: eqP => //<-; rewrite fdisjointX1 in_fset1 eqxx.
  rewrite fdisjointUX => /andP[].
  case: h => //=f' a'.
  rewrite !fdisjointXU => /andP[ff' fa']/andP[af' aa'].
  case: eqP; last by rewrite Hf//Ha// -fsetUA (fsetUA (vars f')) (fsetUC (vars f')) !fsetUA.
  move=> [??]; subst.
  case: (set0IN (vars f')) => [->|[k kf]].
    case: (set0IN (vars a')) => [->|[k ka]]; rewrite !fset0U//.
    by have:= fdisjointP aa' _ ka; rewrite ka.
  by have:= fdisjointP ff' _ kf; rewrite kf.
Qed.

Lemma vars_deref_eq s t:
  vars_sigma s `|` vars (deref s t) = vars_sigma s `|` vars t.
Proof.
  apply/esym; rewrite !(fsetUC (vars_sigma s)).
  elim: t => [p|v|f Hf a Ha]//=.
    case: fndP => //=vs; apply/fsetP => x.
    rewrite !in_fsetU in_fset1; rewrite !(orbC _ (_ || _)).
    case: (boolP (_ \in _)) => xs//=.
    case: (boolP (_ \in _)) => xcs//=.
    case: eqP => xv; subst; first by rewrite vs in xs.
    apply/esym; apply: contraNF xcs => H.
    by apply/codom_varsP; exists _, vs.
  rewrite -(fsetUid (vars_sigma s)) -fsetUA (fsetUA _ (vars_sigma s)).
  rewrite Ha fsetUA fsetUC fsetUA (fsetUC (vars_sigma s)) Hf -fsetUA.
  by rewrite (fsetUC (vars_sigma s)) !fsetUA.
Qed.

Lemma vars_disj_deref_sub2 s t1 t2: vars t1 `<=` vars_sigma s -> vars t2 `<=` vars_sigma s ->
  vars_sigma s `|` vars_disj t1 t2 = vars_sigma s.
Proof.
  elim: t1 t2 => [p|v|f Hf a Ha] t/=.
  - by move=> _ H; rewrite /= fun_if fsetUA fsetU0 vars_eq_sublsl//if_same.
  - by move=> H1 H2; rewrite fun_if fsetU0 (fsetUC [fset v]) fsetUA (vars_eq_sublsl H2) vars_eq_sublsl// if_same.
  - rewrite fsubUset => /andP[H1 H2] H3.
    rewrite fun_if fsetU0; destruct t; rewrite !fsetUA/=.
      by rewrite (vars_eq_sublsl H1) (vars_eq_sublsl H2) fsetU0.
      by rewrite (vars_eq_sublsl H1) (vars_eq_sublsl H2) (vars_eq_sublsl H3).
    by move: H3; rewrite /= fsubUset => /andP[H3 H4]; rewrite Hf//Ha//if_same.
Qed.

Lemma vars_disj_deref_sub s t1 t2: vars t1 `<=` vars_sigma s ->
  vars_sigma s `|` vars_disj t1 (deref s t2) = vars_sigma s `|` vars t2.
Proof.
  elim: t1 t2 => [p|v|f Hf a Ha]/=t2.
  - case: eqP; rewrite (fsetU0,fset0U).
      by rewrite -vars_deref_eq => <-/=; rewrite fsetU0.
    by rewrite vars_deref_eq.
  - rewrite fsub1set => vs; case: eqP => H.
      by rewrite-vars_deref_eq-H/= fsetU0 fsetUC vars_eq_subsll//fsub1set.
    rewrite fsetUC -fsetUA (fsetUC (vars _)) vars_deref_eq fsetUA (@vars_eq_subsll _ [fset v])//.
    by rewrite fsub1set.
  - rewrite fsubUset => /andP[sf sa].
    rewrite fun_if fsetU0.
    case: t2 => [p|v|f' a']//=.
    - by rewrite fsetUC !fsetU0 -fsetUA (vars_eq_subsll sa) vars_eq_subsll.
    - case: fndP => //=vs.
        rewrite (fsetUC _ [fset v]) (@vars_eq_subsll _ [fset v]); last by rewrite fsub1set in_fsetU vs.
        case: eqP => E; first by [].
        rewrite fsetUC vars_eq_subsll//; case H: s.[vs] => [p|vx|f' a']/=.
        - by rewrite fsetU0 fsubUset sf sa.
        - by rewrite !fsubUset sf sa/= fsub1set in_fsetU; apply/orP; right; apply/codom_varsP; exists _,vs; rewrite H in_fset1.
        rewrite fsubUset -{1}(@vars_disj_deref_sub2 s f f')//.
          rewrite fsubsetUr -{1}(@vars_disj_deref_sub2 s a a')//; first by rewrite fsubsetUr.
          apply/fsubsetP => x; rewrite in_fsetU => xa'; apply/orP; right.
          by apply/codom_varsP; exists _, vs; rewrite H/= in_fsetU xa' orbT.
        apply/fsubsetP => x; rewrite in_fsetU => xf'; apply/orP; right.
        by apply/codom_varsP; exists _, vs; rewrite H/= in_fsetU xf'.
    - by rewrite !fsetUA (vars_eq_sublsl sf) (vars_eq_sublsl sa).
    - case: eqP.
        move=> [??]; subst.
        rewrite fsetUA -vars_deref_eq (fsetUC (vars_sigma _)) -fsetUA -vars_deref_eq.
        by rewrite (vars_eq_sublsl sa) vars_eq_subsll.
      by move=> H; rewrite fsetUA Hf// (fsetUC (vars_sigma _)) -fsetUA Ha// fsetUA (fsetUC (vars f')) fsetUA.
Qed.

Lemma deref_disj_sub sf t1 t2:
  vars t1 # vars t2 ->
  deref sf t1 = deref sf t2 ->
  vars t2 `<=` vars_sigma sf.
Proof.
  elim: t1 t2 => [p|v|f Hf a Ha] t/=.
  - by case: t => //=v _; case: fndP => //=vs H; rewrite fsub1set in_fsetU vs.
  - rewrite fdisjoint1X => vt; case: fndP => //=vs.
      move=> H; apply/fsubsetP => x xt; rewrite in_fsetU; case: (boolP (_ \in _)) => //.
      move=> xsf; apply/codom_varsP ; exists _, vs; rewrite H.
      move: xsf xt; clear => xsf; elim: t => //=[v|f Hf a Ha].
        by rewrite in_fset1 => /eqP<-; rewrite not_fnd//= in_fset1.
      by rewrite !in_fsetU => /orP[/Hf|/Ha]->//; rewrite orbT.
    case: t vt => //=v'; rewrite in_fset1 => vv; case: fndP => vs'; last by move=> []/eqP; rewrite (negbTE vv).
    by move=> /=H; rewrite fsub1set in_fsetU vs'.
  - rewrite fdisjointUX; case: t => //=[v|f' a']; rewrite !(fdisjointXU,fdisjointX1).
      by move=> /andP[vf va]; case: fndP => //=vs H; rewrite fsub1set in_fsetU vs.
    by rewrite-andbA => /and4P[ff fa af aa][H1 H2]; rewrite fsubUset Hf//Ha.
Qed.

Lemma vars_disj_deref sf t1 t2: vars t1 # vars t2 ->
  vars_sigma sf `|` vars_disj (deref sf t1) (deref sf t2) = vars_sigma sf `|` vars t1 `|` vars t2.
Proof.
  elim: t1 t2 => [p|v|f Hf a Ha]/=t.
  - rewrite fset0U fun_if !fsetU0 vars_deref_eq; case: eqP => //.
    by rewrite -vars_deref_eq => <-; rewrite fsetU0.
  - rewrite fdisjoint1X => vt; case: fndP => //=vs.
      rewrite (fsetUC _ [fset v]) (@vars_eq_subsll _ [fset v]); last by rewrite fsub1set in_fsetU vs.
      by rewrite vars_disj_deref_sub//fsubsetU//codom_vars_sub_vt orbT.
    case: eqP.
      case: t vt => //=v'; rewrite in_fset1 => vv; case: fndP => //=vs'; last by move=> []/eqP; rewrite (negbTE vv).
      move=> H.
      rewrite fsetU0 fsetUC fsetUA (@vars_eq_subsll _ [fset v']); last by rewrite fsub1set in_fsetU vs'.
      rewrite fsetUC vars_eq_subsll// fsub1set in_fsetU; apply/orP; right.
      by apply/codom_varsP; exists _, vs'; rewrite -H/= in_fset1.
    by move=> _; rewrite (fsetUC [fset v]) fsetUA vars_deref_eq -fsetUA (fsetUC (vars t)) fsetUA.
  - rewrite fdisjointUX => /andP[tf ta].
    rewrite fun_if fsetU0.
    case: eqP.
      rewrite fsetUA -vars_deref_eq (fsetUC (vars_sigma _)) -2!fsetUA (fsetUA (vars_sigma _)).
      rewrite -vars_deref_eq fsetUA (fsetUC (vars_sigma _)) fsetUA -fsetUA -vars_deref_eq.
      move=> H. 
      replace (vars (deref sf f) `|` vars (deref sf a)) with (vars (deref sf (Tm_App f a))) by auto.
      rewrite [deref _ _]/= H fsetUC -fsetUA fsetUid.
      rewrite vars_deref_eq.
      case: t tf ta H => //[v|f' a']; rewrite /=!(fdisjointX1,fdisjointXU).
        move=> vf va; case: fndP => //=vsf H.
        by rewrite vars_eq_sublsl// fsubsetU// fsub1set vsf.
      move=> /andP[ff fa]/andP[af aa][H1 H2].
      rewrite fsetUA !(@vars_eq_sublsl _ _ (vars_sigma _))//.
        by apply: deref_disj_sub H2.
      by apply: deref_disj_sub H1.
    case: t tf ta => [p|v|f' a']/=.
    - by rewrite !fsetU0 fsetUA vars_deref_eq (fsetUC (vars_sigma _)) -fsetUA vars_deref_eq fsetUA (fsetUC (vars f)) fsetUA.
    - case: fndP => /=vs.
      - case H: sf.[vs] => [p|v'|f' a']//=.
        - rewrite fsetU0 (fsetUC _ [fset v]) (fsetUA [fset v]) (@vars_eq_subsll _ [fset v]); last by rewrite fsub1set in_fsetU vs.
          by rewrite fsetUA vars_deref_eq (fsetUC (vars_sigma _)) -fsetUA vars_deref_eq fsetUA (fsetUC (vars f)) fsetUA.
        - rewrite fsetUA !(fsetUC _ [fset v']) !(fsetUC _ [fset v]) (fsetUA [fset v']) (fsetUA [fset v]).
          rewrite (@vars_eq_subsll _ [fset v]); last by rewrite fsub1set in_fsetU vs.
          rewrite (@vars_eq_subsll _ [fset v']); last first.
            by rewrite fsub1set in_fsetU; apply/orP; right; apply/codom_varsP; exists _, vs; rewrite H in_fset1.
          by rewrite fsetUA vars_deref_eq (fsetUC (vars_sigma _)) -fsetUA vars_deref_eq fsetUA (fsetUC (vars f)) fsetUA.
        - have ? : vars f' `<=` vars_sigma sf.
            by apply/fsubsetP => x xP; rewrite in_fsetU; apply/orP; right; apply/codom_varsP; exists _, vs; rewrite H/= in_fsetU xP.
          have ? : vars a' `<=` vars_sigma sf.
            by apply/fsubsetP => x xP; rewrite in_fsetU; apply/orP; right; apply/codom_varsP; exists _, vs; rewrite H/= in_fsetU xP orbT.
          rewrite !(vars_disjC (deref _ _)) fsetUA vars_disj_deref_sub//(fsetUC (vars_sigma _)) -fsetUA vars_disj_deref_sub//fsetUA (fsetUC (vars f)) fsetUA.
          by rewrite (fsetUC _ [fset v]) (fsetUA [fset v]) (@vars_eq_subsll _ [fset v])//; rewrite fsub1set !in_fsetU vs.
      - move=> _ _ H; rewrite fsetUA; f_equal.
        by rewrite fsetUA vars_deref_eq (fsetUC (vars_sigma _)) -fsetUA vars_deref_eq fsetUA (fsetUC (vars f)) fsetUA.
    - rewrite !fdisjointXU => /andP[ff fa]/andP[af aa] _.
      rewrite fsetUA Hf//(fsetUC (vars_sigma _))-2!fsetUA (fsetUC (vars_sigma _)) -fsetUA.
      rewrite  (fsetUC _ (vars_sigma _)) Ha//; apply/fsetP => x.
      rewrite !in_fsetU; do 5 case: (_ \in _) => //=.
Qed.
    

Lemma query_head_limits prog froz q h s r: idempotent s -> vars q # vars h ->
  query_head u prog froz q h s = Some r ->
  (vars_sigma r.2) = (vars_sigma s `|` vars q `|` vars h).
Proof.
  elim: q h s r => [p|v|f Hf a _]//=[p'|v'|f' a']// s r I.
    by case: eqP => //= _ _; case: fndP => //=pP[<-]/=; rewrite !fsetU0.
  rewrite /=fdisjointXU !fdisjointUX -!andbA => /and4P[ff af fa aa].
  case qf: query_head => //[[[|m tl tr] sf]]//=.
  have /={}Hf := Hf _ _ _ I ff qf.
  case H : (_ a') => //[sa][<-{r}]/=.
  have /= I' := idempotent_query_head I qf.
  have: vars_sigma sa = vars_sigma sf `|` (vars_disj (deref sf a') (deref sf a)).
    by move: H; case: ifP => _ H; rewrite (montanari_limits _ (disjoint_L_deref _ _ _) H)//varsL_eq_cons/= varsL_eq_nil fsetU0.
  move=> ->; rewrite vars_disj_deref; last by rewrite fdisjoint_sym.
  by rewrite Hf; apply/fsetP => x; rewrite !in_fsetU; do 6 case: (_ \in _) => //=.
Qed.

Lemma select_limits fv p q rs s:
  idempotent s ->
  max_set (vars q) < fv -> max_set (vars_sigma s) < fv ->
  [forall x : (varsU [seq varsU_rule i  | i <- rs]), fv < getV (val x)] ->
  let t := match select u p q rs s with
  | [::] => KO
  | (s0, r) :: xs => Or None s0 (big_or r xs)
  end in
  vars_tree t `<=` vars q `|` vars_sigma s \/
  (exists2 k : fvS,
    min_maxS k fv (fresh (vars_tree t)) &
    k `|` vars q `|` vars_sigma s = vars_tree t `|` vars_sigma s).
Proof.
  move=> I qv sv.
  elim: rs => /=[|x xs IH] H; first by left.
  have {}Hx : [forall x : varsU [seq varsU_rule i  | i <- xs],  fv < getV (val x)].
    apply/forallP => -[[r] rP]/=.
    have rxs : IV r \in (varsU_rule x `|` varsU [seq varsU_rule i  | i <- xs]).
      by rewrite in_fsetU rP orbT.
    by have:= forallP H [`rxs].
  have {Hx}IH := IH Hx.
  case Q: query_head => [[ty s']|]/=; last first.
    case S: select IH => [|[s0 r0] rs]/= IH; first by left.
    case: IH => //; first by move=> ->; left.
    by move=> [k H1 H2]; right; exists k; rewrite//.
  have dqx : vars q # vars (head x).
    apply/fdisjointP_sym => -[k] kx.
    have kP: IV k \in (varsU_rule x `|` varsU [seq varsU_rule i  | i <- xs]) by rewrite !in_fsetU kx.
    have/= := leq_ltn_trans qv (forallP H [`kP]); clear => H; apply/negP.
    move=> /max_setP /= Z; have:=(ltnW (leq_trans H Z)).
    by rewrite ltnn.
  have /= {}Q := query_head_limits I dqx Q.
  rewrite {s'}Q.
  case (set0IN (vars (head x) `|` vars_atoms (premises x))).
    move=> p0.
    have h0: vars (head x) = fset0.
      move/fsetP: p0 => p0.
      apply/fsetP => m; have:= p0 m; rewrite in_fsetU/=; case: (_ \in _) => //.
    rewrite h0 fset0U in p0.
    rewrite h0 fsetU0.
    case: select IH => [|[s' r0] rs]/=; first by left; rewrite vars_tree_big_and p0 !fset0U fsetUC.
    rewrite vars_tree_big_and p0 fset0U.
    move=> [IH|[k H1 H3]].
      by rewrite fsubUset IH fsetUC/=; left.
    right; exists k.
      by rewrite freshUU min_max_maxr H1.
    by rewrite -fsetUA -(fsetUid (vars q `|` _)) !(fsetUA k) H3 2!fsetUA.
  set hp:= (vars (head _) `|`_).
  (* move=> [[k] kP]; right. *)
  (* rewrite vars_tree_big_or 2!fsetUA. *)
  (* rewrite !(fsetUC _ (vars (head x))) 3!fsetUA -/hp. *)
  have fhp: all_min fv hp.
    apply/forallP => [[[k]]kP]/=.
    have kP': IV k \in (hp `|` varsU [seq varsU_rule i  | i <- xs]) by rewrite in_fsetU kP.
    by have /={kP'}H := forallP H [`kP']; apply/ltnW.
  move=> [[k]kP].
  right.
  case: select IH.
    rewrite/= vars_tree_big_and fsetUA !(fsetUC _ (vars (head _))) fsetUA -/hp.
    exists hp.
      by rewrite freshUU min_max_maxr min_maxS_all fhp/= all_max_max_set.
    by apply/fsetP => z; rewrite !in_fsetU; do 6 case (_\in_) => //.
  move=> [s0 prem] rs/=; rewrite vars_tree_big_or.
  move=> [IH|[z H1 H3]].
    rewrite/= vars_tree_big_and 3!fsetUA !(fsetUC _ (vars (head _))) 5!fsetUA -/hp.
    exists hp; rewrite -/hp.
      by rewrite - 4!fsetUA freshUU min_max_maxr min_maxS_all fhp/= all_max_max_set.
    rewrite -6!fsetUA; f_equal; rewrite -(vars_eq_subsll IH).
    rewrite !fsetUA.
    by apply/fsetP => z; rewrite !in_fsetU; do 6 case ?: (_\in _); rewrite//?(orbT,orbF,orbb)//=.
  set X := varsU _ in H1 H3 *.
  rewrite/= vars_tree_big_and 3!fsetUA !(fsetUC _ (vars (head _))) 5!fsetUA -/hp.
  exists (z `|` hp).
    rewrite min_maxU// -!(fsetUA hp) (freshUU hp) (min_max_maxr hp) (min_maxS_all hp).
    rewrite fhp all_max_max_set !andbT/=.
    by rewrite -fsetUA freshUU !min_max_maxr H1 orbT.
  rewrite -{1}(fsetUid (vars q)) fsetUA -(fsetUA _ (vars q)) (fsetUC (vars q)) fsetUA.
  rewrite (fsetUC z) -!(fsetUA hp) H3 (fsetUC _ (vars_sigma s0)) -!(fsetUA (vars_sigma s0)).
  rewrite -(fsetUA _ (vars q)) (fsetUC (vars q)) -!(fsetUA _ (vars_sigma s)).
  by rewrite (fsetUA (vars_sigma s)) fsetUid.
Qed.

Lemma max_set_max_sigmas n l:
  max_set
  (vars_tree
    match l with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end) <= max_sigmas n l.
Proof.
  elim: l => [|[s0 x] xs IH]/=; first by rewrite max_setP0.
  rewrite max_setUU geq_max !(leq_max (max_set (vars_sigma _))) leqnSn !orbT andbT.
  rewrite !leq_max orbA; apply/orP; left.
  replace (vars_tree (big_or x xs)) with
    (vars_atoms x `|` vars_tree match xs with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end).
    rewrite max_setUU !geq_max IH leqnSn/=andbT; case: leqP => //= H.
    have {}IH := leq_ltn_trans IH H.
    by apply/ltnW/ltnW => //.
  by case: xs {IH} => //=[|[s' r']rs]/=; rewrite vars_tree_big_and (fsetUA,fsetU0)//.
Qed.

Lemma vars_tree_step_limits p A fv s:
  max_set (vars_tree A) < fv -> max_set (vars_sigma s) < fv ->
  let stA := step u p fv s A in
    (vars_tree stA.2 `<=` vars_tree A `|` vars_sigma s \/ 
      (exists2 k, min_maxS k fv stA.1.1.+1 & k `|` vars_tree A `|` vars_sigma s = vars_tree stA.2 `|` vars_sigma s)).
Proof.
  move=> H1 H2; case S: step => [[fv' r] R]/=.
  move: H1 H2 S.
  elim_tree A R fv fv' r s => /=; only 1,2: by move=> _ _[<-_<-]/=; left.
  - case: t; first by move=> _ _[<-_<-]/=; left.
    move=> t ft fs/=.
    rewrite/bc; case: ifP => [iP[<-_<-]|/negbFE iP]/=; first by left.
    set X := fresh _.
    case F: fresh_rules => [n rs][<-_<-{fv' r R}].
    have /= := min_max_fresh_rules X (rules p); rewrite F/= => Hx.
    have fvX: fv < X.
      by rewrite/X -!fsetUA freshUU leq_max freshP1 ltnSn.
    have H: [forall x : (varsU [seq varsU_rule i  | i <- rs]), fv < getV (val x)].
      apply/forallP => [[[x] xP]]/=.
      apply: ltn_leq_trans fvX _.
      by have /andP[] := forallP Hx [`xP].
    have fst: fresh (vars (deref s t)) <= fv.
      apply: leq_trans (fresh_subP (vars_tm_deref_sub _ _)) _.
      by rewrite freshPU ft andbT (leq_trans _ fs)//fresh_subP//fsubsetUr.
    have {H}/=:= select_limits p iP fst fs H.
    rewrite (fsetUC (vars _)) vars_deref_eq (fsetUC (vars t)).
    move=> [->|]; first by left.
    move=> [k].
    rewrite -fsetUA (fsetUC (vars _)) vars_deref_eq (fsetUC _ (vars t)) fsetUA.
    move=> H1 H3; right; exists k; last by [].
    have H:= max_set_max_sigmas n (select u p (deref s t) rs s).
    by rewrite -ltnS in H; rewrite (min_max_leqr H).
  - rewrite 2!freshPU -andbA/= => /and3P[fa fb fsm fs].
    case sA: step => [[fvA tA] A'][???]; subst.
    have /={HB}[{}HA|[{HA}k H1 H2]] := HA _ _ _ _ _ fa fs sA; [left|].
      rewrite 2!fsubUset (fsubset_trans HA)/=; last first.
        by rewrite fsubUset -2!{1}fsetUA fsubsetUl fsubsetUr.
      rewrite {2}(fsetUC _ (vars_sigma sm)) -(fsetUA (vars_sigma sm)) fsubsetUl andbT.
      by case: ifP; rewrite//(fsetUC _ (vars_tree B)) -!fsetUA fsubsetUl.
    case: ifP => ctA/=.
      destruct tA => //=.
      have:= vars_tree_step_cut sA => skA.
      left; rewrite fsetU0 fsubUset -2!fsetUA (fsubset_trans skA (fsubsetUl _ _)).
      by rewrite (fsetUC (vars_sigma sm)) 2!fsetUA fsubsetUr.
    right.
    exists k; rewrite//-{1}(fsetUid (vars_sigma s)) fsetUA (fsetUC _ (vars_sigma s)).
    rewrite 2!fsetUA (fsetUC (vars_sigma s)) -2!fsetUA 3!(fsetUA (vars_sigma s)).
    rewrite (fsetUC (vars_sigma s)) 4!fsetUA H2 (fsetUC (vars_tree A')).
    by rewrite -3!fsetUA fsetUC -3!fsetUA fsetUid -!fsetUA.
  - rewrite {1}[vars_tree _]/= freshPU => /andP[bv smv sv].
    case sB: step => [[fvB tB] B'][???]; subst => /=.
    have {HB}[HB|[k H1 H2]] := HB _ _ _ _ _ bv smv sB.
      by rewrite fsubUset (fsubset_trans HB (fsubsetUl _ _)) fsetUC fsetUA fsubsetUr; left.
    by right; exists k; rewrite// fsetUA H2.
  - rewrite 2!freshPU -andbA => /and3P[av bv b0v sv].
    case: ifP => successA.
      case sB: step => {HA}[[fvB tB] B'][???]; subst => /=.
      case: ifP => ctr/=.
        destruct r => //=.
        have:= vars_tree_step_cut sB => skB.
        left; rewrite 2!fsubUset -2!fsetUA (fsubset_trans (vars_tree_cutl _) (fsubsetUl _ _)).
        rewrite (fsubsetU)/=; last rewrite orbC.
          by rewrite fsubsetU// orbC fsubsetU// fsubsetUl orbT.
        by rewrite (fsubset_trans skB (fsubsetUl _ _)).
      have {HB}[HB|[k H1 H2]] := HB _ _ _ _ _ bv (vars_sigma_next_subst av sv) sB.
        left; rewrite -3!fsetUA !fsubUset fsubsetUl/= (fsetUC (vars_atoms B0)) 2!fsetUA fsubsetUr.
        rewrite (fsubset_trans HB)//= (fsetUC _ (vars_tree B)) -2!fsetUA fsetUS//.
        by rewrite (fsubset_trans (vars_sigma_next_subst_incl _ _))//fsetUA fsubsetUl.
      right; exists k => //.
      rewrite fsetUA -!(fsetUC (vars_atoms B0)) -!(fsetUA (vars_atoms _)); f_equal.
      replace (k `|` (vars_tree A `|` vars_tree B) `|` vars_sigma s) with
        (k `|` vars_tree B `|` vars_sigma (next_subst s A) `|` vars_tree A `|` vars_sigma s).
        rewrite H2 (fsetUC _ (vars_tree B')) -!(fsetUA (vars_tree B')); f_equal.
        by rewrite -fsetUA vars_eq_subsll//vars_sigma_next_subst_incl.
      rewrite -!(fsetUA k); f_equal.
      rewrite (fsetUC _ (vars_tree B)) -!(fsetUA (vars_tree B)); f_equal.
      by rewrite -fsetUA vars_eq_subsll//vars_sigma_next_subst_incl.
    case sA: step => [[fvA tA] A'] [???]; subst => /=.
    have {HA}[HA|[k H1 H2]] := HA _ _ _ _ _ av sv sA.
      left; rewrite (fsetUC _ (vars_sigma _)) 2!fsetUA.
      by rewrite (fsetUC (vars_sigma _)) fsetSU//fsetSU//.
    right; exists k; rewrite//fsetUA !(fsetUC _ (vars_atoms B0)) -!(fsetUA (vars_atoms B0)).
    f_equal; rewrite fsetUA (fsetUC _ (vars_sigma _)) fsetUA (fsetUC (vars_sigma _)).
    by rewrite H2 -fsetUA (fsetUC (vars_sigma s)) fsetUA.
Qed.


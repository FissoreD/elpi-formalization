From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.

Definition has_cut_seq:= (has (fun x => cut == x)).

Section checker.
  Fixpoint all_but_last {T : Type} P (l : seq T) :=
    match l with 
    | [::] | (_ :: [::]) => true
    | x :: xs => P x && all_but_last P xs
    end.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint getS_Callable (sP: sigT) (t: Callable) : option S :=
    match t with
    | Callable_P pn => sP.[? pn]
    | Callable_App hd _ => getS_Callable sP hd
    end.

  Definition tm_is_det (sP: sigT) (t : Callable) :=
    if getS_Callable sP t is Some s then is_det_sig s
    else false.

  Definition check_atom sP (a: A) :=
    match a with
    | cut => true
    | call t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)
  Fixpoint check_atoms (sP :sigT) (s: seq A) :=
    match s with
    | [::] => true
    | cut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | call c :: xs => (tm_is_det sP c || has_cut_seq xs) && check_atoms sP xs
    end.

  Definition check_rule sP head prems :=
    (tm_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules sP rules :=
    all (fun x => check_rule sP x.(head) x.(premises)) rules.
End checker.

Lemma tiki_taka sP s s3 modes t q pn hd1 u:
  let t' := tm2RC (deref s (Callable2Tm t)) in
  t' = Some (q, pn) ->
  tm_is_det sP t ->
    H u modes q hd1 s = Some s3 ->
      tm_is_det sP hd1.
Proof.
  move=>/=.
  elim: modes q pn hd1 t s s3 => //=.
    move=> []//=k kp hd1 t s1 s2.
    case: hd1 => //={}k0.
    case: eqP => //=?; subst k0.
    move=> ++ [?]; subst.
    destruct t => //=; last by case: tm2RC => //=[[]].
    by move=> [->->]/=; rewrite/tm_is_det/=; case: fndP.
  move=> m //ml IH q pn hd t s1 s2 H1 H2 H3.
  have {H3}: exists f1 a1 f2 a2,
    q = Callable_App f1 a1 /\
    hd = Callable_App f2 a2 /\
    (obind (matching u a1 a2) (H u ml f1 f2 s1) = Some s2 \/
    obind (unify u a1 a2) (H u ml f1 f2 s1) = Some s2).
  by move: H3; destruct m, q, hd => //; repeat eexists; auto.
  move=> [f1 [a1 [f2 [a2 [?[?]]]]]]; subst.
  case e: H => //=[s3|]; last by case.
  move: H2; rewrite/tm_is_det/=.
  case: t H1 => //= c t.
  case H : tm2RC => //=[[h1' hp]] [??]?; subst => /=.
  case X: getS_Callable => //[S] H1/= H2.
  by apply: IH H _ e; rewrite/tm_is_det X//.
Qed.

Section mut_excl.
  Variable u : Unif.

  Fixpoint H_head s (ml : list mode) (q : Callable) (h: Callable) : option Sigma :=
    match ml,q,h with
    | [::], Callable_P c, Callable_P c1 => if c == c1 then Some s else None
    | [:: i & ml], (Callable_App q a1), (Callable_App h a2) => obind (u.(unify) a1 a2) (H_head s ml q h)
    | [:: o & ml], (Callable_App q a1), (Callable_App h a2) => (H_head s ml q h)
    | _, _, _ => None
    end.
  
  Definition unif_head := H_head empty.

  Fixpoint select_head (query : Callable) (modes:list mode) (rules: list R) : (seq R) :=
    match rules with
    | [::] => [::]
    | rule :: rules =>
      let tl := select_head query modes rules in
      if H_head empty modes query rule.(head) then rule :: tl else tl
    end.
  
  Definition mut_excl_head (sig:sigT) (query:Callable) rules :=
    match tm2RC (Callable2Tm query) with
      | None => true (*a callable against a non rigid term is OK: failure at runtime*)
      | Some (query, kp) =>
        match sig.[? kp] with 
          | Some sig => 
            if is_det_sig sig then 
              let r := select_head query (get_modes_rev query sig) rules in
              all_but_last (fun x => has_cut_seq x.(premises)) r
            (* ignoring checking for vars *)
            else true
          (*a callable against a rigid term non in sig OK: failure at runtime*)
          | None => true
          end
      end.

  Lemma head_fresh_rule fv r:
    head (fresh_rule fv r).2 = (fresh_callable fv r.(head)).2.
  Proof.
    destruct r; rewrite/fresh_rule/= 1!push.
    case bc: fresh_atoms => [fv' A']//=.
  Qed.

  Lemma head_fresh_premises fv r:
    premises (fresh_rule fv r).2 = (fresh_atoms (fresh_callable fv r.(head)).1 r.(premises)).2.
  Proof.
    destruct r; rewrite/fresh_rule/= 1!push.
    generalize (fresh_callable fv head) => -[{}fv/=b].
    case FA: fresh_atoms => [b1 a']//=.
  Qed.

  Lemma callable_is_det_fresh sP fv hd:
    tm_is_det sP (fresh_callable fv hd).2 =
      tm_is_det sP hd.
  Proof.
    rewrite/tm_is_det.
    elim: hd fv => //= a Ha t fv.
    by rewrite !push/= -(Ha fv).
  Qed.

  Lemma tm_is_det_comb sP f a:
    tm_is_det sP (Callable_App f a) = tm_is_det sP f.
  Proof. by rewrite/tm_is_det/=. Qed.
  
  Lemma tm_is_det_fresh sP c c' sv sv':
    tm_is_det sP c ->
    fresh_callable sv c = (sv', c') ->
    tm_is_det sP c'.
  Proof.
    elim: c c' sv sv' => //=.
      by move=> k c' sv sv' + [_ <-]//.
    move=> f Hf a c' sv sv'.
    case X: fresh_callable => [sv2 f'].
    case Y: rename => [sv3 a'] + [_ <-].
    rewrite !tm_is_det_comb => H.
    by apply/Hf/X.
  Qed.

  Lemma fresh_has_cut sv xs sv' xs':
    has_cut_seq xs -> fresh_atoms sv xs = (sv', xs') -> has_cut_seq xs'.
  Proof.
    elim: xs sv xs' sv' => //= x xs IH sv xs' sv'.
    case Fs: fresh_atoms => [b' a'].
    case Fa: fresh_atom => [b2 a2]/=+[_<-]/=.
    move=> /orP [/eqP?|]; subst; first by move: Fa => /=[_<-].
    by move=> H; rewrite (IH _ _ _ H Fs) orbT.
  Qed.

  Lemma check_atom_fresh sP x x' sv sv':
    check_atom sP x ->
    fresh_atom sv x = (sv', x') ->
    check_atom sP x'.
  Proof.
    destruct x => //=; first by move=> _ [_ <-].
    case X: fresh_callable => [svE c'] H [_ <-]/=.
    by apply/tm_is_det_fresh/X.
  Qed.

  Lemma all_check_atom_fresh sP xs xs' sv sv':
    all (check_atom sP) xs ->
    fresh_atoms sv xs = (sv', xs') ->
    all (check_atom sP) xs'.
  Proof.
    elim: xs xs' sv sv' => //=; first by move=> > _ [_ <-].
    move=> x xs IH xsE sv svE /andP[H1 H2].
    case Fs: fresh_atoms => [sv' xs'].
    case Fa: fresh_atom => [sv2 xs2] [_ <-]/=.
    rewrite (IH _ _ _ _ Fs)//andbT.
    by apply/check_atom_fresh/Fa.
  Qed.

  Lemma check_atoms_fresh sP sv bo sv' bo':
    check_atoms sP bo ->
      fresh_atoms sv bo = (sv', bo') ->
      check_atoms sP bo'.
  Proof.
    elim: bo bo' sv sv' => //=.
      move=> > _ [_ <-]//.
    move=> //= x xs IH bo' sv sv'.
    case Fs: fresh_atoms => [b' xs'].
    case Fa: fresh_atom => [b2 a2] + [_ <-]/=.
    destruct x; move: Fa => /=.
      move=> [_<-].
      move=> /orP[] H; apply/orP.
        by rewrite (all_check_atom_fresh H Fs); left.
      by right; apply/IH/Fs.
    case X: fresh_callable => [b3 c'][_<-] /andP[+/IH-/(_ _ _ _ Fs)->].
    rewrite andbT.
    by move=> /orP[/tm_is_det_fresh -/(_ _ _ _ X)|/fresh_has_cut-/(_ _ _ _ Fs)]->//; rewrite orbT.
  Qed.

  Fixpoint mut_excl sig rules :=
    match rules with
    | [::] => true
    | x :: xs => mut_excl_head sig x.(head) rules && mut_excl sig xs
    end.

End mut_excl.


Definition check_program_aux u sig pr := 
   mut_excl u sig pr && check_rules sig pr.

Definition check_program u pr := 
   check_program_aux u pr.(sig) pr.(rules).

Section check.
  Variable u : Unif.
  (* Variable p : program. *)


  Fixpoint has_cut A :=
    match A with
    | TA cut => true
    | TA (call _) => false
    | KO => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut_seq B0 && has_cut B)
    | Or _ _ _ => false
    end.


  Fixpoint det_tree_seq sP L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP x || has_cut_seq xs) && det_tree_seq sP xs
    end.


  Definition no_alt A := next_alt (success A) A == None.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is OK due to the cut in LHS of Or
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)
  
  *)
  Fixpoint det_tree (sP:sigT) A :=
    match A with
    | TA cut => true
    | TA (call a) => tm_is_det sP a
    | KO | OK => true
    | And A B0 B =>
        det_tree sP B && 
        if no_alt A
        then det_tree sP A || has_cut B
        else
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          (det_tree sP A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq sP B0 (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree sP B
    | Or (Some A) _ B =>
        det_tree sP A && 
        if has_cut A then det_tree sP B 
        else (B == KO) 
    end.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim_tree A => /=.
      (* by move=> /andP[/is_ko_cutl->].
      by move=> /is_ko_cutl. *)
    rewrite fun_if/=.
    case:ifP => // sA.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[->/HB->]; rewrite orbT//.
  Qed.

  Lemma has_cut_seq_has_cut_big_and l:
    has_cut (big_and l) = has_cut_seq l.
  Proof. by elim: l => //[[|c]] xs IH//=; rewrite IH Bool.andb_diag. Qed.

  (* Lemma cut_followed_by_det_has_cut {sP l}:
      check_atoms sP l -> has_cut_seq l.
  Proof. rewrite/check_atoms. elim: l => //= -[|c] l _ //=. Qed. *)

  Lemma det_tree_big_and sP L:
    det_tree sP (big_and L) = det_tree_seq sP L.
  Proof.
    elim: L => //=-[|c] L ->.
      by rewrite orTb andTb andbb.
    rewrite has_cut_seq_has_cut_big_and /= [RHS]andbC.
    by case: det_tree_seq => //=; case: has_cut_seq => //=; rewrite orbC //= andbC.
  Qed.

  Lemma cut_followed_by_det_nfa_and {sP bo} :
    check_atoms sP bo -> det_tree_seq sP bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      by elim: l {IH} => //= x xs IH /andP[->]/IH->.
    by move=> /andP[->]/=.
  Qed.

  Lemma no_alt_cutl A: success A -> no_alt (cutl A).
  Proof. by rewrite /no_alt success_cut => ->; rewrite next_alt_cutl. Qed.

  Lemma det_tree_cutl {sP A}: success A -> det_tree sP (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= => /andP[sA sB]/=.
    by rewrite sA HA// HB//no_alt_cutl//.
  Qed.

  Lemma check_rules_cons sP x xs : check_rules sP (x :: xs) = check_rule sP (head x) (premises x) && check_rules sP xs.
  by []. Qed.

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
Qed.

  Lemma det_tree_fresh sP sv bo:
    det_tree_seq sP bo -> det_tree_seq sP (fresh_atoms sv bo).2.
  Proof.
    elim: bo sv => //= [x xs] IH sv /andP[H1 /IH -/(_ sv)].
    case Fs: fresh_atoms => [b' a'].
    case Fa: fresh_atom => [b2 a2]/=->; rewrite andbT {IH}.
    move/orP: H1 => [|] H.
      by rewrite (check_atom_fresh H Fa).
    by rewrite (fresh_has_cut H Fs) orbT.
  Qed.

  Lemma select_same2 vx vy q m rs s:
    (select u vx q m rs s).2 = (select u vy q m rs s).2.
  Proof.
    elim: rs vx vy q m s => //= r rs IH vx vy q m s.
    case: H => //=?; rewrite !push//=; f_equal; auto.
  Qed.

  Lemma tm_is_det_tm2RC s s1 c :
    tm_is_det s c ->
    exists q qp (kP: qp \in domf s), 
      tm2RC (deref s1 (Callable2Tm c)) = Some (q, qp) /\ is_det_sig s.[kP].
  Proof.
    rewrite/tm_is_det.
    case CS: getS_Callable => //=[S].
    elim: c s1 S CS => //= [p|f IH a] s1 S.
      by case: fndP => //= kP [<-] dS; repeat eexists; eassumption.
    move=> H DS.
    have [q[qp [kP [H1 H2]]]] := IH s1 _ H DS.
    by rewrite H1; repeat eexists; apply: H2.
  Qed.

  (* Lemma mut_exclP *)

  Lemma check_rulesP s rs c fv s1:
    check_rules s rs ->
    tm_is_det s c ->
    all (fun x => check_atoms s x.2.(premises)) (bc u {| rules := rs; sig := s |} fv c s1).2.
  Proof.
    rewrite/bc.
    case DR: tm2RC => //=[[q p]].
    case: fndP => //= pP.
    rewrite push/=.
    case X: fresh_rules => [fv1 rs']/=.
    generalize (get_modes_rev q s.[pP]) => md.
    generalize fv1 => fv2.
    elim: rs fv2 md rs' s c s1 fv q p {pP} fv1 DR X => //=[|[hd bo] rs IH] fv2 md rs' s c s1 fv q p fv1 DR ++ TD.
      move=> [_ <-]//.
    case FS: fresh_rules => [fv3 rs3].
    case FR: fresh_rule => [fv4 r'][??]/=/andP[H1 H2]; subst.
    move=> /=.
    have {}IH := IH _ _ _ _ _ _ _ _ _ _ DR FS H2 TD.
    case H: H => //=; last by apply: IH.
    rewrite !push/=.
    have TD' := tiki_taka DR TD H.
    move: FR.
    rewrite/fresh_rule !push/=.
    case X: fresh_atoms => [fs2 f']/= => -[??]; subst => /=.
    rewrite /= callable_is_det_fresh in TD'.
    move: H1; rewrite/check_rule TD'/= => ?.
    rewrite (check_atoms_fresh _ X)//=.
    apply: IH.
  Qed.

  Lemma deref_empty t:
    deref empty t = t.
  Proof. by elim: t => //= [v|f -> a ->//]; case: fndP => //=. Qed.

  (* sufficient modes length for callable t *)
  Fixpoint suff_mode (t:Callable) (m:seq mode) :=
    match m, t with
    | [::], Callable_P _ => true
    | [:: _ & xs], Callable_App x _ => suff_mode x xs
    | _, _ => false
    end.

  Lemma HH q' hd qp m s :
    suff_mode hd m -> tm2RC (Callable2Tm hd) = Some (q', qp) ->
    H_head u s m q' hd.
  Proof.
    elim: hd m s qp q' => //=[p [|_ _]|f Hf a [|m0 ms]]//= s qp q' sm.
      by move=> [<-]; rewrite //= eqxx.
    case X: tm2RC => [[q2 qp2]|]//=[??]; subst.
    have:= Hf _ s _ _ sm X.
    case: m0 => //=; case: H_head => //= Y _.
    apply: unif_refl.
  Qed.

  Lemma tm2RC_rigid_deref c1 d1 h1 d2 h2 s1 s2 fv m c:
    tm2RC (Callable2Tm c1) = Some (d1, h1) ->
    H u m d2 (fresh_callable fv c1).2 s1 = Some s2 ->
    tm2RC c = Some (d2, h2) -> h1 = h2.
  Proof.
    elim: c1 d1 h1 d2 h2 s1 s2 fv m c => //=[p|f Hf r] d1 h1 d2 h2 s1 s2 fv m c.
      move=> [??]; subst.
      case: m => /=[|[] _]; case: d2 => //p; case: eqP => //=-> _.
      elim: c h1 h2 => //=[>[<-<-]|]//f Hf a Ha h1 h2.
      by case X: tm2RC => //[[c1 p1]][//].
    case H: tm2RC => [[C P]|]//=[??]; subst.
    rewrite !push/=.
    have {H}Hf := Hf _ _ _ _ _ _ _ _ _ H.
    case m => [|[]]//=; case: d2 => //= c1 t1 l1;
    case H: H => //=[s3]; have {}Hf := Hf _ _ _ _ _ _ _ H;
    case: c => //= f' a'; case tm: tm2RC => //=[[c' p']]/= + [???]; subst;
    have:= Hf _ _ tm => //.
  Qed.

  Lemma tm2RC_get_modes c1 d1 h1 d2 h2 s1 s2 fv m c l:
    tm2RC (Callable2Tm c1) = Some (d1, h1) ->
    H u m d2 (fresh_callable fv c1).2 s1 = Some s2 ->
    tm2RC c = Some (d2, h2) -> 
      get_modes_rev d1 l = get_modes_rev d2 l.
  Proof.
    elim: c1 d1 h1 d2 h2 s1 s2 fv m c l => //=[p|f Hf r] d1 h1 d2 h2 s1 s2 fv m c l.
      by move=> [??]; subst; case: m => /=[|[] _]; case: d2 => //.
    case H: tm2RC => [[C P]|]//=[??]; subst.
    rewrite !push/=.
    have {H}Hf := Hf _ _ _ _ _ _ _ _ _ _ H.
    case m => [|[]]//=; case: d2 => //= c1 t1 l1;
    case H: H => //=[s3]; have {}Hf := Hf _ _ _ _ _ _ _ _ H;
    case: c => //= f' a'; case tm: tm2RC => //=[[c' p']]/= + [???]; subst;
    have:= Hf _ _ _ tm => //; case: l => //=;
    rewrite/get_modes_rev/=/sigtm_rev/sigtm/=!add0n => m1 ml mr IH _;
    by rewrite !rev_cons/=!map_rcons/= IH.
  Qed.


  Lemma H_suff_mode l q fv hd s1 s2:
    H u l q (fresh_callable fv hd).2 s1 = Some s2 -> suff_mode hd l.
  Proof.
    elim: l hd q s1 s2 fv => //=.
      move=> hd []//= p s1 s2 fv; case fc: fresh_callable => [fv' [p'|]]/=//.
      case: eqP => //? [?]; subst.
      by case: hd fc => //= c t; rewrite !push.
    move=> m l IH hd q s1 s2 fv.
    case: m; case: q => //= c t; case fc: fresh_callable => [fv' [|f a]]//=;
    case H: H => [s3|]//=; move: fc; case: hd => //=[f' a']; rewrite !push;
    move=> [???]; subst => H1; apply: IH H.
  Qed.

  Lemma H_head_None m q hd hd' hd0 hd1 s1 s2 fv2 fv fv' p:
    H u m q (fresh_callable fv2 hd).2 s1 = Some s2 -> (*q   ~  hd*)
    tm2RC (Callable2Tm hd) = Some (hd', p) ->         (*hd  ~  hd'*)
    H_head u empty m hd' hd0 = None ->                (*hd' <> hd0*)
    fresh_callable fv hd0 = (fv', hd1) ->             (*hd0 ~  hd1*)
    H u m q hd1 s1 = None.                            (*hd1 <> q*)
  Proof.
    elim: m q hd hd' hd0 hd1 s1 s2 fv2 fv fv' p => //=.
      move=> []//p []//=; last by move => >; rewrite !push.
      move=> p1 hd hd1 hd2 s1 s2 _ fv fv' p2; case: eqP => //? [?][??]; subst.
      case: hd1 => //=.
        by move=> p1; case: eqP => //= H _ [? <-]; case: eqP => //.
      by move=> c t _; rewrite !push => -[_ <-].
    move=> m l IH q hd hd' hd0 hd1 s1 s2 fv2 fv fv' p.
    case: q; first by case: m.
    case: hd => /=; first by move=> >; case: m.
    move=> f1 a1 f2 a2; rewrite !push/=.
    case X: tm2RC => [[f1' p']|]//= + [??]; subst => /=.
    case: hd0 => /=; first by move=> p0 + _ [??]; subst; case: m.
    move=> f3 a3; rewrite !push => /= ++ [??]; subst.
    case H: H => [s1'|]/=; last by case: m.
    case FC1: fresh_callable => [fvx f1'']/=.
    case FC2: fresh_callable => [fvy f3']/=.
    have {}IH := IH _ _ _ _ _ _ _ _ _ _ _ H X _ FC2.
    case: m => UM HH; last by rewrite IH//.
    move: HH; case HH: H_head => [sh|]/=; last by rewrite IH.
    move=> HU.
    case HH': lang.H => //=[s1''].
    apply: unif_match HU UM.
  Qed.

  Lemma select_head_nil fv fv1 fv2 fv3 rs rs' hd hd' s1 s2 q m p:
    fresh_rules fv rs = (fv1, rs') ->                 (*fresh rs = rs'*)
    H u m q (fresh_callable fv2 hd).2 s1 = Some s2 -> (*hd ~ q*)
    tm2RC (Callable2Tm hd) = Some (hd', p) ->         (*hd ~ hd'*)
    select_head u hd' m rs = [::] ->                  (*select hd' rs =  [::]*)
    (select u fv3 q m rs' s1).2 = [::].               (*select q   rs' = [::]*) 
  Proof.
    elim: rs rs' fv fv1 fv2 fv3 m hd hd' s1 s2 q p => //=; first by move=> > [ _<-].
    move=> x xs IH rs' fv fv1 fv2 fv3 m hd hd' s1 s2 q p.
    rewrite !push/= => -[??]; subst => /=.
    move=> H1 H2.
    case FS: fresh_rules => [fv' xs'].
    case FR: fresh_rule => [fv'' x']/=.
    case Hd: H_head => //= SH.
    have {}IH := IH _ _ _ _ _ _ _ _ _ _ _ _ FS H1 H2 SH.
    case H: H => [s1'|]//=.
    rewrite !push/= {}IH.
    exfalso.
    case: x' FR H; case: x Hd => /= hd0 pm0 Hd hd1 pm1.
    rewrite/fresh_rule/=.
    case FC: fresh_callable => [fv''' hd01]/=.
    case FA: fresh_atoms => [fv'''' pm0']/= [???]; subst.
    by rewrite (H_head_None H1 H2 Hd FC).
  Qed.

  Lemma mut_exclP s rs fv c s1:
    mut_excl u s rs -> 
      tm_is_det s c ->
        all_but_last (fun x => has_cut_seq x.2.(premises)) (bc u {|sig:=s; rules := rs|} fv c s1).2.
  Proof.
    rewrite/bc.
    case DR: tm2RC => //=[[q p]].
    case: fndP => //= pP.
    rewrite push/=.
    case X: fresh_rules => [fv1 rs']/=.
    generalize fv1 => fv2.
    elim: rs fv2 rs' s c s1 fv q p pP fv1 DR X => //=[|[hd bo] rs IH] fv2 rs' s c s1 fv q p pP fv1 DR ++ TD.
      move=> [_ <-]//.
    case FS: fresh_rules => [fv3 rs3].
    case FR: fresh_rule => [fv4 r'][??]/=/andP[H1 H2]; subst.
    move=> /=.
    have {}IH := IH _ _ _ _ _ _ _ _ _ _ DR FS H2 TD.
    case H: H => //=[s2|]; rewrite !(IH,push)//={}IH andbT.
    have TD' := tiki_taka DR TD H.
    move: FR.
    rewrite/fresh_rule !push/=.
    case X: fresh_atoms => [fs2 f']/= => -[??]; subst => /=.
    simpl in H.
    rewrite /= callable_is_det_fresh in TD'.
    move: H1; rewrite/check_rule/mut_excl_head/=.
    have [q'[qp[qP[H3 H4]]]] := tm_is_det_tm2RC empty TD'.
    rewrite deref_empty in H3.
    rewrite H3 in_fnd H4.
    have ?:= tm2RC_rigid_deref H3 H DR; subst.
    rewrite (bool_irrelevance qP pP).
    rewrite (tm2RC_get_modes _ H3 H DR).
    clear qP H4.
    have SM := H_suff_mode H.
    have:= HH empty SM H3.
    case HH: H_head => //=[r] _.
    move: HH H H3 FS.
    generalize (get_modes_rev q s.[pP]) as m => m HH H H3 FS.
    case SH: select_head => [|h1 hs].
      by rewrite (select_head_nil _ FS H H3 SH).
    move=> /andP[CBo _].
    by rewrite (fresh_has_cut CBo X); case: select => //= _ [].
  Qed.


  Lemma is_det_no_free_alt pr c sv s1:
    check_program u pr -> tm_is_det (sig pr) c -> 
    det_tree (sig pr) (backchain u pr sv s1 c).2.
  Proof.
    rewrite /backchain/bc/check_program/check_program_aux.
    case: pr => rs s/= => /andP[].
    case X: tm2RC => //=[[q qp]]; rewrite !push/=.
    case: fndP => //= kP.
    move=> ++ H.
    have [q'[qp' [H1 [H2 H3]]]] := tm_is_det_tm2RC s1 H.
    move=> ME CR.
    have := mut_exclP sv s1 ME H.
    have := check_rulesP sv s1 CR H.
    rewrite/bc X/= in_fnd.
    case: fresh_rules => [a rs'].
    case: select => /= _.
    move=> [|[_ + {ME CR}rs]]//=; clear.
    elim: rs => //=[|[s0 r0] rs IH] [h b]/=.
      by move=> /andP[]*; rewrite det_tree_big_and cut_followed_by_det_nfa_and//.
    move=> /and3P[Cb Cr0 HL] /andP[cb].
    rewrite has_cut_seq_has_cut_big_and cb.
    rewrite det_tree_big_and cut_followed_by_det_nfa_and//=.
    by move=> /IH; rewrite /= Cr0 HL => /(_ isT).
  Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim_tree A => //=.
    rewrite success_and.
      (* by move=> /andP[/is_ko_success].
      by move=> /is_ko_success. *)
    by move=> /orP[/HA->|/andP[+ /HB->]]//; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof. by apply/contraTF => /has_cut_success->. Qed.

  Lemma step_has_cut_help p sv A s: 
    has_cut A -> has_cut (step u p sv s A).2 \/ is_cb (step u p sv s A).1.2.
  Proof.
    elim: A s sv; try by move=> /=; auto.
    - by move=> []//=; auto.
    - move=> A HA B0 B HB s sv /=.
      rewrite !push/= => /orP[].
        move=> cA; rewrite has_cut_success//=.
        by have [->|] := HA s sv cA; auto.
      case/andP=> cB0 cB.
      move: (HB (get_subst s A) sv cB).
      case: ifP => sA/=; rewrite cB0/=.
        by move=> [->|->]; rewrite ?orbT; auto.
      by rewrite cB; rewrite orbT; auto.
  Qed.

  Lemma step_keep_cut p A s sv: 
    has_cut A -> is_cb (step u p sv s A).1.2 = false -> 
      has_cut (step u p sv s A).2.
  Proof. move/step_has_cut_help => /(_ p sv s)[]//->//. Qed.

  Lemma succ_failF_no_alt A: success A = false -> failed A = false -> no_alt A = false.
  Proof. by rewrite/no_alt => -> /failedF_next_alt ->//. Qed.

  Lemma no_alt_det_tree p sP fv c s:
    no_alt (backchain u p fv s c).2 -> det_tree sP (backchain u p fv s c).2.
  Proof.
    rewrite/backchain !push/=.
    case bc: bc => [fv' [|[s0 r0] sr]] //=.
    rewrite/no_alt/=.
    rewrite next_alt_big_or//.
  Qed.

  Lemma step_no_free_alt pr sv s1 A r: 
    check_program u pr -> det_tree pr.(sig) A -> 
      step u pr sv s1 A = r ->
        det_tree pr.(sig) r.2.
  Proof.
    move=> H + <-; clear r.
    elim_tree A s1.
    - case: t => [|c]//=; rewrite !push/=.
      by apply: is_det_no_free_alt.
    - move=>/= /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - by rewrite /=!push; move=> /HB/=->.
    - rewrite step_and/= => /andP[dB].
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      rewrite (fun_if (det_tree (sig pr))).
      case SA: success.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb; first by case/orP=> [->//|/step_keep_cut->]; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /no_alt /sA failed_step//= SA.
      rewrite (succ_failF_no_alt SA fA) => /andP[+ ->]/=.
      by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
  Qed.

  Goal forall sP s, det_tree sP (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma step_next_alt {sP A} : 
    det_tree sP A -> success A ->
      next_alt true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[? _].
      by rewrite HA.
  Qed.

  Lemma build_na_is_dead {sP A}:
    det_tree sP A -> success A ->
      next_alt true A = None.
  Proof. move=> H2 H3; rewrite (step_next_alt H2)//=. Qed.

  Lemma has_cut_next_alt {A R b}: 
    has_cut A -> next_alt b A = Some R -> has_cut R.
  Proof.
    elim_tree A R b => /=.
    - case: t => //= _ [<-]//.
    (* - by move=>/andP[kA kB]; rewrite !is_ko_next_alt//. *)
    (* - by move=>/is_ko_next_alt->. *)
    - move=> /orP[].
        move=> cA.
        case: ifP => sA.
          case X: next_alt => // [A'|].
            by move=> [<-]/=; rewrite cA.
          by case nA: next_alt => //=[A'][<-]/=; rewrite (HA _ _ _ nA).
        case: ifP => //= fA.
          by case nA: next_alt => //[A'][<-]/=; rewrite (HA _ _ _ nA).
        by move=> [<-]/=; rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= sA.
        case X: next_alt => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: next_alt => //[A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and  cB0 orbT.
      case: ifP=> fA.
        case X: next_alt => //= [A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and cB0 orbT.
      by move=> [<-]/=; rewrite cB0 cB orbT.
  Qed.

  Lemma next_alt_no_alt b A A' : next_alt b A  = Some A' -> success A = b -> no_alt A = false.
  Proof. by rewrite /no_alt=> + -> => ->. Qed.

  Lemma no_free_alt_next_alt {sP A R b}:
    det_tree sP A -> next_alt b A = Some R -> det_tree sP R.
  Proof.
    elim_tree A R b => /=.
    - by case: b => // _ [<-].
    - by move=> _ [<-]//.
    - move=>/andP[fA].
      case nA: next_alt => [A'|].
        move=> + [<-]/=;rewrite (HA _ _ _ nA)//=.
        case: ifP => //= cA.
          rewrite (has_cut_next_alt _ nA)//.
        by move=> /eqP?; subst; rewrite if_same.
      case nB: next_alt => //=[B']+[<-]/=.
      case: ifP => [|_ /eqP] => ?; subst => // H.
      by rewrite (HB _ _ _ nB).
    - by case nB: next_alt => //=[B']H[<-]/=; apply: (HB B' b).
    - move=> /andP[dB +].
      case sA: (success A).
        case nB: next_alt => [B'|] => [+ [<-/=]|].
          rewrite (HB B' b)//=.
          case cB: (has_cut B); first by rewrite (has_cut_next_alt cB nB).
          case cB': (has_cut B'); rewrite /= orbC //= ?orbT.
          by rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[-> //].
        case nA: next_alt => [A'|] //= + [<-/=].
        rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (next_alt_no_alt nA)//.
        rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
        by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
      case fA : (failed A) => [|] => [|+ [<-/=]]; last by rewrite dB.
      case nA: next_alt => [A'|] => [+ [<-/=]|//].
      rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (next_alt_no_alt nA)//.
      rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
      by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
  Qed.

  Lemma step_next_alt_failedF p sv sv' A B C s b:
    check_program u p ->
      det_tree p.(sig) A -> step u p sv s A = (sv', Failed, B) ->
        next_alt b B = Some (C) -> det_tree p.(sig) C.
  Proof.
    move=> H1 H2 H3 H4.
    have /= H5 := step_no_free_alt H1 H2 H3.
    by have:= no_free_alt_next_alt H5 H4.
  Qed.

  Definition is_det u p A := forall b s sv s' B fv',
    run u p sv s A s' B b fv' -> B = None.

  Lemma run_next_alt p A: 
    check_program u p -> 
      det_tree p.(sig) A -> is_det u p A.
  Proof.
    rewrite/is_det.
    move=> H1 H2 b s sv s' B ? H3.
    elim_run H3 H1 H2.
    - apply: build_na_is_dead H2 SA.
    - by apply/IH/(step_no_free_alt H1 H2 eA).
    - by apply/IH/no_free_alt_next_alt/nA.
  Qed.

  Lemma main p t:
    check_program u p -> tm_is_det p.(sig)  t -> 
      is_det u p (TA (call t)).
  Proof.
    move=> H1 fA HA.
    apply: run_next_alt H1 _ HA.
    apply: fA.
  Qed.

  Print Assumptions  main.
  
  (* Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == cut end.
    
    Definition AllTailCut p := (all tail_cut (rules p)).

    Lemma cut_in_prem_tail_cut : AllTailCut p -> check_program u p.
    Proof.
      case: p; rewrite/AllTailCut/check_program/=.
      move=> rules sig H; apply/andP; split.
        elim: rules sig H => //= x xs IH sig /andP[H1 H2].
        rewrite IH//andbT.
        rewrite/mut_excl_head/=.
        case: tm2RC => [[c p']|]//; case: fndP => //= kP.
        case: ifP => //= HD.
        case: x H1 => /= hd pm; clear -H2.
        rewrite/tail_cut/=.
        elim: pm hd xs H2 => //= x xs IH.
        generalize sig.[kP].
        move : (sig.[kP]) => /=.
      move=> H; apply/andP; split. move: H; case: p.
      rewrite /AllTailCut /check_program.
      rewrite /tail_cut /check_rules.
      remember (rules p) as RS.

      apply: sub_all => r; clear.
      rewrite /check_rule.
      case X: callable_is_det => //=.
      case: r X => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sP t:
      AllTailCut p -> tm_is_det sP t -> is_det (TA (call t)).
    Proof.
      move=> /(cut_in_prem_tail_cut sP).
      apply main.
    Qed.
  End tail_cut. *)

  (* Print Assumptions tail_cut_is_det. *)

End check.
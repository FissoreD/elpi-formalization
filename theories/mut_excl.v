From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars fresh unif.

Section good_mode.
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
  Definition good_modesI (s: sigT) := [forall x : domf s, all_inp s.[valP x]].

  Lemma all_mode_good_mode d l: all_mode d l -> good_mode l.
  Proof. elim: l => //= m f Hf a Ha /andP[/eqP->{m}]; destruct d => //. Qed.

  Lemma good_modesI_GM M:
    good_modesI M -> good_modes M.
  Proof. by move=> H; apply/forallP => x; have:= all_mode_good_mode (forallP H x). Qed.


  Lemma good_modes_in p sP (pP: p  \in domf sP):
    good_modes sP -> good_mode sP.[pP].
  Proof. by move=> GM; have:= forallP GM [`pP]; rewrite valPE. Qed.
End good_mode.

Definition arri t := if t is _ --i--> _ then true else false.
Definition arro t := if t is _ --o--> _ then true else false.

(* sub input term: return a subterm of t where all output have been removed *)
(* Fixpoint subit (sP:sigT) t : Tm * option (S) :=
  match t with
  | Tm_P p => (t, sP.[?p])
  | Tm_App f a =>
    let (f, ty) := subit sP f in
    match ty with
    | Some (arr m tl tr as ty) =>
      ((if m == input then Tm_App f a else f), Some (if m == input then tr else ty))
    | _ => (f, None)
    end
  | _ => (t, None)
  end. *)

(* Lemma subitP sP t t' r: subit sP t = (t', Some r) -> 
  exists p, exists pP : p \in sP, 
    [/\ get_tm_hd t = inl p, get_tm_hd t' = inl p & eat_ty (term_arg t') sP.[pP] = Some r]
  .
Proof.
  elim: t t' r => //=[p|f Hf a Ha] t' r.
    by case: fndP => pP//[<-<-]/=; eexists _, pP.
  case H: subit => //[t2 [[//|m tl tr]|//]] H'.
  have [p[pP [fp f'p E]]]:= Hf _ _ H.
  exists p, pP.
  move: H'; case: m E {H} => //= E [<-<-]//; split => //=.
  case: sP.[pP] E => //=; first by case: t2 f'p.
  by move=> m tl' tr';apply: eat_ty_arr.
Qed. *)

(* Lemma subit_inp sP t t' r:
  subit sP t = (t', Some r) -> arri r ->
  t = t'.
Proof.
  elim: t t' r => //=[p|f Hf a _] t' r; first by move=> [<-].
  case X: subit => [t [[//|[] tr tl]|//]]/=[??]; subst => //=.
  by have <-:= Hf _ _ X isT.
Qed. *)

(* Lemma H_sub u sP fv q h s:
  H u sP fv q h s ->
  let x := subit sP q in
  let y := subit sP h in
  [/\ x.2 = y.2 & H u sP fv x.1 y.1 s].
Proof.
  elim: q h fv s => //[p|f Hf a _] [p'|//|//|f' a']//=fv s.
    by case: ifP => ///eqP->; case: fndP => //=pP[<-]/=.
  case H: H => [[[[|m tl tr] s'] fv']|]//=.
  have {Hf}[H2 H1] := Hf _ _ _ (isSomeP H).
  rewrite !push/=.
  case su1: subit H1 H2 => //=[t1 os1] H1 H2.
  case su2: subit H1 H2 => //=[t2 os2] H1 H2; subst.
  case I: (_ s') => [r'|]//= _; subst => /=.
  case: os2 su1 su2 => //=[[|m' t1' t2']]//= su1 su2.
  split => //=.
  destruct m' => //=.
  move: H1; case Hs: lang.H => //= [[[ty sx] fx]]//= _.
  have [p[pP [fp t1p Et2]]] := subitP su1.
  have [] := HP Hs.
  rewrite t1p => /esym t2p at1t2 [p'[p'P [?]]]; subst.
  rewrite (bool_irrelevance p'P pP) Et2 => -[?]; subst.
  rewrite/=.
  have ?:= subit_inp su1 isT; subst.
  have ?:= subit_inp su2 isT; subst.
  move: Hs; rewrite H => -[?????]; subst.
  move: I => /=->//.
Qed. *)

(* Section test.
  Local Notation D := (Tm_D (ID 1)).
  Local Notation p := (IP 2).
  Local Goal subit 
    fmap0.[p <- arr input (b Exp) (arr input (b Exp) (arr output (b Exp) (arr output (b Exp) (b (d Pred)))))]
    (Tm_App (Tm_App (Tm_App (Tm_P p) D) D) D) = ((Tm_App (Tm_App (Tm_P p) D) D), Some ((arr output (b Exp) (arr output (b Exp) (b (d Pred)))))).
  Proof. by rewrite/subit !FmapE.fmapE/=. Qed.
End test. *)

Section mut_excl.
  Variable u : Unif.

  (* returns if all inputs can be unified *)
  (* inputs come before outputs *)
  (* outputs are neutral for this function *)
  Fixpoint H_head (sP:sigT) (q : Tm) (h: Tm) : option S :=
  match q,h with
  | Tm_P p, Tm_P p' => if p == p' then sP.[?p] else None
  | Tm_App f a, Tm_App f' a' =>
    if H_head sP f f' is Some (arr m _ r) then
      if (m == output) || lang.unify u f f' fmap0 then Some r
      else None
    else None
  | _, _ => None
  end.

  Fixpoint H_inp (sP:sigT) fv (q : Tm) (h: Tm) s : option ((S * Sigma)) :=
    match q,h with
    | Tm_P p, Tm_P p' => if p == p' then omap (fun x => ((x, s))) sP.[?p] else None
    | Tm_App f a, Tm_App f' a' =>
      if H_inp sP fv f f' s is Some ((arr m _ r), s) then
        if m == input then omap (fun x => (r, x)) (lang.matching u fv a' a s)
        else Some ((r, s))
      else None
    | _, _ => None
    end.

  (* Fixpoint term_hd_inp (sP:sigT) (t:Tm) : nat * option (S) :=
    match t with
    | Tm_P p => (0, sP.[?p])
    | Tm_App f a =>
      let: (n, ty) := term_hd_inp sP f in 
      match ty with
      | Some (arr m tl tr as ty) => 
        if m == input then (n.+1, Some tr) else (n, Some ty)
      | _ => (n, None)
      end
    | _ => (0, None)
    end. *)

  (* Lemma eat_ty_arr1 n md tf ta m tl tr:
    eat_ty n ta = Some tr -> 
    eat_ty n (arr md tf ta) = Some (arr m tl tr).
  Proof.
    elim: n md tf ta m tl tr => [|n IH] md tf ta m tl tr/=.
      admit.
    case: ta => //=>; apply: IH.
    by case: ta => [|>]; [case n|apply: IH].
  Qed. *)


  Lemma HH_inpP sP fv t1 t2 s r: H_inp sP fv t1 t2 s = Some r -> 
    [/\ get_tm_hd t1 = get_tm_hd t2, term_arg t1 = term_arg t2 &
      exists p, exists2 pP : p \in sP, get_tm_hd t1 = inl p & 
      eat_ty (term_arg t1) sP.[pP] = Some r.1].
      (* eaty ... = tearm_hd_inp .2 *)
  Proof.
    elim: t1 t2 fv s r => //=[p|f Hf a _] [p'|d|v|f' a']//= fv s r.
      case: eqP => //<-; case: fndP => //=pP[<-]; split => //.
      by exists p, pP.
    case H: H_inp => //[[[|m tl tr] s']]//= I.
    (* case : (_ s') => //= sz [?]; subst => /=. *)
    have {Hf}/=[Hx Hy [p [pP H1 H2]]] := Hf _ _ _ _ H.
    rewrite Hy; split => //=.
    eexists p, pP => //=.
    move: H2; case X: sP.[pP] => //=[b|m' tl' tr'].
      by destruct term_arg.
    move=> /eat_ty_arr; rewrite Hy.
    move: I; destruct m; [case lang.matching => //=?|] => -[<-]//.
  Qed.

  Lemma eat_ty_good_mode n m res:
    good_mode m -> eat_ty n m = Some res -> good_mode res.
  Proof.
    elim: n m res => //=[|n IH] m res; first by move=> +[<-].
    case: m => //=-[] l r; first by apply: IH.
    by move=> /all_mode_good_mode; apply: IH.
  Qed.

  Lemma HH_inp sP fv q h s r:
    good_modes sP ->
    H u sP fv q h s = Some r ->   
    exists r', [/\ H_inp sP fv q h s = Some r', (arri r.1 -> r = r') & r.1 = r'.1].
  Proof.
    move=> GM; elim: q h s r => //[p|f Hf a _] [p'|||f' a']//= s r.
      by case: eqP => //->; case: fndP => //=pP[<-]; eexists; repeat split; by exists 0.
    case H: H => //[[[|m tf tr] s']]//=.
    case I: (_ s') => //=[s''][?]; subst.
    have {Hf} [[ty' sx] /= [+ AI H2]] := Hf _ _ _ H; subst.
    case HI: H_inp => //-[?]; subst.
    move: I; destruct m => //=.
      move: AI => /(_ isT) [?]; subst => ->.
      by eexists; split => //.
    eexists; split => //.
    case: tr {AI HI} H => [|[]]//=?? H.
    have [?? [p[pP fp]]] := HP H.
    by move=> /(eat_ty_good_mode (good_modes_in pP GM)).
  Qed.

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
  
Lemma all_out_good_modeM m tl:
  match m with
  | output => all_out tl
  | input => good_mode tl
  end -> good_mode tl.
Proof. by case: m => ///all_mode_good_mode. Qed.

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

Lemma eat_ty_inp n t m t1 t2:
  eat_ty n t = Some (arr m t1 t2) ->
  good_mode t ->
  arri t2 ->
  m = input.
Proof.
  elim: n t m t1 t2 => [[//|]|n IH]//=.
    by move=> ??? m ? t [???]; subst; case: m => //=; case: t => //=[[]]//.
  by move=> [|[]]//= _ s m t1 t2 + /all_mode_good_mode ; apply: IH.
Qed.

(* Lemma H_all_inp_v2 sP v1 t1 t2 s1 r:
  good_modes sP ->
  H u sP v1 t1 t2 s1 = Some r ->
  arri r.1 -> r.2 = v1 `|` vars_tm t1.
Proof.
  move=> GM.
  elim: t1 t2 s1 v1 r => [p|//|//|f Hf a _] [p'|//|//|f' a']//= s1 v1 r.
    case: eqP => //=; case: fndP => //=pP _ [<-]//=.
    by rewrite fsetU0.
  case H: H => [[[[|m tf' tr'] s1' v1']]|]//=.
  case I:  (_ s1') => //=[r'][<-]{r}/= AI.
  have /=[hff' aff' [p[pP H1 E]]] := HP H.
  have := forallP GM [`pP]; rewrite valPE => {}GM.
  have ? := eat_ty_inp E GM AI; subst => /=.
  simpl in I.
  have /=? := Hf _ _ _ _ H isT; subst.
  by rewrite fsetUA.
Qed. *)

Lemma fdisjoint_rem (K: choiceType) (qa qf:{fset K}) :
  (qa `\` qf) # qf.
Proof. by apply/fdisjointP => k; rewrite !inE => /andP[]. Qed.

Lemma mp_trans: transitive mp.
Proof.
  move=> b a c M1 M2; apply/forallP => -[x xa].
  have:= forallP M1 [`xa]; rewrite !valPE/=.
  case: fndP => //= xb/eqP[]; have:= forallP M2 [`xb].
  rewrite valPE/=; case: fndP => //xc/eqP[<-] <-.
  by rewrite derefxx//.
Qed.

Lemma H_mp sP fv q hd s1 r: acyclic_sigma s1 ->
  H u sP fv q hd s1 = Some r -> mp s1 r.2.
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a _] fv [p'|//|//|f' a']// s1 r.
    by case: eqP => //->; case: fndP => //= ? A[<-]; apply: mp_id.
  move=> A; case H: H => [[[|m tl tr] s']|]//=.
  case M: (_ s') => //=[{}r][<-]/=.
  have {}Hf := Hf _ _ _ _ A H.
  have A' := acyclic_sigma_H A H.
  have: mp s' r.
    by move: M; destruct m => /=/(montanari_mp A' (disjoint_L_deref _ _ A')) ->//.
  by apply: mp_trans.
Qed.

Lemma H_deref_eq sP fv q hd s1 r:
  acyclic_sigma s1 ->
    H u sP fv q hd s1 = Some r ->
      deref r.2 (deref s1 q) = deref r.2 (deref s1 hd).
Proof.
  elim: q fv hd s1 r => //=[p|f Hf a _] fv [p'|//|//|f' a']// s1 r.
    by case: eqP => //-> A; case: fndP => //.
  move=> A.
  case H: H => [[[|m tl tr] s1']|]//=.
  case X: (_ s1') => //= [sx][?]; subst => /=.
  have /= A' := acyclic_sigma_H A H.
  have s1s1' := H_mp A H.
  have s1'sx: mp s1' sx.
    have M := montanari_mp A' (disjoint_L_deref _ _ A').
    by move: X; destruct m => /= /M.
  have MP := mp_trans s1s1' s1'sx.
  have /={Hf} := Hf _ _ _ _ A H.
  rewrite !derefxx//= => Hf.
  rewrite -(@derefxx s1')// Hf derefxx//.
  move: X; destruct m => /matchingP->//.
Qed.

(* Lemma get_input_vars_inp f p sP t (pP: p \in sP):
  good_modes sP -> get_tm_hd f = inl p ->
  eat_ty (term_arg f) sP.[pP] = Some t -> arri t ->
  (get_input_vars sP f).1 = vars_tm f.
Proof.
  move=> G; elim: f t => //=[f Hf a _] t GP.
  case H: sP.[pP] => //=[m tr tl] E AI.
  have {Hf} /= := Hf (arr m tr tl) GP; rewrite H => /=.
  rewrite H /= in Hf.
  Search eat_ty_arr *)

(* Lemma matching_disj_froz:
  vars_tm a' 
  matching froz a' a sm = Some r -> *)

Lemma xx sP froz t1 t2 s r:
  good_modes sP ->
  fdisjoint (domf s) froz ->
  H u sP froz t1 t2 s = Some r ->
  arri r.1 ->
  (domf r.2) # froz.
Proof.
  move=> GM.
  elim: t1 t2 s r => //[p|f Hf a _] [p'|//|//|f' a']//= s r.
    case: eqP => //-> H; case: fndP => //=pP[<-]//=; rewrite /=?fdisjoint0X fsetU0//=.
  case H: H => [[[|m tf' tr'] sm]|]//=.
  move=> sfroz.
  case I: (_ sm) => //=[r'][?] AI; subst; simpl in *.
  have /=[hff haa [p'[pP hp E]]] := HP H.
  have ? := eat_ty_inp E (good_modes_in pP GM) AI; subst.
  rewrite/= in I *.
  have /={Hf} := Hf _ _ _ sfroz H isT.
  move=> {}Hf.
  have Ha := matching_ext1 I.
  by apply/(fdisjointWl Ha); rewrite fdisjointUX Hf/= fdisjoint_rem.
Qed.

Lemma H_all_inp sP v1 query head s1 r:
  acyclic_sigma s1 ->
  good_modes sP ->
  fdisjoint (domf s1) v1 ->
  H u sP v1 query head s1 = Some r -> arri r.1 ->
  matching v1 head query s1.
Proof.
  move=> A GM sq H AI.
  rewrite/matching/montanari_deref/montanari_pair.
  apply: exists_montanari => //.
    by rewrite disjoint_L_deref.
  exists r.2; split => //.
    by apply: acyclic_sigma_H H.
    have:= H_deref_eq A H.
    by rewrite/unifier/unif_pair/map_prod1/= andbT => ->.
  by apply: xx H _.
Qed.

(* Lemma Hmatching u sP fv f f1 s1:
  good_modesI sP ->
  H u sP fv f f1 s1 ->
  matching fv f f1 s1.
Proof. *)

Lemma get_input_vars2 sP fv q h s x:
  H u sP fv q h s = Some x -> (get_input_vars sP q).2 = Some x.1.
Proof.
  elim: q h s x => //=[p|f Hf a _][p'|||f' a']//=s [ty s'].
    by case: eqP => //=->; case: fndP => //= ? [<-].
  case H: H => [[[|m tl tr] s'']|]//=.
  case M: (_ s'') => //=[r][??]; subst.
  have:= Hf _ _ _ H.
  by case X: get_input_vars => //=?; subst => /=.
Qed.

Lemma get_input_vars_vars_tm sP fv q h s r:
  good_modes sP ->
  H u sP fv q h s = Some r -> arri r.1 ->
  (get_input_vars sP q).1 = vars_tm q.
Proof.
  move=> GM; elim: q h s r => [p|||f Hf a _]//=[p'|||f' a']//= s r.
  case H: H => //=[[[|m tl tr] s']]//=.
  case X: (_ s') => //=[s''][?]; subst.
  case: tr H => //[[] tl' tr']//= H' _.
  have [_ _ [p [pP G E]]] := HP H'.
  have := eat_ty_good_mode (good_modes_in pP GM) E.
  destruct m => //= _.
  have /= := Hf _ _ _ H' isT.
  case IV: get_input_vars => //=[fv' ty'] ?; subst.
  by have:= get_input_vars2 H'; rewrite IV => /=?; subst.
Qed.

Lemma SHS sP fv1 fv2 query hd2 hd1 (s1 s2:Sigma):
  good_modes sP ->
  acyclic_sigma s1 -> acyclic_sigma s2 ->
  fdisjoint (domf s1) fv1 ->
  fdisjoint (domf s2) fv2 ->
  (get_input_vars sP query).1 `<=` fv1 ->
  (get_input_vars sP query).1 `<=` fv2 ->
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
    move=> _ _ _ _ _ _ _ _ _; case: eqP => // <-; case: eqP => //->; case: fndP => //=.
  move=> S1 S2 d2f2 s1f1.
  rewrite 2!fdisjointXU => /andP[V1 V2] /andP[V3 V4].
  rewrite ?fdisjointUX !fdisjointXU.
  move=> /andP[/andP[f1f2 f1a2] /andP[a1f2 a1a2]].
  move=> /andP[/andP[ff1 fa1] /andP[af1 aa1]].
  move=> /andP[/andP[ff2 fa2] /andP[af2 aa2]].
  (* move=> /andP[Da Db] /andP[Dc Dd]. *)
  move=> /andP[s1f s1a] .
  move=> /andP[s2f s2a] .
  case H1 : H => //=[[[//|m1 tf1 ta1] s1']].
  case H2 : H => //=[[[//|m2 tf2 ta2] s2']].
  have [hh1 ha1 [p[pP hf1 he]]] := HP H1.
  have:= HP H2.
  rewrite hh1 ha1 => -[hh2 ha2 [p'[pP']]].
  rewrite -hh1 hf1 => /esym [?]; subst.
  rewrite (bool_irrelevance pP' pP) -ha1 he => -[???]; subst.
  (* case I1: (_ s1') => //=[r1].  *)
  (* case I2: (_ s2') => //=[r2] _ _. *)
  have fv2sub : (get_input_vars sP f).1 `<=` fv2.
    by move: s1f1; apply: fsubset_trans => //=; case: get_input_vars => //= ? [[|[]]|]//=; rewrite fsubsetUl.
  have fv1sub : (get_input_vars sP f).1 `<=` fv1.
    by move: d2f2; apply: fsubset_trans => //=; case: get_input_vars => //= ? [[|[]]|]//=; rewrite fsubsetUl.
  have {Hf} := Hf _ _ _ _ _ _ A1 A2 S1 S2 fv1sub fv2sub V1 V3 f1f2 ff1 ff2 s1f s2f (isSomeP H1) (isSomeP H2).
  case HH: H_head => //=[ty'] _.
  have [Hx Hy [p'[{}pP']]] := H_headP HH.
  rewrite -hh1 hf1 => -[?]; subst.
  rewrite -ha1 (bool_irrelevance pP' pP) he => -[?]; subst.
  destruct m2 => //=.
  rewrite ifT => //.
  have:= forallP GM [`pP]; rewrite valPE => GM'.
  have /= Hs := H_all_inp A1 GM S1 H1 isT.
  have /= Hr := H_all_inp A2 GM S2 H2 isT.
  rewrite !(fdisjoint_sym (vars_tm f)) in ff1, ff2.
  have ivf1 := get_input_vars_vars_tm GM H1 isT.
  rewrite ivf1 in fv1sub, fv2sub.
  apply: matching_unify_trans Hs Hr => //.
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

Fixpoint make_all_inp m :=
  match m with
  | arr m l r => if m == output then b Exp else arr input l (make_all_inp r)
  | b _ => m
  end.

Definition make_all_inpM (m:sigT) : sigT :=
  [fmap x: domf m => make_all_inp m.[valP x]].


Fixpoint inp_term (sP:sigT) t :=
  match t with
  | Tm_P p => omap (fun x => (t, x)) sP.[?p]
  | Tm_D _ | Tm_V _ => None
  | Tm_App f a =>
    match inp_term sP f with
    | Some (t, (arr m l r as ty)) =>
      Some ((if m == input then (Tm_App t a) else t), r)
    | _ => None
    end
  end.  

Lemma H_inp_arri (sP:sigT) v t1 t2 s r:
  good_modes sP ->
  H u sP v t1 t2 s = Some r -> arri r.1 ->
  [/\ inp_term sP t1 = Some (t1, r.1) & inp_term sP t2 = Some (t2, r.1)].
Proof.
  move=> GM; elim: t1 t2 s r => //=[p|f Hf a _] [p'|//|//|f' a']//= s r.
    by case: eqP => //->; case: fndP => //=pP [<-].
  case H: H => //[[[//|m tf ta] s']] + AI.
  case I: (_ s') => //=[r'][?]; subst.
  simpl in *.
  have [ff ff' [p[pP fp E]]] := HP H.
  have/=:= eat_ty_good_mode (good_modes_in pP GM) E.
  destruct m; last first.
    by destruct ta as [|[]].
  move=> gmta; simpl in *.
  by have/=[->->]:= Hf _ _ _ H isT.
Qed.

Lemma H_changeSP (sP1 sP2:sigT) v f f' p s:
  get_tm_hd f = inl p ->
  sP1.[?p] = sP2.[?p] ->
  H u sP1 v f f' s = H u sP2 v f f' s.
Proof.
  move=> + H.
  elim: f f' s => //[p'|f Hf a _] [p''|||f' a']//= s.
    move=> [->]; case: eqP => //=.
    by move: H; case: fndP => //=pP <-.
  by move=> fp; rewrite Hf//.
Qed.

(* Lemma H_make_all_inp p sP v f f' s r (pP: p \in sP):
  good_modes sP ->
  get_tm_hd f = inl p ->
  H u sP v f f' s = Some r -> arri r.1 ->
  all_inp sP.[pP].
Proof.
  move=> GM.
  elim: f f' s r => //[p'|f Hf a _] [p''|||f' a']//= s r.
    case: eqP => //->[->]; rewrite in_fnd//= => -[<-]/=.
    case X: sP.[pP] => //=[[] tl tr]//=.
    have:= good_modes_in pP GM; rewrite X => //=. *)

Fixpoint relA t1 t2 :=
  match t1 with
  | arr m l r => 
    if m == input then 
    match t2 with
    | arr input _ r' => relA r r'
    | _ => false
    end
    else true
  | _ => true
  end.

Lemma relA_mkI s: relA s (make_all_inp s).
Proof. elim: s => //=m f Hf a Ha; case: m => //=. Qed.

Lemma H_inp_arri' sP v f f' s r1 r2:
  good_modes sP ->
  H u sP v f f' s = Some r1 -> arri r1.1 ->
  H u (make_all_inpM sP) v f f' s = Some r2 ->
  relA r1.1 r2.1 /\ r1.2 = r2.2.
Proof.
  move=> GM; elim: f f' s r1 r2 => //[p|f Hf a _][p'|||f' a']// s r1 r2.
    rewrite/H; case: eqP => //->; case: fndP => //pP[<-].
    rewrite in_fnd/= ffunE valPE => + [<-]/=.
    by case: sP.[pP] => //=[[]]//= *; rewrite relA_mkI.
  rewrite/=; case H: H => //[[[|m tl tr] sx]]//=.
  case X: (_ sx) => //=[r'] [?]; subst.
  move=> /=; case: tr H => [|[] tl' tr']//= H _.
  have [ff ff' [p[pP fp E]]] := HP H.
  have /= := eat_ty_good_mode (good_modes_in pP GM) E.
  destruct m => //= GMTR'.
  case H' : lang.H => //[[[//|m' tl2 sr2]]sx'].
  case M: (_ sx') => //=[k][?]; subst => /=.
  have [{}Hf /= ?] /= := Hf _ _ _ _ H isT H'; subst.
  destruct m' => //=.
  by move: M X; rewrite/= => ->[->].
Qed.

Lemma H_inpP (sP:sigT) v t1 t2 s r:
  good_modes sP ->
  H u sP v t1 t2 s = Some r ->
  exists x y, 
    [/\ inp_term sP t1 = Some x, x.2 = r.1,
        inp_term sP t2 = Some y, y.2 = r.1 &
      H u (make_all_inpM sP) v x.1 y.1 s].
Proof.
  elim: t1 t2 s r => //[p|f Hf a _][p'|||f' a']//=s r GM.
    case: eqP => //->; case: fndP => //= pP[<-].
    do 2 eexists; split => //.
    by rewrite ![fst _]/=/lang.H eqxx in_fnd//=.
  case H: H => //[[[|m tf ta] s']]//=.
  case X: (_ s') => //=[r'] [?]; subst.
  have [[t1' s1'] [[t2' s2'] /= [I1 ? I2 ? {}Hf]]] := Hf _ _ _ GM H; subst.
  rewrite I1 I2.
  do 2 eexists; split => //=.
  destruct m => //=.
  case Hf: lang.H Hf => //=[[tx sx]] _.
  simpl in X.
  have /=[] := H_inp_arri GM H isT.
  rewrite I1 I2 => -[?][?]; subst.
  have [ff ff' [p[pP fp E]]] := HP H .
  have [/=+?] := H_inp_arri' GM H isT Hf; subst.
  rewrite/=; destruct tx => //; destruct m => //=.
  by rewrite X.
Qed.

Lemma get_input_vars_sub sP query:
  (get_input_vars sP query).1 `<=` vars query.
Proof.
  elim: query => //= f + a _.
  case: get_input_vars => fv s/= H.
  have {}H:= fsubset_trans H (fsubsetUl _ (vars a)).
  by case: s => [[|[]]|]//= _ _; rewrite fsubUset//= H//=fsubsetUr.
Qed.

Lemma HSH sP rules hd query s: 
  good_modes sP ->
  acyclic_sigma s ->
  (* (get_input_vars sP query).1 `<=` fv -> *)
  [disjoint domf s & vars_tm query] ->
  [disjoint vars_tm hd & v_prog rules] ->
  [disjoint vars_tm query & v_prog rules] ->
  [disjoint vars_tm query & vars_tm hd] ->
  [disjoint vars_sigma s & v_prog rules] ->
  [disjoint vars_sigma s & vars_tm hd] ->
  H u sP (get_input_vars sP query).1 query hd s ->
  select_head u sP hd rules = [::] ->
  (select u sP query rules s).2 = [::].
Proof.
  move=> GM.
  elim: rules query s hd => //=-[hd bo] rs IH/= query s h' AS sq.
  rewrite !v_prog_cons /varsU_rhead /varsU_rprem/=.
  rewrite !fdisjointXU -!andbA.
  move=> /and3P[h'h h'b h'r] /and3P[qh qb qr] qh' /and3P[sh sb sr sh'] H1.
  case HH: H_head => //= S1.
  have {IH} := IH _ _ _ AS sq h'r qr qh' sr sh' H1 S1.
  case S: select => //=?; subst.
  case H2: H => [[ty s']|]//=.
  have {}HH := isNoneP HH.
  exfalso; apply: negP HH; rewrite negbK.
  have sq' := fdisjointWr (get_input_vars_sub sP _) sq.
  apply: SHS H1 (isSomeP H2) => //=.
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
  FRS1.1 `<=` fx ->
  FRS2.1 `<=` fy ->
  select_head u sP ((lang.rename fx hd empty).2) FRS1.2 = [::] ->
  select_head u sP ((lang.rename fy hd empty).2) FRS2.2 = [::].
Proof.
  elim: rs fx fy fv1 fv2 hd => //= x xs IH fx fy fv1 fv2 hd; rewrite !push/=.
  move=> H2 H3.
  rewrite !(head_fresh_rule).
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
  have [[t1 si1][[t2 si2]/= [I1 ? I2 ? HH]]] := H_inpP GM H; subst.
  apply: HSH (isSomeP H) HS => //.
  (* have:= HSH _ _ _ _ _ _ _ _ _ HH => //=. *)
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



From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars fresh unif.

Section checker.

  Definition check_atom sP (a: Atom) :=
    match a with
    | cut => true
    | call t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)
  Fixpoint check_atoms sP (s: seq Atom) :=
    match s with
    | [::] => true
    | cut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | call c :: xs => (tm_is_det sP c || has_cut_seq xs) && check_atoms sP xs
    end.

  Definition check_rule sP head prems :=
    (tm_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules (p:program) :=
    all (fun x => check_rule p x.(head) x.(premises)) p.(rules).
End checker.

Lemma is_det_rename sP fv hd m:
  tm_is_det sP (rename fv hd m).2 =
    tm_is_det sP hd.
Proof.
  rewrite/rename!push/=.
  move: (fresh_tm _ _ _) => -[]/= _.
  by elim: hd.
Qed.

Lemma check_atom_fresh sP x sv m:
  check_atom sP (fresh_atom sv x m).2 = check_atom sP x.
Proof. by destruct x; rewrite //= !push/= is_det_rename. Qed.

Lemma all_check_atom_fresh sP xs sv m:
  all (check_atom sP) (fresh_atoms sv xs m).2 = all (check_atom sP) xs.
Proof. by elim: xs sv => //=x xs IH sv; rewrite !push/= IH check_atom_fresh. Qed.

Lemma check_atoms_fresh sP sv bo m:
  check_atoms sP (fresh_atoms sv bo m).2 = check_atoms sP bo.
Proof.
  elim: bo sv => //= -[|c] xs IH sv; rewrite !push//=IH//all_check_atom_fresh//.
  rewrite !push/= is_det_rename has_cut_seq_fresh//.
Qed.

Section check.
  (* Variable u : Unif. *)
  Definition u : Unif := mk_Unif unify matching.
  Notation runT := (runT u).

  Fixpoint has_cut A :=
    match A with
    | Unexplored cut => true
    | Unexplored (call _) => false
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


  Definition nilA A := prune (success A) A == None.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is det if A' and B are deterministic
    "((A, A') ; B) , !, C" is det if C is deterministic, because any alt from first conjunct dies
    "((A, A') ; KO) , C" is det
    "(A ; B)" for any A and B is not det since nothing prevents the execution of B if A fails
  *)
  Fixpoint det_tree p A :=
    match A with
    | Unexplored a => check_atom p a
    | KO | OK => true
    | And A B0 B =>
        det_tree p B && 
        (nilA A ||
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          ((det_tree p A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq p B0)) (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree p B
    | Or (Some A) _ B =>
        det_tree p A && 
        if has_cut A then det_tree p B 
        else (B == KO) 
    end.

  Lemma has_cut_big_and x xs:
    has_cut (big_andA x xs) = has_cut_seq (x::xs).
  Proof. by elim: xs x => //=[|x xs ->][]//=; rewrite andbb. Qed.

  Lemma has_cut_seq_has_cut_big_and l:
    has_cut (big_and l) = has_cut_seq l.
  Proof. by case: l => >//; rewrite /=has_cut_big_and//. Qed.

  Lemma det_tree_big_and sP L:
    det_tree sP (big_and L) = det_tree_seq sP L.
  Proof.
    case: L => //= + L.
    elim: L => [|x xs IH][|c]//=; rewrite ?(orbF,andbT)//=IH;
    rewrite (andbb,has_cut_big_and)//=andbb.
    by case: check_atom; case: det_tree_seq; case: has_cut_seq; rewrite//=andbF.
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

  Lemma no_alt_cutl A: success A -> nilA (cutl A).
  Proof. by rewrite /nilA success_cut => ->; rewrite prune_cutl. Qed.

  Lemma det_tree_cutl {sP A}: success A -> det_tree sP (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= => /andP[sA sB]/=.
    by rewrite sA HA// HB//no_alt_cutl//.
  Qed.

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
  Qed.

  Lemma callable_ren m hd p:
    get_tm_hd (ren m hd) = inl p <-> get_tm_hd hd = inl p.
  Proof. by elim: hd => //= [q|d|v|f Hf a Ha]. Qed.

  Lemma callable_rename fv hd p mp: get_tm_hd (rename fv hd mp).2 = inl p <-> get_tm_hd hd = inl p.
  Proof. by rewrite/rename!push/= => /=; split => /callable_ren. Qed.

  Lemma check_rulesP p c fv s1:
    check_rules p ->
    tm_is_det p (deref s1 c) ->
    all (fun x => check_atoms p x.2) (bc u p fv c s1).2.
  Proof.
    case: p => [rs s].
    rewrite/bc/=/check_rules/= => CR TD.
    case: ifP => // _.
    (* case DR: get_tm_hd => //=[p]. *)
    (* case: fndP => //= pP. *)
    rewrite !push/=.
    (* move: (flatten_mode _) CR. *)
    elim: rs s s1 fv c TD CR => //= -[hd bo] xs IH sig s fv c/= .
    move=> TD /andP[cbo cxs].
    have {}IH := IH _ _ _ _ TD cxs.
    rewrite !push/= head_fresh_rule/=.
    (* rewrite IH. *)
    (* case:eqP => //= /esym tH. *)
    case H: H => //=[s'].
    rewrite !push/= IH andbT.
    rewrite premises_fresh_rule/=.
    rewrite check_atoms_fresh.
    move: TD cbo; rewrite /check_rule /tm_is_det.
    have [HE HE' [p[pP Hp E]]] := HP H.
    set X := fresh_rules _ _ in HE HE'.
    rewrite Hp in_fnd.
    have:= proj1 (callable_rename X.1 hd p fmap0) .
    rewrite -HE Hp => /(_ erefl) ->.
    by rewrite in_fnd => ->.
  Qed.

  Lemma deref_empty t:
    deref fmap0 t = t.
  Proof. by elim: t => //= [v|f -> a ->//]; case: fndP => //=. Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim_tree A => //=.
    rewrite success_and.
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
      move: (HB (next_subst s A) sv cB).
      case: ifP => sA/=; rewrite cB0/=.
        by move=> [->|->]; rewrite ?orbT; auto.
      by rewrite cB; rewrite orbT; auto.
  Qed.

  Lemma step_keep_cut p A s sv: 
    has_cut A -> is_cb (step u p sv s A).1.2 = false -> 
      has_cut (step u p sv s A).2.
  Proof. move/step_has_cut_help => /(_ p sv s)[]//->//. Qed.

  Goal forall sP s, det_tree sP (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma det_check_prune_succ {sP A} : 
    det_tree sP A -> success A -> prune true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite/nilA sA.
      case: eqP => pA.
        by rewrite pA//.
      by move => /andP[? db]; rewrite HA//.
  Qed.

  Lemma has_cut_prune {A R b}: 
    has_cut A -> prune b A = Some R -> has_cut R.
  Proof.
    elim_tree A R b => /=.
    - case: t => //= _ [<-]//.
    - move=> /orP[].
        move=> cA.
        case: ifP => sA.
          case X: prune => // [A'|].
            by move=> [<-]/=; rewrite cA.
          by case nA: prune => //=[A'][<-]/=; rewrite (HA _ _ _ nA).
        case: ifP => //= fA.
          by case nA: prune => //[A'][<-]/=; rewrite (HA _ _ _ nA).
        by move=> [<-]/=; rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= sA.
        case X: prune => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: prune => //[A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and  cB0 orbT.
      case: ifP=> fA.
        case X: prune => //= [A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and cB0 orbT.
      by move=> [<-]/=; rewrite cB0 cB orbT.
  Qed.

  Lemma prune_no_alt b A A' : prune b A  = Some A' -> success A = b -> nilA A = false.
  Proof. by rewrite /nilA=> + -> => ->. Qed.

  (*SNIPT: det_tree_prune *)
  Lemma det_tree_prune:
    forall p A B b, det_tree p A -> prune b A = Some B -> det_tree p B.
  (*ENDSNIPT: det_tree_prune *)
  Proof.
    move=> sP A R b; elim_tree A R b => /=.
    - by case: b => // _ [<-].
    - by move=> _ [<-]//.
    - move=>/andP[fA].
      case nA: prune => [A'|].
        move=> + [<-]/=;rewrite (HA _ _ _ nA)//=.
        case: ifP => //= cA.
          rewrite (has_cut_prune _ nA)//.
        by move=> /eqP?; subst; rewrite if_same.
      case nB: prune => //=[B']+[<-]/=.
      case: ifP => [|_ /eqP] => ?; subst => // H.
      by rewrite (HB _ _ _ nB).
    - by case nB: prune => //=[B']H[<-]/=; apply: (HB B' b).
    - move=> /andP[dB +].
      case sA: (success A).
        case nB: prune => [B'|] => [+ [<-/=]|].
          rewrite (HB B' b)//=.
          case cB: (has_cut B); first by rewrite (has_cut_prune cB nB).
          case cB': (has_cut B') => //.
          by case n: nilA => //=; rewrite orbF => /andP[-> //].
        case nA: prune => [A'|] //= + [<-{R}/=].
        rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
        rewrite/nilA andbb=> /andP[+ ->]/=.
        case: eqP => pA//=.
        by case/orP=> [/HA/(_ nA)->//|/andP[? ->]] => //=; rewrite orbT.
      case fA : (failed A) => [|] => [|+ [<-/=]]; last by rewrite dB.
      case nA: prune => [A'|] => [+ [<-/=]|//].
      rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
      rewrite andbb=> /andP[+ ->]/=.
      case n: nilA => //=.
      by move=> /orP[/HA/(_ nA)->//|/andP[_ ->]]; rewrite orbT.
  Qed.

  Lemma det_check_big_or_help s r0 rs:
    all (fun x => check_atoms s x.2) (r0 :: rs) ->
    all_but_last (fun x  => has_cut_seq x.2) (r0 :: rs) ->
    det_tree s (big_or r0.2 rs).
  Proof.
    move=> /= => /andP[].
    elim: rs r0 => [|x xs IH] r0/= H; rewrite?push/=det_tree_big_and cut_followed_by_det_nfa_and//.
    move=> /andP[c1 c2]/andP[cu1 +]/=.
    rewrite has_cut_seq_has_cut_big_and cu1.
    by apply: IH.
  Qed.
End check.
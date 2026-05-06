From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl fresh sig_lattice compat_sig.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Definition sigV := {fmap V -> S}.

Definition is_sigV (x : sigV) := unit.
Lemma is_sigV_inhab : forall x, is_sigV x. Proof. exact (fun x => tt). Qed.
Definition sigV_eqb (x y : sigV) := x == y.
Lemma sigV_eqb_correct : forall x, eqb_correct_on sigV_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigV_eqb_refl : forall x, eqb_refl_on sigV_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigV is_sigV is_sigV_inhab sigV_eqb sigV_eqb_correct sigV_eqb_refl.
HB.instance Definition _ : hasDecEq sigV := Equality.copy sigV _.


Definition odflt1 {T} (ab : T * bool) x := 
  match x with (Some x, b1) => (x,b1) | (None,_) => ab end.

Definition flex_head T := if get_tm_hd T is inr (inr _) then true else false.

(* takes a tm and a signature and updates variable signatures
    updates are performed only on variables in input positions *)
(* Invariant: length s = length t *)
Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : seq Tm) (s : seq mode) (t: seq S): sigV :=
  match s, t, tm with
  | _, _, [::] | [::], _, _ | _, [::], _ => sV
  | output :: ms, _  :: tys, _ :: ts => assume_tm sP sV ts ms tys
  | input  :: ms, ty :: tys, t :: ts =>
    let sV := match t with
    | Tm_V v =>
      match sV.[? v] with
      | None => sV.[v <- ty]
      | Some oldv =>
        if compat_type oldv ty then add v (min ty oldv) sV else sV
      end
    | _ => sV end in  (*TODO: complete this pattern*)
    assume_tm sP sV ts ms tys
  end.

(* returns the signature of the term and if it is well called *)
Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm)  : S * bool :=
  match tm with
  | Tm_D k => (b Exp, true)
  | Tm_P k => odflt1 (b(d Pred),false) (lookup k sP, true)
  | Tm_V v =>  odflt1 (b(d Pred),false) (lookup v sV, true)
  | Tm_App l r => 
      (* before we check the LHS and then we go right *)
      let (sl, b1) := check_tm sP sV l  in
      (* if the type of l is not an arrow, we return anyT *)
      if sl is arr m tl tr then
        if m == input then
          let (cr, br) := check_tm sP sV r in
          if incl cr tl && b1 && br then (tr, true)
          else (weak tr, false)
        else (tr, b1)
      else (b(d Pred),false)
  end.

(* Definition subst2sig sP (s: Sigma) :=
  let x := [fmap x: domf s => check_tm sP empty s.[valP x]] in
  fmap_filter. *)


(* returns the determinacy of the term t *)
Definition call_is_det sP sV t :=
  check_tm sP sV t == (b (d Func), true).

Definition check_atom sP sV (a: Atom) :=
  match a with
  | cut => true
  | call t => call_is_det sP sV t
  end. 

(* There is cut and after the cut there are only call to Det preds *)
Fixpoint check_atoms (sP :sigT) sV (s: seq Atom) :=
  match s with
  | [::] => true
  | cut :: xs => all (check_atom sP sV) xs || check_atoms sP sV xs
  | call c :: xs => (call_is_det sP sV c || has_cut_seq xs) && check_atoms sP sV xs
  end.

Module check_atoms1.
  Fixpoint check_atoms1 sP sV s d :=
  match s with
  | [::] => d
  | cut :: xs => check_atoms1 sP sV xs Func
  | call t :: xs => 
    check_atoms1 sP sV xs (maxD d (if call_is_det sP sV t then Func else Pred))
  end.

  Lemma xx sP sV xs:
    check_atoms1 sP sV xs Func = Pred ->
      all (check_atom sP sV) xs = false.
  Proof.
    elim: xs => //= x xs IH; case: x => //= t.
    case: call_is_det => //.
  Qed.

  Lemma yy sP sV xs: has_cut_seq xs = false ->
    check_atoms1 sP sV xs Pred = Pred.
  Proof.
    elim: xs => //= x xs IH; case: x => //.
  Qed.

  Lemma zz sP sV xs:
    has_cut_seq xs = true ->
    check_atoms1 sP sV xs Func = check_atoms1 sP sV xs Pred.
  Proof.
    elim: xs => //= x xs IH; case: x => //= t /IH.
    case: ifP => //.
  Qed.

  Goal forall sP sV s, check_atoms sP sV s = (check_atoms1 sP sV s Func == Func).
  Proof.
    move=> sP sV s.
    elim: s => //= -[|t] xs IH//=; rewrite IH.
      case C: check_atoms1; rewrite (orbT,orbF)//= xx//.
    case: call_is_det => //=.
    case C: has_cut_seq.
      by rewrite zz.
    rewrite yy//.
  Qed.
End check_atoms1.

  
Definition check_rule (sP:sigT) head prems :=
  match get_tm_hd head with
  | inl pred =>
    if sP.[? pred] is Some sig then
      let md := flatten_mode sig in
      let tys := flatten_sig sig in
      let args := flatten_term head in
      let sV := assume_tm sP empty args md tys in
      (tm_is_det sP head == false) || 
        (check_atoms sP sV prems)
    else true
  | _ => true
  end.

Definition check_rules p :=
  all (fun x => check_rule p.(sig) x.(head) x.(premises)) p.(rules).

Module Test.
  Definition p := b (d Pred).
  Definition f := b (d Func).
  Definition e := b Exp.
  Notation V1 := (IV 0).
  Notation V2 := (IV 1).
  Notation F := (IV 2).
  
  Definition mkP sym sig r := {| sig := [fmap].[sym <- sig]; rules := [::r] |}.

  Module Once.
    Notation onceSym := (IP 1).
    Definition onceI   := mkR (Tm_App (Tm_P onceSym) (Tm_V V1)) [::call (Tm_V V1); cut].
    Definition onceSig := arr input p f.

    Goal check_rules (mkP onceSym onceSig onceI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite [get_tm_hd _]/=.
      cbn match.
      rewrite in_fnd; first by rewrite !in_fsetE eqxx.
      move=> H.
      rewrite/tm_is_det [get_tm_hd _]/=.
      cbn match.
      rewrite !FmapE.fmapE orFb.
      by case: eqP => //=; rewrite not_fnd//= /call_is_det /check_tm !FmapE.fmapE/=.
    Qed.
  End Once.
  
  Module Do.
    Notation doSym := (IP 2).
    Definition doI   := mkR (Tm_App (Tm_P doSym) (Tm_V V1)) [::call (Tm_V V1)].
    Definition doSig := arr input f f.

    Goal check_rules (mkP doSym doSig doI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite [get_tm_hd _]/=.
      cbn match.
      rewrite in_fnd; first by rewrite !in_fsetE eqxx.
      move=> H.
      rewrite/tm_is_det [get_tm_hd _]/=.
      cbn match.
      rewrite !FmapE.fmapE not_fnd//.
      rewrite [flatten_term _]/= [flatten_mode _]/= [flatten_sig _]/=.
      case:eqP => // _.
      rewrite orFb.
      rewrite [flatten_mode _]/= [flatten_sig _]/=.
      rewrite/assume_tm not_fnd//.
      rewrite/check_atoms /tm_is_det.
      rewrite/call_is_det /check_tm.
      by rewrite FmapE.fmapE/=.
    Qed.
  End Do.
  
  (* apply F X :- F X. *)
  Module Apply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e f) (arr input e f).

    Goal check_rules (mkP applySym applySig applyI).
    Proof.
      rewrite/check_rules/= andbT/check_rule.
      rewrite [get_tm_hd _]/=.
      cbn match.
      rewrite !FmapE.fmapE eqxx .
      rewrite [flatten_term _]/= [flatten_mode _]/= [flatten_sig _]/=.
      rewrite/tm_is_det/get_tm_hd FmapE.fmapE.
      rewrite orFb.
      (* assume head *)
      rewrite/assume_tm (@not_fnd _ _ _ (IV 2))//.
      rewrite !FmapE.fmapE not_fnd//=.
      (* check body, with F: exp -> func, and V1: e *)
      by rewrite/call_is_det /check_tm !FmapE.fmapE eqxx.
    Qed.
  End Apply.
  
  (* apply F X :- F X. *)
  Module WrongApply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e p) (arr input e f).

    Goal ~~ check_rules (mkP applySym applySig applyI).
    Proof.
      rewrite/check_rules/= andbT/check_rule.
      rewrite [get_tm_hd _]/=.
      cbn match.
      rewrite !FmapE.fmapE eqxx .
      rewrite [flatten_term _]/= [flatten_mode _]/= [flatten_sig _]/=.
      rewrite/tm_is_det/get_tm_hd FmapE.fmapE.
      rewrite orFb.
      (* assume head *)
      rewrite/assume_tm (@not_fnd _ _ _ (IV 2))//.
      rewrite !FmapE.fmapE not_fnd//=.
      (* check body, with F: exp -> pred, and V1: e *)
      by rewrite/call_is_det /check_tm !FmapE.fmapE eqxx.
    Qed.
  End WrongApply.
End Test.  


Lemma is_det_rename sP fv hd m:
  tm_is_det sP (rename fv hd m).2 =
    tm_is_det sP hd.
Proof.
  rewrite/rename!push/=.
  move: (fresh_tm _ _ _) => -[]/= _.
  elim: hd => //= v b; rewrite ren_V//.
Qed.

Lemma is_det_deref sig fv c :
  tm_is_det sig c ->
  tm_is_det sig (deref fv c).
Proof. by elim: c => //. Qed.


Lemma tm_is_det_comb sP f a:
  tm_is_det sP (Tm_App f a) = tm_is_det sP f.
Proof. by rewrite/tm_is_det/=. Qed.

Lemma fresh_has_cut sv xs m:
  has_cut_seq (fresh_atoms sv xs m).2 = has_cut_seq xs.
Proof. by elim: xs sv => //= -[|c] xs IH sv; rewrite!push//=IH !push//. Qed.

(* TODO: in the second I should use a sV which is related to sV and fv *)
Lemma call_is_det_rename sP sV t fv m:
  call_is_det sP sV (rename fv t m).2 = call_is_det sP sV t.
Proof. Admitted.

Lemma check_atom_fresh sP sV x fv m:
  check_atom sP sV (fresh_atom fv x m).2 = check_atom sP sV x.
Proof. destruct x; rewrite //= !push/= call_is_det_rename//. Qed.

Lemma all_check_atom_fresh sP sV xs sv m:
  all (check_atom sP sV) (fresh_atoms sv xs m).2 = all (check_atom sP sV) xs.
Proof. by elim: xs sv => //=x xs IH sv; rewrite !push/= IH check_atom_fresh. Qed.

Lemma check_atoms_fresh sP sV fv bo m:
  check_atoms sP sV (fresh_atoms fv bo m).2 = check_atoms sP sV bo.
Proof.
  elim: bo fv => //= x xs IH fv.
  rewrite !push/= IH all_check_atom_fresh.
  case: x => //= t.
  rewrite !push/= has_cut_seq_fresh call_is_det_rename//.
Qed.

Section check.
  Variable u : Unif.
  Notation runT := (runT u).
  Definition runT' p v s t r := (exists v' b', runT p v s t r v' b').

  Fixpoint has_cut A :=
    match A with
    | TA cut => true
    | TA (call _) => false
    | KO => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut_seq B0 && has_cut B)
    | Or _ _ _ => false
    end.


  Fixpoint det_tree_seq sP sV L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP sV x || has_cut_seq xs) && det_tree_seq sP sV xs
    end.

  Definition nilA A := prune (success A) A == None.

  Definition det_to_bool d := match d with Func => true | _ => false end.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is det if A' and B are deterministic
    "((A, A') ; B) , !, C" is det if C is deterministic, because any alt from first conjunct dies
    "((A, A') ; KO) , C" is det
    "(A ; B)" for any A and B is not det since nothing prevents the execution of B if A fails
  *)
  Fixpoint det_tree (sP:sigT) sV A :=
    match A with
    | TA a => check_atom sP sV a
    | KO | OK => true
    | And A B0 B =>
        det_tree sP sV B && 
        if nilA A
        then det_tree sP sV A || has_cut B
        else
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          (det_tree sP sV A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq sP sV B0 (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree sP sV B
    | Or (Some A) _ B =>
        det_tree sP sV A && 
        if has_cut A then det_tree sP sV B 
        else (B == KO) 
    end.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim_tree A => /=.
    rewrite fun_if/=.
    case:ifP => // sA.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[->/HB->]; rewrite orbT//.
  Qed.

  Lemma has_cut_big_and x xs:
    has_cut (big_andA x xs) = has_cut_seq (x::xs).
  Proof. by elim: xs x => //=[|x xs ->][]//=; rewrite andbb. Qed.

  Lemma has_cut_seq_has_cut_big_and l:
    has_cut (big_and l) = has_cut_seq l.
  Proof. by case: l => >//; rewrite /=has_cut_big_and//. Qed.

  Lemma det_tree_big_and sP sV L:
    det_tree sP sV (big_and L) = det_tree_seq sP sV L.
  Proof.
    case: L => //= + L.
    elim: L => [|x xs IH][|c]//=; rewrite ?(orbF,andbT)//=IH;
    rewrite (andbb,has_cut_big_and)//=andbb.
    by case: check_atom; case: det_tree_seq; case: has_cut_seq; rewrite//=andbF.
  Qed.

  Lemma cut_followed_by_det_nfa_and sP sV bo :
    check_atoms sP sV bo -> det_tree_seq sP sV bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      by elim: l {IH} => //= x xs IH /andP[->]/IH->.
    by move=> /andP[->]/=.
  Qed.

  Lemma no_alt_cutl A: success A -> nilA (cutl A).
  Proof. by rewrite /nilA success_cut => ->; rewrite prune_cutl. Qed.

  Lemma det_tree_cutl {sP sV A}: success A -> det_tree sP sV (cutl A).
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

  Lemma check_rulesP p c fv s1 sV:
    check_rules p ->
    call_is_det p.(sig) sV c ->
  (* TODO: should link sV with x.1 *)
    all (fun x => check_atoms p.(sig) sV x.2) (bc u p fv c s1).2.
  Proof.
    case: p => [rs s].
    rewrite/bc/=/check_rules/= => CR TD.
    (* rewrite (is_det_cder _ TD). *)
    case: ifP => // _.
    case DR: get_tm_hd => //=[p].
    case: fndP => //= pP.
    rewrite !push/=.
    (* move: (flatten_mode _). *)
    elim: rs s s1 fv c CR TD p DR pP => //= -[hd bo] xs IH sig s fv c/=.
    move=> /andP[c1 c2] TD p C pP.
    have {}IH := IH _ _ _ _ c2 TD _ C pP.
    rewrite !push/= head_fresh_rule/=.
    rewrite eq_sym callable_rename1.
    case:eqP => //= /esym tH.
    case H: H => //=[s'].
    rewrite !push/= IH andbT.
    rewrite premises_fresh_rule/=.
    rewrite check_atoms_fresh.
    move=> {xs c2 IH H}.
    move: c1; rewrite/check_rule -tH in_fnd.
    case: eqP => /=.
      admit. (*should proove that TD + C -> tm_isdet sig hd = true*)
    move=> Hx.
    admit.
  Admitted.

  Lemma deref_empty t:
    deref empty t = t.
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

  Goal forall sP sV s, det_tree sP sV (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma det_check_prune_succ {sP sV A} : 
    det_tree sP sV A -> success A -> prune true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite -{1}[det_tree sP sV A]andbT -fun_if => /andP[? _].
      by rewrite HA.
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

  Lemma det_check_prune {sP sV A R b}:
    det_tree sP sV A -> prune b A = Some R -> det_tree sP sV R.
  Proof.
    elim_tree A R b => /=.
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
          case cB': (has_cut B'); rewrite /= orbC //= ?orbT.
          by rewrite -{1}[det_tree sP sV A]andbT -fun_if => /andP[-> //].
        case nA: prune => [A'|] //= + [<-/=].
        rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
        rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
        by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
      case fA : (failed A) => [|] => [|+ [<-/=]]; last by rewrite dB.
      case nA: prune => [A'|] => [+ [<-/=]|//].
      rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
      rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
      by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
  Qed.

  (*SNIP: check_program *)
  Definition check_program pr := mut_excl u pr && check_rules pr.
  (*ENDSNIP: check_program *)

  Lemma det_check_big_or_help s sV r0 rs:
    all (fun x => check_atoms s sV x.2) (r0 :: rs) ->
    all_but_last (fun x  => has_cut_seq x.2) (r0 :: rs) ->
    det_tree s sV (big_or r0.2 rs).
  Proof.
    move=> /= => /andP[].
    elim: rs r0 => [|x xs IH] r0/= H; rewrite?push/=det_tree_big_and cut_followed_by_det_nfa_and//.
    move=> /andP[c1 c2]/andP[cu1 +]/=.
    rewrite has_cut_seq_has_cut_big_and cu1.
    by apply: IH.
  Qed.
  
  (* TODO: fixme *)
  Lemma det_check_big_or pr c fv fv' sV r0 rs s1:
    check_program pr -> call_is_det (sig pr) sV c -> 
    bc u pr fv c s1 = (fv', r0 :: rs) ->
    det_tree (sig pr) sV (big_or r0.2 rs).
  Proof.
    rewrite /bc/check_program.
    case: pr => rules s/= => /andP[].
    case: ifP => ///negbFE AS.
    case X: get_tm_hd => //=[p].
    case: fndP => //= kP.
    move=> ++ H.
    (* have [q'[qp' [+ H2]]] := is_det_der s1 H. *)
    (* rewrite X => -[?]; subst. *)
    move=> ME CR.
    have := check_rulesP fv s1 CR H.
    have := @mut_exclP _ _ fv ((deref s1 c)) s1 ME.
    rewrite/bc X/= in_fnd.
    rewrite !push/= AS/= => ++ [?]; subst.
    (* move=> H1 H2. *)
    (* apply/det_check_big_or_help => //=. *)
    
    (* rewrite (bool_irrelevance kP qp') => ++ S. *)
    (* rewrite S. *)
    (* rewrite AS/=. *)
    (* by apply/det_check_big_or_help. *)
  Admitted.

  Fixpoint acyclic_sigmaT T :=
    match T with
    | And A _ B => acyclic_sigmaT A && acyclic_sigmaT B
    | Or None sm B => acyclic_sigma sm && acyclic_sigmaT B
    | Or (Some A) sm B => [&& acyclic_sigma sm, acyclic_sigmaT A & acyclic_sigmaT B]
    | TA _ | OK | KO => true
    end.

  Lemma acyclic_sigma_next_subst s A:
    acyclic_sigma s -> acyclic_sigmaT A ->
    acyclic_sigma (next_subst s A).
  Proof.
    elim_tree A s => As/=; rewrite rew_pa.
      by move=> /and3P[]; auto.
      by move=> /andP[]; auto.
    move=> /andP[AA AB]; case: ifP; auto.
  Qed.

  Lemma det_check_step pr fv s1 A r sV: 
    check_program pr -> det_tree pr.(sig) sV A -> 
      step u pr fv s1 A = r ->
        det_tree pr.(sig) sV r.2.
  Proof.
    move=> H + <-; clear r.
    elim_tree A s1.
    - case: t => [|c]//=; rewrite !push/=.
      case bc: bc => //=[fv'[|[s0 r0]rs]]//= H1.
      by apply: det_check_big_or bc.
    - rewrite/= => /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - by rewrite /=!push/=; apply/HB.
    - move=> /=/andP[dB].
      rewrite step_and/=.
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      rewrite (fun_if (det_tree (sig pr) sV)).
      case SA: success.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb; first by case/orP=> [->//|/step_keep_cut->]; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /nilA /sA failed_step//= SA.
      case pA: (incomplete A).
        rewrite/nilA incomplete_prune_id//= => /andP[+ ->]/=.
        by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
      by have:= succF_failF_paF SA fA pA.
  Qed.

  (*SNIPT: is_det *)
  Definition is_det p s v t := 
    forall r, runT' p v s t r -> r = None \/ exists s, r = (Some (s, None)).
  (*ENDSNIPT: is_det *)

  Lemma acyclic_sigmaT_big_and B0: acyclic_sigmaT (big_and B0).
  Proof. rewrite/big_and; case: B0 => //= + l; elim: l => //=. Qed.

  Lemma acyclic_sigmaT_prune b A C:
    acyclic_sigmaT A -> prune b A = Some C -> acyclic_sigmaT C.
  Proof.
    elim_tree A b C => //=.
      by case: ifP => //= _ _ [<-].
      by move=> _ [<-].
      move=> /and3P[As AA AB]; case pA: prune => //=.
        by move=> [<-]//=; apply/and3P; split => //; apply/HA/pA.
      by case pB: prune => //-[<-]/=; apply/andP; split => //; apply/HB/pB.
      move=> /andP[AA AB]; case pA: prune => //=-[<-]/=.
      by apply/andP; split => //; apply/HB/pA.
    move=> /andP[aA aB]; case: ifP => sA.
      case pB: prune.
        by move=> [<-]/=; rewrite aA; apply/HB/pB.
      by case pA: prune => //=-[<-]/=; rewrite acyclic_sigmaT_big_and andbT; apply/HA/pA.
    case: ifP.
      by case pA: prune => //fA [<-]/=; rewrite acyclic_sigmaT_big_and andbT; apply/HA/pA.
    by move=> _ [<-]/=; rewrite aA aB.
  Qed.

  Lemma acyclic_sigma_cut A : acyclic_sigmaT A ->
    acyclic_sigmaT (cutl A).
  Proof.
    elim_tree A => /=.
      by move=> /and3P[->/HA->]//.
      by move=> /andP[->]//.
    by move=> /andP[H1 H2]; case: ifP => //=; rewrite HA//HB.
  Qed.

  Lemma acyclic_sigma_H m t hd s1 s2:
    acyclic_sigma s1 ->
      H u m t hd s1 = Some s2 ->
        acyclic_sigma s2.
  Proof.
    elim: m t hd s1 s2 => /=[|m tl IH] t hd s1 s2.
      by case: t => //=; case: hd => //= + [<-].
    move=> AS; case: t; case: hd => //=.
    move=> f1 a1 f2 a2.
    case H: H => //=[s1'].
    case: m => //=.
      by apply/matching_acyclic/IH/H.
    by apply/unif_acyclic/IH/H.
  Qed.

  Lemma acyclic_sigma_select p pred m t s1 e:
    acyclic_sigma s1 ->
     e \in (select u pred t m p s1).2 ->
        acyclic_sigma e.1.
  Proof.
    elim: p m t s1 e => //=-[hd bo] rs IH m t s1 e AS/=.
    case:eqP => //= [|_/IH -/(_ AS)]// X.
    case H: H => [s2|]; last by apply: IH.
    rewrite !push/= in_cons => /orP[/eqP?|]; subst; last by apply: IH.
    by apply/acyclic_sigma_H/H.
  Qed.

  Lemma acyclic_sigma_bc s1 p v0 t:
    acyclic_sigma s1 ->
      forall x, x \in (bc u p v0 t s1).2 ->
        acyclic_sigma x.1.
  Proof.
    rewrite/bc/= => H1 -[s2 b]/=.
    case: ifP => ///negbFE AS.
    case: get_tm_hd => //= x; case: fndP => //= kP.
    by rewrite !push/=; apply/acyclic_sigma_select.
  Qed.

  Lemma acyclic_big_or r0 rs:
    (forall x, x \in rs -> acyclic_sigma x.1) ->
    acyclic_sigmaT (big_or r0 rs).
  Proof.
    elim: rs r0 => //=; first by move=> *; rewrite acyclic_sigmaT_big_and.
    move=> r rs IH r1 H/=.
    rewrite push/=.
    rewrite acyclic_sigmaT_big_and H//=; last by rewrite in_cons eqxx.
    by apply/IH => x H1; apply/H; rewrite in_cons H1 orbT.
  Qed.

  Lemma acyclic_sigmaT_step p v0 s1 A:
    acyclic_sigma s1 ->
    acyclic_sigmaT A -> acyclic_sigmaT (step u p v0 s1 A).2.
  Proof.
    elim_tree A v0 s1 => /=AS.
      case: t => //=t _.
      rewrite !push/=.
      have /= := @acyclic_sigma_bc s1 p v0 t AS.
      case bc: bc => //=[fv' [|r0 rs]]//=.
      rewrite !push/= => H; rewrite H/=; last by rewrite in_cons eqxx.
      apply/acyclic_big_or => x H1.
      by apply/H; rewrite in_cons H1 orbT.
    - by move=> /and3P[As AA AB]; rewrite !push/= As HA//=; case: ifP => //.
    - by move=> /andP[As AB]; rewrite !push/= As HB//.
    move=> /andP[aA aB]; rewrite !push/=; case: ifP => /= sA.
      rewrite HB//=; last by rewrite acyclic_sigma_next_subst.
      by rewrite andbT; case: ifP; rewrite //=acyclic_sigma_cut.
    rewrite HA//.
  Qed.

  (*SNIPT: det_check_tree *)
  Lemma det_check_tree: 
    forall s v p t fv, check_program p -> det_tree p.(sig) fv t -> is_det p s v t.
  (*ENDSNIPT: det_check_tree *)
  Proof.
    rewrite/is_det.
    move=> s v p t sV H1 H2 r [b[v' R]].
    elim_run R H1 H2; last by apply/IH/det_check_prune/nA.
      by rewrite (det_check_prune_succ H2 sA); eauto.
    apply: IH => //=.
    by apply: det_check_step eA.
  Qed.

  (*SNIPT: det_check_call *)
  Theorem det_check_call:
    forall p s t v fv, 
      check_program p -> call_is_det p.(sig) fv t -> is_det p s v (TA (call t)).
  (*ENDSNIPT: det_check_call *)
  Proof.
    move=> /= p t s v fv cp td r H.
    apply/det_check_tree/H => //=; eauto.
  Qed.

  (*SNIPT: det_check_calls *)
  Theorem det_check_calls:
    forall p t v fv, check_program p -> call_is_det p.(sig) fv t -> is_det p empty v (TA (call t)).
  (*ENDSNIPT: det_check_calls *)
  Proof.
    move=> /= p t v cp fv td r H.
    apply/det_check_tree/H => //; eauto.
  Qed.


  Print Assumptions  det_check_call.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == cut end.
    
    Definition all_tail_cut p := (all tail_cut (rules p)).

    Lemma tail_cut_has_cut r: tail_cut r -> has_cut_seq (premises r).
    Proof. 
      rewrite/tail_cut; case: r => /= _; elim => //= -[|c] xs IH /eqP H//=.
      by case: xs H IH => //= x xs H ->//; rewrite H.
    Qed.

    Lemma all_tail_cut_all_cut p: all_tail_cut p -> all_cut p.
    Proof. by apply/sub_all => x H; apply/tail_cut_has_cut. Qed.

    Lemma last_has_cut a xs:
      last a xs == cut -> cut == a \/ has_cut_seq xs.
    Proof.
      elim: xs => //=; first by move=> /eqP->; left.
      move=> [|c]/= xs IH; auto.
      by case: a IH; auto => c1 IH H; apply: IH; destruct xs.
    Qed.

    Lemma cut_in_prem_tail_cut p: good_modes p.(sig) -> all_tail_cut p -> check_program p.
    Proof.
      move=> GM.
      rewrite/check_program.
      move=> H; apply/andP; split.
        by apply/all_cut_mut_excl/all_tail_cut_all_cut.
      move: H; apply:sub_all => -[hd bo].
      rewrite/tail_cut/=.
      rewrite/check_rule.
      case: get_tm_hd => //= pred.
      case: fndP => //= kp.
      case: tm_is_det => //=.
      elim: bo => //= x xs IH//=.
      destruct xs => //=[/eqP->|/[dup]{}/IH]//=->.
      destruct x; rewrite (orbT,andbT)//.
      by move=> /last_has_cut[]->; rewrite !orbT.
    Qed.
  End tail_cut.
End check.
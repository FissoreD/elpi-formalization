From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run.

(* TODO:
A valid state for substitutions is mandatory?
Given the following program execution
(main X) => (p X, q X) => p X succeeds setting X to func, then
OK, (r X \/ s X) => backchain for q X gives two solutions
Is it important that the substitution in the Or note, X is a function?
*)

Lemma tm2RC_kp {t1 k} : 
  tm2RC t1 = Some (RCallable_Kp k) -> t1 = Tm_Kp k.
Proof.
  case: t1 k => //=.
  - move=> k1 k2 []; congruence.
  - move=> h b k; case X: tm2RC => //.
Qed.

Lemma deref_kp {s1 t k}:
  tm2RC (deref s1 t) = Some (RCallable_Kp k) ->
    (t = Tm_Kp k) \/ (exists v, t = Tm_V v /\ sigma s1 v = Some (Tm_Kp k)).
Proof.
  case: t k => //=.
  - move=> k1 k2 []; left; congruence.
  - move=> v k; case x: sigma => [t1|]//=.
    move=>/tm2RC_kp?; subst.
    right; by eexists.
  - move=> h b k; case X: tm2RC => //.
Qed.

Fixpoint has_cut A :=
  match A with
  | CutS => true
  | CallS _ _ => false
  | Bot | Dead => true
  | OK | Top => false
  | And A B0 B => has_cut A || (has_cut B0 && has_cut B)
  | Or _ _ _ => is_ko A
  end.


Lemma has_cut_cut {B}: has_cut (cutr B).
Proof. 
  elim: B => //=.
  - move=> ?????; rewrite !is_ko_cutr//.
  - by move=> A ->.
Qed.

Lemma has_cut_dead {A}: is_dead A -> has_cut A.
Proof.
  elim: A => //=.
  - move=> A HA s B HB/andP[/is_dead_is_ko->/is_dead_is_ko->]//.
  - move=> A HA B0 _ B HB dA; rewrite HA//.
Qed.
Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
Proof.
  elim: A => //.
    move=> A HA s B HB/=/andP[kA kB]; rewrite fun_if/= is_ko_cutr kA !is_ko_cutl// if_same//.
  move=> A HA B0 HB0 B HB /=/orP[].
    by move=>/HA->.
  move=>/andP[cB0 cB].
  rewrite HB0//HB//orbT//.
Qed.

Lemma expand_has_cut {u A s}: 
  has_cut A -> has_cut (get_state (expand u s A)) \/ is_cutbrothers (expand u s A).
Proof.
  elim: A s; try by move=> /=; auto.
  - move=> A HA s1 B HB s /=/andP[kA kB].
    case: ifP => dA.
      rewrite (is_ko_expand _ kB)/=kA kB; auto.
    rewrite (is_ko_expand _ kA)/=kA kB; auto.
  - move=> A HA B0 _ B HB s /=/orP[].
      move=> /(HA s); case: expand => [s1|s1||s1] C/= []//; auto => cC.
      - by rewrite cC /=; left.
      - by rewrite cC /=; left.
      left; rewrite get_state_And /=.
      by case: ifP; rewrite ?cC // has_cut_cutl.
    case/andP=> cB0 cB.
    case: expand => [s1|s1||s1] C/=; rewrite ?cB ?cB0 ?orbT; auto.
    move: (HB s1 cB).
    by case: expand => [s2|s2||s2] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
Qed.

Lemma has_cut_success {A}:
  has_cut A -> success A = false.
Proof.
  elim: A => //.
  - move=> A HA s B HB /=/andP[kA kB].
    rewrite !is_ko_success// if_same//.
  - move=> A HA B0 HB0 B HB /=/orP[].
      by move=>/HA->.
    by move=>/andP[] _/HB->; rewrite andbF.
Qed.

Lemma success_has_cut {A}:
  success A -> has_cut A = false.
Proof.
  elim: A => //.
  - move=> A HA s B HB/=; case: ifP => dA.
      rewrite is_dead_is_ko//=; apply: success_is_ko.
    move=>/success_is_ko->//.
  - by move=> A HA B0 HB0 B HB/=/andP[]/HA->/HB->; rewrite andbF.
Qed.

Lemma has_cut_next_alt {s A s' B}: 
  has_cut A -> next_alt s A = Some (s', B) -> has_cut B.
Proof.
  elim: A s B s' => //.
  - move=>/=[]?//?? _ [_<-]//.
  - move=> A HA s1 B HB s C s' /=.
    move=>/andP[kA kB].
    by rewrite !is_ko_next_alt//; rewrite !if_same//.
  - move=> A HA B0 HB0 B HB s C s' /=.
    case: ifP => //= dA /orP[].
      move=> cA.
      have:= HA s _ _ cA.
      case: next_alt => // [[s2 D]|].
        move=>/(_ _ _ erefl) cD.
        case: ifP => //= fA.
          case: ifP => //= fB0 [??]; subst.
          by rewrite /= cD.
        case: next_alt => //[[s3 E]|].
          by move=>[??]; subst; rewrite/=cA.
        by case: ifP => fB //=[??]; subst; rewrite /= cD.
      move=> _; case: ifP => //= fA.
      case: next_alt => //= [[s2 D]][??]; subst => /=.
      by rewrite cA.
    move=>/andP[cB0 cB].
    case: ifP => /= fA.
      by case: next_alt => //= [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
    have:= HB s _ _ cB.
    case: next_alt => //= [[s1 D]|].
      by move=> /(_ _ _ erefl) cD [_ <-]/=; rewrite cB0 cD orbT.
    by move=> _; case: next_alt => // [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
Qed.


Section checker.
  Definition sigV := V -> option S.

  Fixpoint get_prop_rightmost sig := (*this is the signature of predicate that should end in prop...*)
    match sig with
    | b (d r) => r
    | b Exp => Func (*TODO: type error*)
    | arr _ _ s => get_prop_rightmost s
    end.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint getS_tm (sP : sigT) (sV : sigV) (tm: Tm) : option S :=
    match tm with
    | Tm_Kd _ => Some (b Exp)
    | Tm_Kp k => Some (sP k)
    | Tm_V v => sV v
    | Tm_Comb h _ => getS_tm sP sV h
    end.

  Definition getS_Callable (sP: sigT) sV (t: Callable) : option S :=
    getS_tm sP sV (Callable2Tm t).

  Definition callable_is_det (sP: sigT) sV (t : Callable) :=
    odflt false (omap is_det_sig (getS_Callable sP sV t)).

  Definition maxD (d1 d2 : D) :=
    match d1, d2 with
    | Pred, _ | _, Pred => Pred
    | Func, Func => Func
    end.

  Definition minD (d1 d2 : D) :=
    match d1, d2 with
    | Func, _ | _, Func => Func
    | Pred, Pred => Pred
    end.

  Fixpoint incl_aux f1 f2 s1 s2 :=
    match s1, s2 with
    | b Exp, b Exp => true
    | b(d D1), b(d D2) => f1 D1 D2 == D1
    | arr i l1 r1, arr i l2 r2 => incl_aux f2 f1 l1 l2 && incl_aux f1 f2 r1 r2
    | arr o l1 r1, arr o l2 r2 => incl_aux f1 f2 l1 l2 && incl_aux f1 f2 r1 r2
    | _, _ => false (*TODO: this is type error*)
    end.

  Fixpoint min_max f1 f2 s1 s2 :=
    match s1, s2 with
    | b Exp, b Exp => b Exp
    | b(d D1), b(d D2) => b(d(f1 D1 D2))
    | arr i l1 r1, arr i l2 r2 => arr i (min_max f2 f1 l1 r1) (min_max f1 f2 r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (min_max f1 f2 l1 r1) (min_max f1 f2 r1 r2)
    | _, _ => b Exp (*TODO: this is type error*)
    end.

  Definition incl := incl_aux minD maxD.
  Definition min := min_max minD maxD.
  Definition max := min_max maxD minD.
  
  Fixpoint strong s :=
    match s with
    | b Exp => b Exp
    | b(d _) => b(d Func)
    | arr i l r => arr i (weak l) (strong r)
    | arr o l r => arr o (strong l) (strong r)
    end
  with weak s :=
    match s with
    | b Exp => b Exp
    | b(d _) => b(d Pred) 
    | arr i l r => arr i (strong l) (weak r)
    | arr o l r => arr o (weak l) (weak r)
    end.

  Section test.
    Definition SMap := 
      (arr i (arr i (b Exp) (arr o (b Exp) (b(d Func)))) (arr i (b Exp) (arr o (b Exp) (b(d Func))))).
    Definition WMap := 
      (arr i (arr i (b Exp) (arr o (b Exp) (b(d Func)))) (arr i (b Exp) (arr o (b Exp) (b(d Pred))))).
    Goal incl SMap WMap && ~~(incl WMap SMap). Proof. move=>//. Qed.
    Goal (weak SMap) == WMap. Proof. move=> //=. Qed.
  End test.

  Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm) : (S * bool) :=
    match tm with
    | Tm_Kd k => (b Exp, true)
    | Tm_Kp k => (sP k, true) 
    | Tm_V v => (odflt (b Exp) (sV v), true) (*TODO: what to return if v is not in sV ??*)
    | Tm_Comb l r => 
      let '(s1, b1) := check_tm sP sV l in
      match s1 with
      | arr i tl tr => 
        let '(s2, b2) := check_tm sP sV r in
        let r := b1 && b2 && incl s2 tl in
        if r then (tr, true)
        else (weak tr, false)
      | arr o tl tr => if b1 then (check_tm sP sV l) else (weak tr, false)
      | _ => (b Exp, false) (*TODO: this is a typechecking error...*)
      end
    end.

  Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : Tm) (s : S): sigV :=
    match tm with
    | Tm_Kd _ | Tm_Kp _ => sV
    | Tm_V v =>
      let t' := sV v in
      fun x => if x == v then Some (odflt s (omap (fun x => min x s) t')) else sV x
    | Tm_Comb l r =>
      match s with
      | arr i tl tr =>
        let sP' := assume_tm sP sV l tl in
        assume_tm sP sP' r tr
      | arr o tl tr => assume_tm sP sV l tl
      | _ => sV (*TODO: this is type error...*)
      end
    end.

  Fixpoint assume_call (sP:sigT) (sV:sigV) (c : Callable) (s : S): sigV :=
    match c with
    | Callable_Kp _ => sV
    | Callable_V v => sV
    | Callable_Comb l r =>
      match s with
      | arr i tl tr => assume_call sP sV l tl
      | arr o tl tr => 
        let sV' := assume_call sP sV l tl in
        assume_tm sP sV' r tr
      | _ => sV (*TODO: this is type error*)
      end
    end.

  Fixpoint assume_hd (sP:sigT) (sV:sigV) (s : S) (tm:Tm) : sigV :=
    match tm with
    | Tm_Kd _ => sV
    | Tm_Kp _ => sV
    | Tm_V v => fun x => if x == v then Some s else sV x
    | Tm_Comb l r => 
      match s with
      | arr i tl tr => assume_hd sP (assume_hd sP sV tl l) tr r
      | arr o tl _ => (assume_hd sP sV tl l)
      | _ => sV (*TODO: wrong type, should be unreachable*)
      end
    end.

  Fixpoint check_hd (sP:sigT) (sV:sigV) (s : S) (tm:Tm) : bool :=
    match tm with
    | Tm_Kd _ => true
    | Tm_Kp k => sP k == s
    | Tm_V v => odflt false (omap (fun x => x == s) (sV v))
    | Tm_Comb l r => 
      match s with
      | arr i tl _ => (check_hd sP sV tl l)
      | arr o tl tr => 
        let '(t, b1) := check_tm sP sV r in 
        (t == s) && b1 && (check_hd sP sV tl l)
      | _ => false (*TODO: wrong type, should be unreachable*)
      end
    end.

  Definition check_callable sP sV (c: Callable) : (D * sigV) :=
    let '(x, b1) := check_tm sP sV (Callable2Tm c) in (*TODO: we hope b1 to be Func or Pred*)
      if b1 then 
        if x is b(d x) then
          if getS_Callable sP sV c is Some s then
            let sV' := assume_call sP sV c s in
            (maxD x (get_prop_rightmost s), sV')
          else (Pred, sV)
        else (Pred, sV) (*TODO: type error*) 
      else (Pred, sV).

  Definition check_atom sP sV (a: A) (s:D) : (D * sigV) :=
    match a with
    | ACut => (Func, sV)
    | ACall t => check_callable sP sV t
    end. 

  Fixpoint check_atoms sP sV l s :=
    match l with
    | [::] => (s, sV)
    | x :: xs => 
      let '(s', sV') := check_atom sP sV x s in
      check_atoms sP sV' xs s'
    end.

  (* all bodies should have a cut followed by checked atoms *)
  (* ACCEPTED: a1 ... an, !, b1 ... bm *)
  (* we want that b1 ... bm is func *)
  (* NOTE: flags about determinacy can be obtained from a1...an *)
  Definition check_atoms_w_cut (sP :sigT) sV (l: seq A) :=
    ((check_atoms sP sV l Func).1 == Func) && (ACut \in l).

  Fixpoint rcallable_is_det (sP: sigT) (t:RCallable) : bool :=
    match t with
    | RCallable_Comb h _ => rcallable_is_det sP h
    | RCallable_Kp k => is_det_sig (sP k)
    end.

  Definition empty_ctx : sigV := fun x => None.
  
  (* The rules passes the check if it is 
     implementating a relation predicate.
     Otherwiser its atoms should pass the check
  *)
  Definition check_rule sP sV head prems :=
    (rcallable_is_det sP head == false) ||
    check_atoms_w_cut sP sV prems.

  Definition check_rules sP sV rules :=
    all (fun x => check_rule sP sV x.(head) x.(premises)) rules.

  Definition check_program sP := 
    forall pr, check_rules sP empty_ctx (rules pr).
End checker.

(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)
Fixpoint det_tree_aux (sP:sigT) (sV : sigV) A dd : D * sigV :=
  match A with
  | CutS => (Func, sV)
  | CallS _ a => check_atom sP sV (ACall a) dd
  | Top | Bot | OK => (dd, sV)
  | Dead => (dd, sV)
  | And A B0 B =>
    if is_ko A then (dd, sV)
    else
      let '(dd', sV') := det_tree_aux sP sV A dd in
      let '(ddB0, sVB0) := det_tree_aux sP sV' B0 dd' in
      let '(ddB, sVB) := det_tree_aux sP sV' B dd' in
      (maxD ddB0 ddB, sV')
  | Or A _ B =>
      let '(sVA, sV') := det_tree_aux sP sV A dd in
      let '(sVB, _) := det_tree_aux sP sV B dd in
      if has_cut A then (maxD sVA sVB, sV) else 
      if (is_ko B) then (sVA, sV')
      else (Pred, sV)
  end.

Definition det_tree sP A := (det_tree_aux sP empty_ctx A Func).1 == Func.

Lemma no_alt_ko {sP A}: is_ko A -> det_tree sP A.
Proof.
  rewrite/det_tree.
  elim: A => //.
  + move=> A HA s B HB /=/andP[kA kB].
    case X: det_tree_aux HA => //=[dA sVA]/(_ kA)/eqP?; subst.
    case Y: det_tree_aux HB => //=[dB sVB]/(_ kB)/eqP?; subst.
    rewrite kB; case: ifP => //.
  + move=> A HA B0 HB0 B HB /= ->//.
Qed.

  Lemma no_alt_cut {sP A}: det_tree sP (cutr A).
Proof. apply: no_alt_ko is_ko_cutr. Qed.


Lemma no_alt_dead {sP A}: is_dead A -> det_tree sP A.
Proof. move=>/is_dead_is_ko. apply: no_alt_ko. Qed.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  (check_atoms sP sV l r).1 = Func -> 
    (det_tree_aux sP sV (big_and p l) r).1 = (Func).
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [dA sVA].
  move=> {}/IH H.
  case: A X => //=.
    move=> [??]; subst => /=.
    case: det_tree_aux H => //=-[]//.
  move=> c.
  rewrite/check_callable.
  case Z: check_tm => [S []]/=; last first.
    move=> [??]; subst.
    case: det_tree_aux H => -[]//.
  case: S Z => //=; last first.
    move=> m s1 s2 Z [??]; subst.
    case: det_tree_aux H => -[]//.
  move=> []//=.
    move=> +[??]; subst.
    case: det_tree_aux H => -[]//.
  move=> d.
  case X: getS_Callable => //=[SS|].
    move=> +[??]; subst.
    case: det_tree_aux H => //=-[]//.
  move=> +[??]; subst.
  case: det_tree_aux H => //=-[]//.
Qed.

Lemma cut_followed_by_det_has_cut {sP sV l} p:
  check_atoms_w_cut sP sV l -> has_cut (big_and p l).
Proof. move=>/andP[] _; elim: l => //=-[]//= x xs IH /IH->//. Qed.

Lemma cut_followed_by_det_nfa_and {sP sV bo} p:
  check_atoms_w_cut sP sV bo -> (det_tree_aux sP sV (big_and p bo) Func).1 = Func.
Proof. move=>/andP[]/eqP/all_det_nfa_big_and//. Qed.

(* Lemma tiki_taka {modes sP sV u s t q hd s2}:
  tm2RC (deref s (Callable2Tm t)) = Some q ->
  H u (modes q) q hd s = Some s2 ->
  getS_Callable sP sV t = Some (b (d Func)) -> rcallable_is_det sP hd.
Proof.
  generalize (modes q) => {}modes/=.
  elim: modes q hd t s s2 => //=.
    move=> []//=k []//= k1 t s1 s2; case: eqP => //=<-.
    move=>/deref_kp [].
      case: t => //= k2[->] _ [->]//.
    move=> [v[]]; case: t => //= v1 [->] H _.
    rewrite /getS_Callable/=.
    admit.
  move=> []//ml IH []//h1 b1 []//=h2 b2 t s1 s2 H1 H2 H3.
    move: H2; case e: H => //=[s1']H2.
    case: t H1 H3 => //=.
      admit.
    move=> c t.
    case H : tm2RC => //=[h1'] [??]; subst => /=H1.
    apply: IH H e H1.
  move: H2; case e: H => //=[s1']H2.
  case: t H1 H3 => //=.
    admit.
  move=> c t.
  case H : tm2RC => //=[h1'] [??]; subst => /=H1.
  apply: IH H e H1.
Admitted.

(* TODO: HERE
  Given a deterministic predicate p,
  Let t, be a valid call to p,
  Given a list of valid rules in a program p, then
  backchaining produces a deterministic tree!
*)
Lemma is_det_det_tree {u sP t s1 sV} {p:program}:
  (* TODO: s1 and sV should be linked somehow *)
  check_rules sP sV p.(rules) -> (check_callable sP sV t).1 = Func -> 
    (det_tree_aux sP sV (big_or u p s1 t) Func).1 = Func.
Proof.
  rewrite/check_callable.
  rewrite /big_or/F.
  case X: tm2RC => //[rc].
  case: p => rules modes sig1 /=.
  generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
  clear -X.
  elim: rules modes s1 t pr rc X => //=.
  move=> [] hd bo rules IH modes s/= t p q X /andP[H1 H1'] H2.
  case H: H => /= [s2|]; last first.
    apply: IH X H1' H2.
  clear IH.
  move: H.
  (* set t' := deref s t. *)
  move: H1 => /orP[]; last first.
    move=> + _.
    elim: rules sV H1' H2 bo => //=.
      move=> sV _ _ bo.
      move=>/(cut_followed_by_det_nfa_and p).
      case: det_tree_aux => //=-[]//.
    move=> [] hd1 bo1/= l IH sV /andP [H3 H4] H2 bo H1.
    case H: H => [s3|]//=; last first.
      by apply: IH.
    rewrite (cut_followed_by_det_has_cut _ H1).
    have:= cut_followed_by_det_nfa_and p H1.
    case Y: det_tree_aux => //=[? sV']?; subst.
    case Z: det_tree_aux => [d sV''].
    move: H2; case W: check_tm => //=[d1 []]//.
    case: d1 W => //=-[]// d1.
    case: d Z => //.
    suffices Hz : (getS_Callable sP sV t = Some (b (lang.d d1))).
      rewrite Hz/=.
      case: d1 Hz => //= Hz Z H5 _.
      move: H3 => /orP[]H3; last first.
        have:= IH sV.
        rewrite H4 H5/= Hz/= => /(_ isT erefl _ H3).
        rewrite Z//.
      admit.
    admit.
  move=> /eqP H3 H4.
  case W: det_tree_aux => [[|]sV1]//.
  move: H2; case C: check_tm => [S []]//.
  case: S C => //=-[]//=d C.
  case Z: getS_Callable => //=[S].
  case: d C => //= C.
  case K: get_prop_rightmost => //=.
  
  case: S Z => //=.
  have:= tiki_taka X H4 .
  have /= := tiki_taka X H2 H4; congruence.

  case r: rules => //=.

  elim: t sV => //=.
  - move=> k sV.
Qed. *)


  (* 
    Given a checked program, and a deterministic tree,
    then calling expand produces a tree which is still deterministic.
  *)
Lemma expand_det_tree {u sP s1 A r} : 
  check_program sP -> det_tree sP A -> 
    expand u s1 A = r ->
      det_tree sP (get_state r).
Proof.
  move=> H + <-; clear r.
  elim: A s1 => //.
  - move=> p t s1 /=.
    rewrite/det_tree.
    move: H.
    rewrite /check_program.
    apply: is_det_det_tree.
    by have:= H p.
  - move=> A HA s B HB s1 /=/andP[fA].
    case: ifP => //= cA.
      move=> nnB.
      case: ifP => //= dA.
        have:= HB s1 nnB.
        case: expand => //= [_|_||_] C nnC/=; rewrite get_state_Or/=fA/=cA?HB//.
      have:= HA s1 fA.
      have := @expand_has_cut _ s1 cA.
      case X: expand => //= -[]// + ->; rewrite ?nnB ?no_alt_cut //=; try by case: has_cut.
      by rewrite cutr2 eqxx if_same.
    move/eqP->.
    case: ifP => [dA|].
      rewrite get_state_Or/=cA no_alt_dead//=is_ko_expand//=?is_ko_cutr//cutr2//.
    have:= HA s1 fA => + dA.
    case Y: expand => /=->; rewrite !cutr2 eqxx no_alt_cut if_same//.
  - move=> A HA B0 HB0 B HB s /=.
    move=>/orP[].
      move=>kA; rewrite is_ko_expand///=kA//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case X: expand => //= [|||s1 C]; try rewrite cB0 cB/= fB0 fB !orbT//.
      rewrite get_state_And.
      rewrite /= (HB s1) //.
      have := @expand_has_cut _ s1 cB.
      case H1: (is_cutbrothers (expand u s1 B)).
        move=>_/=; rewrite has_cut_cutl// det_tree_cutl det_tree_cutl !orbT//.
      move=> []//H2; rewrite H2 fB0 cB0 orbT//.
    have:= HA s fA.
    case X: expand => //= [|||s1 C] H1; try rewrite H1 orbT fB fB0 orbT//.
    have:= HB s1 fB; case Y: expand => //= H2; try rewrite fB0 H2 H1 orbT !orbT//.
    rewrite !det_tree_cutl H2 !orbT//.
Qed.

Lemma expand_next_alt {sP s1 A s2 B} : 
  check_program sP -> det_tree sP A ->
    expand u s1 A = Success s2 B -> forall s3, next_alt s3 B = None.
Proof.
  move=> H.
  elim: A s1 B s2 => //.
  - by move=> /= s1 A s2 _ [_ <-]//.
  - move=> A HA s B HB s1 C s2.
    move=> /=/andP[fA].
    case: (ifP  (is_dead _)) => dA.
      rewrite has_cut_dead// => fB.
      have:= HB s _ _ fB.
      case X: expand => ///(_ _ _ erefl) H1 [??]; subst => /= s3.
      rewrite dA H1//.
    have:= HA s1 _ _ fA.
    case X: expand => // [s4 A'] /(_ _ _ erefl) H1 + [_<-] s3/=.
    rewrite (expand_not_dead _ dA X) H1.
    rewrite success_has_cut ?(expand_solved_same _ X)//.
    move=>/eqP->.
    rewrite is_ko_next_alt?if_same//is_ko_cutr//.
  - move=> A HA B0 _ B HB s1 C s2 /=.
    move=>/orP[].
      move=> kA; rewrite is_ko_expand//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case X: expand => // [s3 D].
      have:= HB s3 _ _ fB.
      have sbF:= has_cut_success cB.
      case Y: expand => ///(_ _ _ erefl) H1 [??] s4;subst.
      have [[]]:= expand_solved_same _ Y; congruence.
    have:= HA s1 _ _ fA.
    case X: expand => //[s3 D]/(_ _ _ erefl) H1.
    have:= HB s3 _ _ fB.
    case Y: expand => ///(_ _ _ erefl) H2 [??];subst => /= s4.
    by rewrite H1 H2; rewrite !if_same.
Qed.

Lemma expandedb_next_alt_done {sP s A s1 B b}: 
  check_program sP -> 
    det_tree sP A -> expandedb u s A (Done s1 B) b ->
      forall s0, next_alt s0 B = None.
Proof.
  remember (Done _ _) as d eqn:Hd => Hz + H.
  elim: H s1 B Hd => //; clear -Hz.
  - {
    move=> s s' A B HA s1 C [_ <-] fA; clear s1 C.
    apply: expand_next_alt Hz fA HA.
  } 
  - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
    apply: IH erefl (expand_det_tree Hz fA HA).
  - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
    apply: IH erefl (expand_det_tree Hz fA HA).
Qed.


Lemma det_tree_next_alt {sP s1 A s2 B}:
  det_tree sP A -> next_alt s1 A = Some (s2, B) -> det_tree sP B.
Proof.
  elim: A s1 B s2 => //.
  - move=> []//??? _ [_<-]//.
  - move=>/=??[]//??? _ [_<-]//.
  - move=> []//??? _ [_<-]//.
  - move=> A HA s B HB s1 C s2 /=.
    move=>/andP[fA].
    case: (ifP (is_dead _)) => dA.
      rewrite has_cut_dead//.
      move=> fB.
      have:= HB (Some s) _ _ fB.
      case X: next_alt => //[[s3 D]] /(_ _ _ erefl) fD[_ <-]/=.
      rewrite no_alt_dead// has_cut_dead// fD.
    case: ifP => cA.
      move=> fB.
      have:= (HA s1 _ _ fA).
      case X: next_alt => //[[s3 D]|].
        have cD:= has_cut_next_alt cA X.
        by move=> /(_ _ _ erefl) fD[_<-]/=; rewrite fD cD fB.
      move=> _.
      case: ifP => dB//.
      have idA := @is_dead_dead A.
        case Y: next_alt => //[[s3 D]].
        move=>[_ <-]/=.
        rewrite no_alt_dead// has_cut_dead//.
        apply: HB fB Y.
    move=>/eqP->; rewrite (is_ko_next_alt is_ko_cutr) if_same.
    have:= HA s1 _ _ fA.
    case: next_alt => // [[s3 D]]/(_ _ _ erefl) fD [_ <-]/=.
    by rewrite fD cutr2 eqxx no_alt_cut if_same.
  - move=> A HA B0 HB0 B HB s1 C s2 /=.
    case: (ifP (is_dead _)) => dA//.
    move=>/orP[].
      move=>kA.
      by rewrite is_ko_failed// is_ko_next_alt//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case: ifP => // fA.
        case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
        by rewrite cB0 fB0 orbT.
      have:= HB s1 _ _ fB.
      case X: next_alt => // [[s3 D]|].
        by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite cB0 (has_cut_next_alt cB X) fD fB0 orbT.
      move=> _; case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
      by rewrite cB0 fB0 orbT.
    case: ifP => // _.
      have:= HA s1 _ _ fA.
      case X: next_alt => // [[s3 D]].
      move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
      by rewrite fD orbT fB0 orbT.
    have:= HB s1 _ _ fB.
    case: next_alt => // [[s3 D]|].
      by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite fA fD fB0 !orbT.
    move=> _.
    have:= HA s1 _ _ fA.
    case X: next_alt => // [[s3 D]].
    move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
    by rewrite fD orbT fB0 orbT.
Qed.

Lemma expand_next_alt_failed {sP A B C s s'}:
  check_program sP ->
    det_tree sP A -> expand u s A = Failure B ->
      forall sN, next_alt sN B = Some (s', C) -> det_tree sP C.
Proof.
  move=> Hz.
  elim: A B C s s' => //.
  - move=> /=????? []<-//.
  - move=> /=????? []<-//.
  - move=> A HA s1 B HB C D s s' /=++sN.
    move=>/andP[fA].
    case: (ifP (is_dead _)) => dA.
      rewrite has_cut_dead// => fB.
      have:= HB _ _ s1 _ fB.
      case: expand => // E /(_ _ _ _ erefl (Some s1)) + [<-]/=.
      rewrite dA.
      case: next_alt => //[[s2 F]] /(_ _ _ erefl) + [_<-]/=.
      by move=> /= ->; rewrite has_cut_dead// no_alt_dead.
    case: ifP => //.
      have := HA _ _ s _ fA _ sN.
      case X: expand => // [E] /(_ _ _ _ erefl) + cA + [?]; subst.
      rewrite /= (expand_not_dead _ dA X).
      have:= @expand_has_cut _ s cA; rewrite X/= => -[]// cE.
      case Y: next_alt => //[[s2 F]|].
        move=> /(_ _ _ erefl) fF fB [_ <-] /=.
        have cF:= has_cut_next_alt cE Y.
        by rewrite fF cF fB.
      move=>_ fB.
      case: ifP => // dB.
      have dDe := @is_dead_dead E.
        case nB : next_alt => //= [[s2 F]] [_<-]/=.
        rewrite no_alt_dead// has_cut_dead// (det_tree_next_alt fB nB)//.
    move=> cA /eqP->.
    have:= HA _ _ s _ fA _ sN.
    case X: expand => // [E] /(_ _ _ _ erefl) + [<-]/=.
    have kcB := @is_ko_cutr B.
    rewrite /= (expand_not_dead _ dA X) (is_ko_next_alt kcB).
    rewrite if_same.
    case Y: next_alt => //[[s2 F]].
    move=> /(_ _ _ erefl) fF [_ <-] /=.
    by rewrite fF no_alt_cut cutr2 eqxx if_same.
  - move=> A HA B0 _ B HB C D s s' /= ++sN.
    move=> /orP[].
      move=> kA; rewrite is_ko_expand// => -[<-]/=.
      rewrite is_ko_failed// is_ko_next_alt// if_same//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case X: expand => //[E|s1 E].
        move=> [<-]/=.
        case: ifP => // dS.
        case: ifP => // fS.
          case nE: next_alt => [[s3 F]|]//.
          by case: ifP => //FB0 [_<-]/=; rewrite cB0 fB0 orbT.
        case Y: next_alt => //[[s3 F]|].
          by move=>[_ <-]/=; rewrite cB0 (has_cut_next_alt cB Y) fB0 (det_tree_next_alt fB Y) orbT.
        by case: next_alt => // [[s3 F]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
      have:= HB _ _ s1 _ fB _ sN.
      case Z: expand => // [F] /(_ _ _ _ erefl) + [<-]/=.
      case: ifP => //dE; case:ifP=>FE.
        move=> _.
        by case: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
      case Y: next_alt => //[[s3 G]|].
        move=>/(_ _ _ erefl) nG.
        have := @expand_has_cut _ s1 cB.
        rewrite Z/==>-[]//cF.
        by move=>[_ <-]/=; rewrite cB0 nG fB0 (has_cut_next_alt cF Y) orbT.
      have [??]:= expand_solved_same _ X; subst => _.
      case W: next_alt => //[[s3 G]]; case: ifP => // _[_<-]/=.
      by rewrite cB0 fB0 orbT.
    have:= HA _ _ s _ fA _ sN.
    case X: expand => //[E|s1 E].
      move=> /(_ _ _ _ erefl) + [<-]/=.
      case: ifP => // dS.
      case: ifP => //fE.
        case: next_alt => //[[s4 G]] /(_ _ _ erefl) fG.
        by case: ifP => // _[_<-]/=; rewrite fB0 fG orbT orbT.
      case Y: (next_alt sN B) => //[[s4 G]|].
        by move=> _ [_<-]/=; rewrite (det_tree_next_alt fB Y) fB0 (expand_det_tree Hz fA X) orbT orbT.
      case: next_alt => //[[s3 G]] /(_ _ _ erefl)fG; case:ifP=>//_[_<-]/=.
      by rewrite fG fB0 orbT orbT.
    move=> _.
    have:= HB _ _ s1 _ fB _ sN.
    case Z: expand => // [F] /(_ _ _ _ erefl) {}HB [<-]/=.
    have /= fE := expand_det_tree Hz fA X.
    case: ifP => //dE; case:ifP=>FE.
      case W: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=.
      by rewrite fB0 (det_tree_next_alt fE W) orbT orbT.
    move: HB.
    case W: next_alt => //[[s3 G]|].
      move=> /(_ _ _ erefl) fG [_<-]/=; rewrite fG fB0 fE orbT orbT//.
    case T: next_alt => //[[s3 G]] => _; case:ifP => //[fB01][_<-]/=.
    by rewrite fB0 (det_tree_next_alt fE T) orbT orbT.
  Qed.

Lemma expandedb_next_alt_failed {sP s A B C s' b1}: 
  check_program sP ->
    det_tree sP A ->
      expandedb u s A (Failed B) b1 -> 
        forall sN, next_alt sN B = Some (s', C) -> det_tree sP C.
Proof.
  remember (Failed _) as f eqn:Hf => Hz + H.
  elim: H B C s' Hf => //; clear -Hz.
  - move=> s A B HA ? C s' [<-] fA nB.
    apply: expand_next_alt_failed Hz fA HA nB.
  - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
    apply: IH erefl (expand_det_tree Hz fA HA) _ nB.
  - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
    apply: IH erefl (expand_det_tree Hz fA HA) _ nB.
Qed.

Definition is_det A := forall s s' B,
  run u s A s' B -> forall s2, next_alt s2 B = None.

Lemma runb_next_alt {sP A}: 
  check_program sP -> 
    det_tree sP A -> is_det A.
Proof.
  rewrite/is_det.
  move=> H1 H2 s s' B []b H3.
  elim: H3 H2; clear -H1 => //.
  - move=> s s' A B C b HA -> fA s2.
    have H := expandedb_next_alt_done H1 fA HA _.
    have sB := expanded_Done_success u HA.
    have//:= next_alt_clean_success sB (H s2).
  - move=> s s' r A B C D b1 b2 b3 HA HB HC IH ? fA s2; subst.
    apply: IH.
    apply: expandedb_next_alt_failed H1 fA HA _ HB.
Qed.

Lemma main {sP p t}:
  check_program sP -> callable_is_det sP t -> 
    is_det ((CallS p t)).
Proof.
  move=> H1 fA HA.
  apply: runb_next_alt H1 _ HA.
  apply: fA.
Qed.

Print Assumptions  main.

Section tail_cut.

  Definition tail_cut (r : R) :=
  match r.(premises) with [::] => false | x :: xs => last x xs == ACut end.
  
  Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

  Lemma cut_in_prem_tail_cut sP: AllTailCut -> check_program sP.
  Proof.
    rewrite /AllTailCut /check_program.
    rewrite /tail_cut /check_rules.
    move=> + pr => /(_ pr).
    remember (rules pr) as RS.
    apply: sub_all => r; clear.
    rewrite /check_rule.
    case X: rcallable_is_det => //=.
    case: r X => //= hd []//= + l.
    elim: l => //=.
    move=> x xs IH []//=; last first.
      move=> _; apply IH.
    by move=> H1 H2; rewrite IH//orbT.
  Qed.

  Lemma tail_cut_is_det sP p t:
    AllTailCut -> callable_is_det sP t -> is_det ((CallS p t)).
  Proof.
    move=> /(cut_in_prem_tail_cut sP).
    apply main.
  Qed.
End tail_cut.

Print Assumptions tail_cut_is_det.

End check.

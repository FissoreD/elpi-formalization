From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl fresh sig_lattice sig_compat.
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

Definition cincl s1 s2 := compat_type s1 s2 && incl s1 s2.

Lemma cincl_trans : transitive cincl.
Proof. by move=> x y z /andP[C1 I1] /andP[C2 I2]; rewrite /cincl (incl_trans I1 I2) (compat_type_trans C1 C2). Qed.

Lemma cincl_refl: reflexive cincl.
Proof. by rewrite /cincl/reflexive => x; rewrite compat_type_refl incl_refl. Qed.

Lemma cincl_arr m a b a' b':
  cincl (arr m a b) (arr m a' b') =
    (if m == input then cincl a' a else cincl a a') && cincl b b'.
Proof.
  rewrite/cincl/= incl_arr.
  case: m => //=; rewrite -!andbA//; f_equal.
    by apply: compat_type_comm.
    by case: compat_type => //; rewrite andbF.
  by case: compat_type => //=; rewrite andbF.
Qed.

Lemma size_fs_fm a : size (flatten_sig a) = size (flatten_mode a).
Proof. by elim: a => //= _ _ _ ? ->. Qed.

Lemma cincl_is_det_sig a b: cincl a b ->  is_det_sig b ->  is_det_sig a.
Proof.
  elim: a b => //=[|m f Hf a Ha]//=.
    by move=> [|[]]//=[[|[]]|[]]//=.
  case: m => -[|[]]//f' a'; rewrite cincl_arr/= => /andP[] _ /Ha; auto.
Qed.

(* takes a tm and a signature and updates variable signatures
    updates are performed only on variables in input positions *)
(* Invariant: length s = length t *)
Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : seq Tm) (s : seq mode) (t: seq S): sigV :=
  match s, t, tm with
  | _, _, [::] | [::], _, _ | _, [::], _ => sV
  | output :: ms, _  :: tys, _ :: ts => sV
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

Lemma assume_tm_all_out sP sV hs ms ss:
  all_out ms -> assume_tm sP sV hs ms ss = sV.
Proof. by case: hs => //=; case: ms => //=[|[]]//=; case: ss. Qed.

Definition get_sig (sP:sigT) (sV:sigV) t :=
  match t with
  | Tm_V v => sV.[? v]
  | Tm_P p => sP.[? p]
  | Tm_D _ => Some (b Exp)
  | Tm_App _ _ => None
  end.

Definition to_tm (X: P + (D + V)) :=
  match X with
  | inl P => Tm_P P
  | inr (inl D) => Tm_D D
  | inr (inr V) => Tm_V V
  end.

(* tells if the list of terms have the right signatures wrt modes *)
Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : seq Tm) (s : seq mode) (t: seq S) :=
  match s, t, tm with
  | [::], [::], [::] => true
  | output :: ms, _  :: tys, _ :: ts => true
  | input  :: ms, ty :: tys, t :: ts =>
    (* TODO: instead == Some ty, could use my_sub in case of prop *)
    (if get_sig sP sV t is Some ty' then cincl ty' ty else false) && check_tm sP sV ts ms tys
  | _, _, _ => false
  end.

Definition check_tmM sP sV t :=
  if get_sig sP sV (to_tm (get_tm_hd t)) is Some s then
    let m := flatten_mode s in
    let ty := flatten_sig s in
    let ag := flatten_term t in
    check_tm sP sV ag m ty && is_det_sig s
  else false.

(* returns the determinacy of the term t *)
Definition call_is_det sP sV t := check_tmM sP sV t.

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
      rewrite !FmapE.fmapE//=.
      rewrite/tm_is_det /get_tm_hd FmapE.fmapE/=.
      by rewrite not_fnd//= andbT orbT.
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
      rewrite FmapE.fmapE/= not_fnd//= andbT orbF.
      by rewrite/call_is_det/=/check_tmM /get_sig/to_tm/get_tm_hd FmapE.fmapE/= orbT.
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
      rewrite !FmapE.fmapE eqxx.
      rewrite/tm_is_det/get_tm_hd FmapE.fmapE orFb.
      rewrite/check_atoms andbT orbF.
      rewrite/call_is_det/check_tmM.
      rewrite/get_sig/get_tm_hd/to_tm.
      rewrite [flatten_term _]/= [flatten_mode _]/= [flatten_sig _]/=.
      rewrite/assume_tm (@not_fnd _ _ empty F)//.
      rewrite  FmapE.fmapE (@not_fnd _ _ empty)//.
      rewrite !FmapE.fmapE/=.
      by rewrite FmapE.fmapE/=.
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
      rewrite andbT orbF.
      rewrite/call_is_det/check_tmM /to_tm/get_tm_hd/get_sig.
      by rewrite !FmapE.fmapE/= FmapE.fmapE//.
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


(* Definition sPsV (s : Sigma) (sT: sigT) (sV: sigV) :=
  [forall k : domf sV, 
    match s.[?val k] with
    | Some v => 
        let: (s, g) := check_tm sT sV v in
        g && compat_type s sV.[valP k] && incl s sV.[valP k]
    | _ => false
    end
  ].

Lemma sPsV_sub s sT sV: sPsV s sT sV -> (domf sV `<=` domf s).
Proof. by move=> H; apply/fsubsetP => x xv; have:= forallP H [`xv]; case: fndP => //. Qed.

Lemma sPsV_in pr s v sV (vv : v \in domf sV): sPsV s pr sV ->
  exists (vs : v \in s), 
    let: (s, g) := check_tm pr sV s.[vs] in
        [/\g, compat_type s sV.[vv] & incl s sV.[vv]].
Proof.
  move=> H; have Hs := sPsV_sub H.
  have vs:= fsubsetP Hs _ vv; exists vs; have:= forallP H [`vv].
  rewrite in_fnd//= valPE; case: check_tm => ??/andP[/andP[]]//.
Qed.

Lemma check_tm_deref s pr sV c r r2:
  check_tm pr sV c = (r, true) ->
  sPsV s pr sV -> check_tm pr sV (deref s c) = r2 ->
  [/\ r2.2, compat_type r2.1 r & incl r2.1 r].
Proof.
  move=> + H1 <-{r2}.
  elim: c r => [p|d|v|f Hf a Ha]/= r.
    by case: fndP => //pp[<-]{r}//=.
    by move=> [<-]//=.
    case: fndP => //vv[<-]{r}.
    by have [vs] := sPsV_in vv H1; rewrite !push in_fnd.
  case C1: check_tm => [[|[] l' r'] b']//=; last first.
    move=> [??]; subst.
    have [] := Hf _ C1.
    case: check_tm => sx []//= _.
    by case: sx => [[]|[]]//= ??/andP[]; rewrite incl_arr//= => ++ /andP[].
  rewrite !push/= -!andbA.
  case: (boolP (andb _ _)) => //=/and3P[H3 ? H4]; destruct b' => //=-[?]; subst.
  move: H4; case C2: check_tm H3 => [sk []]//= H3 _.
  have {Hf}[] := Hf _ C1.
  case: check_tm => sx []//= _.
  case: sx => [[]|[]]//= s1 s2 /andP[C3 C4]; rewrite incl_arr//= => /andP[I1 I2].
  have {Ha} [] := Ha _ C2.
  case : check_tm => //= sz []//= _; rewrite !andbT/= => C5 I5.
  by rewrite (incl_trans I5 (incl_trans H3 I1))//.
Qed.

Lemma check_tmD sT sV t s: domf sV # vars t ->
  check_tm sT sV t = (s, true) -> is_det_sig s ->
    exists p, exists2 hs : p \in sT, get_tm_hd t = inl p & is_det_sig sT.[hs].
Proof.
  elim: t s => //[p|v|d|f Hf a Ha]/= s.
    by move=> _; case: fndP => //ps[H]; exists p, ps => //; rewrite H.
    by move=> _ [<-].
    by rewrite fdisjointX1 => vv; rewrite not_fnd//.
  rewrite fdisjointXU => /andP[D1 D2].
  case C: check_tm => [[|[] l r] b]//=.
    rewrite !push/= -andbA; case: (boolP (andb _ _)) => //=.
    move=> -/and3P[H1 H2 H3][?]ds; subst; destruct b => //.
    by apply: Hf C _.
  move=> [<-{s}?] dr; subst.
  by apply: Hf C _.
Qed.

Lemma call_is_det_deref pr c (sV:sigV) (s:Sigma):
  sPsV s pr sV -> call_is_det pr sV c -> call_is_det pr sV (deref s c).
Proof.
  rewrite/call_is_det/tm_is_det => Hx /eqP H1.
  case ch: (check_tm pr sV (deref s c)) => [s' b'].
  have/= [? C I] := check_tm_deref H1 Hx ch; destruct b' => //.
  case: s' C I ch => [[|[]]|[]]//= _ _ ch.
Qed.

Lemma call_is_det_s pr c (sV:sigV) (s:Sigma): acyclic_sigma s ->
  sPsV s pr sV -> call_is_det pr sV c -> tm_is_det pr (deref s c).
Proof.
  rewrite/call_is_det/tm_is_det => A Hx /eqP H1.
  case ch: (check_tm pr sV (deref s c)) => [s' b'].
  have/= [? C I] := check_tm_deref H1 Hx ch; destruct b' => //.
  case: s' C I ch => [[|[]]|[]]//= _ _ ch.
  have [|p[pp -> dh]] := check_tmD _ ch isT; last by rewrite in_fnd.
  apply/fdisjointWl/acyclic_deref_disjoint/A/sPsV_sub/Hx.
Qed.

Lemma call_is_det_tm0_aux c p pr sV s:
  get_tm_hd c = inl p ->
  check_tm pr sV c = (s, true) -> is_det_sig s ->
  exists (pP: p \in pr), is_det_sig pr.[pP].
Proof.
  elim: c p s => //=[p|f Hf a Ha] p0 s.
    move=> [<-{p0}].
    case X: (pr.[?p]) => //[s'][?]; subst.
    by move: X => /fndSomeP[pP<-{s}] H; eexists pP.
  move=> H; case C: check_tm => [[|[] l r] b]//=; last first.
    by move=> [<-{s}?]; subst => Hx; apply: Hf C _ => //=.
  case C1: check_tm => [s' b']//=.
  case: (boolP (andb _ _)) => //=/andP[/andP[]]; destruct b, b' => // I _ _ [<-{s}] Hx.
  by apply: Hf C _.
Qed.

Lemma call_is_det_tm0 pr c (sV:sigV) p:
  get_tm_hd c = inl p -> call_is_det pr sV c -> tm_is_det pr c.
Proof.
  rewrite/call_is_det/tm_is_det => /[dup] + -> /eqP.
  move=> H1 H2.
  have [pP H] := call_is_det_tm0_aux H1 H2 isT.
  by rewrite in_fnd.
Qed. *)

Section check.
  (* Variable u : Unif. *)
  Notation u := mut_excl.u.
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

  (* Lemma check_tmFW s sV t sig:
    check_tm s sV t = (sig, false) -> sig = weak sig.
  Proof.
    elim: t sig => //=[p|v|f Hf a Ha] sig.
      by case: fndP => //ps [<-].
      by case: fndP => //vv [<-].
    case C: check_tm => [[d|m l r] b]; first by move=> [<-].
    case: m C => //=; last first.
      by move=> H [??]; subst; have [] := Hf _ H.
    move=> H; case C1: check_tm => [s' b'].
    by case: ifP => //= Hx [<-]; rewrite weak2.
  Qed. *)

  (* Definition filter_in K (f : domf sV -> bool) (s : {fmap V -> option K}) : {fmap V -> option K} :=
    filterf s (fun x => match sum_bool ) *)

  Definition filter_opt K (s : {fmap V -> option K}) : {fmap V -> option K} :=
    filterf s (fun x => match s.[?x] with Some r => r | _ => false end).

  (* Definition translate (sT:sigT) (sV: sigV) (s:Sigma) :=
    [fmap x : domf s => let r := (check_tm sT sV s.[valP x]) in if r.2 then Some r.1 else None]. *)

  Definition keep_some K (s:{fmap V -> option K}) dft : {fmap V -> K} := [fmap x: domf s =>
      match s.[valP x] with
      | None => dft
      | Some x => x
      end].

  (* Definition translatem sT sV s :sigV :=
    let res := filter_opt (translate sT sV s) in
    keep_some res (b Exp). *)
  Lemma compat_type_flattem_mode t1 t2: compat_type t1 t2 -> flatten_mode t1 = flatten_mode t2.
  Proof. by elim: t1 t2 => [[[]|d []]|[] f Hf a Ha [|[] f' a']]//= /andP[/Hf ? /Ha]; congruence. Qed.

  Lemma clincl_fm t1 t2: cincl t1 t2 -> flatten_mode t1 = flatten_mode t2.
  Proof. by move=> /andP[/compat_type_flattem_mode]. Qed.

  Definition mpV (o n: sigV) :=
    [forall x : domf o, 
      match n.[? val x] with
      | Some s => cincl s o.[valP x]
      | _ => false  
      end
    ].

  Fixpoint cond_inp T (ms :seq mode) (f : T -> bool) (l : list T) :=
    match ms with
    | [::] | (output :: _) => true
    | input :: ms => 
      match l with
      | [::] => true
      | x :: xs => f x && cond_inp ms f xs
      end
    end.

  Fixpoint cond_inp2 T Q (ms :seq mode) (f : T -> Q -> bool) (l1 : list T) (l2 : list Q) :=
    match ms with
    | [::] | (output :: _) => true
    | input :: ms => 
      match l1, l2 with
      | [::], _ | _, [::] => true
      | x :: xs, y::ys => f x y && cond_inp2 ms f xs ys
      end
    end.

  Lemma cond_inp2_refl T l (f: T -> T -> bool) s: reflexive f -> cond_inp2 l f s s.
  Proof. by elim: l s => //= -[]//=ms IH []//=x xs /[dup]/IH->->. Qed.

  Lemma check_tm_mp sP v0 v1 t m s1 s2:
    cond_inp2 m cincl s1 s2 -> size s1 = size s2 ->
    mpV v0 v1 -> check_tm sP v0 t m s1 -> check_tm sP v1 t m s2.
  Proof.
    move=> ++ H; elim: m t s1 s2 => //=.
      by move=> [|??]//=[]//[]//.
    move=> [] ms IH t [|s ss]//[|s1 ss1]//=; case: t => //=.
    move=> t l /andP[CI H1] [S]/andP[H2 H3].
    rewrite (IH _ _ _ H1)//= andbT.
    move: H2; rewrite /get_sig; case: t => //=[p|d|v].
      by case: fndP => //=pP H4; apply: cincl_trans H4 _.
      by case: s CI => //= -[]//=.
    case: fndP => //= vv0 CI'.
    have:= forallP H [`vv0]; case: fndP => //= vv1.
    rewrite valPE/= => Hx; apply: cincl_trans Hx _.
    by apply: cincl_trans CI' _.
  Qed.

  Lemma cond_inp2_cincl a b:
    cincl b a -> cond_inp2 (flatten_mode a) cincl (flatten_sig a) (flatten_sig b).
  Proof.
    elim: a b => //=-[]//f Hf a Ha [|[]f' a']//.
    by rewrite cincl_arr/= => /andP[->/Ha->].
  Qed.

  Lemma call_is_det_mp s a b t: mpV a b -> call_is_det s a t -> call_is_det s b t.
  Proof.
    rewrite/call_is_det => H.
    rewrite/check_tmM/get_sig.
    case X: get_tm_hd => [p|[d|v]]/= => [|/andP[]|]//.
      case: fndP => //= ps /andP[H1 ->]; rewrite andbT.
      apply: check_tm_mp H1 => //.
      apply : cond_inp2_refl cincl_refl.
    case: fndP => // va /andP[H1 H2].
    have:= forallP H [`va]; rewrite valPE/=; case: fndP => //vb cba.
    rewrite (clincl_fm cba).
    apply/andP; split.
      apply: check_tm_mp H1 => //.
      by apply: cond_inp2_cincl.
      by rewrite !size_fs_fm (clincl_fm cba).
    by apply: cincl_is_det_sig H2.
  Qed.

  Lemma check_atom_mp s a b t:
    mpV a b -> check_atom s a t -> check_atom s b t.
  Proof. by case: t => //=t; apply: call_is_det_mp. Qed.
  
  Lemma check_atoms_mp s a b t:
    mpV a b -> check_atoms s a t -> check_atoms s b t.
  Proof.
    move=> H; elim: t => //=[[|c] l IH].
      move=> /orP[|/IH->]; last rewrite orbT//.
      move=> /allP Hx; apply/orP; left; apply/allP => x xP.
      by apply/check_atom_mp/Hx.
    move=> /andP[+/IH->]; rewrite andbT.
    by move=> /orP[/call_is_det_mp|]->//; rewrite orbT.
  Qed.

  (* Lemma check_atom_mp1 froz sV s s' hd bo fv q modes p sig (sg:sigT) (pP : p \in sg): sPsV s' sg sV ->
    incl (sg.[pP]) sig ->
      H u froz (modes) q (flatten_term (head (fresh_rule fv {| head := hd; premises := bo |}).2)) s = Some s' ->
        check_atoms sg (assume_tm sg empty (flatten_term hd) (modes) (flatten_sig sig)) bo ->
        check_atoms sg (translatem sg sV s') (premises (fresh_rule fv {| head := hd; premises := bo |}).2).
  Proof.
  Admitted. *)

  (* Search (_ \in _ `&` _). *)

  (* Definition xxx (s: sigV) (r: {fmap V -> V}) :=
    ([fmap x: domf r =>
      match s.[? r.[valP x]] with
      | None => None
      | Some x => Some x
      end]).

  Definition filterxxx  K (s:{fmap V -> option K}) : {fmap V -> option K} :=
    filterf s (fun x => match s.[? x] with Some x => x | _ => false end).


  Definition fff s r:= keep_some (filterxxx (xxx s r)).
    
  
  (* X ---> func               rename Z = X  *)
  (* quindi nel mapping ho Z -> X *)
  (* vorrei Z ------> X *)
  Lemma check_atoms_rename sv f sg bo m:
    check_atoms sg (fff sv (fresh_atoms f bo m).1.2 (b Exp)) bo -> 
    check_atoms sg sv (fresh_atoms f bo m).2.
  Proof.
    elim: bo f sv => [|x xs IH]//=f sv; rewrite !push/=.
    case: x => [|t]/=.
      move=> /orP[] H1; last rewrite IH// orbT//.
      admit.
    rewrite !push/= => /andP[H1 H2].
    rewrite IH//=.
      admit.
    apply: check_atoms_mp H2.
    apply/forallP => [[x xP]]; rewrite valPE[val _]/=.
    rewrite in_fnd.
      rewrite /fff/keep_some/filterxxx/= . *)

  (* Lemma check_selectS s q rs (sg:sigT) sV p (pP : p \in domf sg):
    all (fun x => check_rule sg (head x) (premises x)) rs ->
    sPsV s sg sV -> acyclic_sigma s -> call_is_det sg sV q -> get_tm_hd q = inl p ->
    all (fun x => check_atoms sg (translatem sg sV x.1) x.2)
      (select u p (flatten_term q) (flatten_mode sg.[pP]) rs s).2.
  Proof.
    elim: rs s q sg sV p pP => [|[hd bo] rs IH]//=.
    move=> s q sg sV p pP /andP[Hh Hr] ss As dq hq.
    rewrite eq_sym.
    case: eqP => //= IP; last by apply: IH.
    case H: H => [s'|]; last by apply: IH.
    rewrite !push/=; apply/andP; split; last by apply: IH.
    move: Hh; rewrite/check_rule.
    rewrite IP in_fnd.
    have:= call_is_det_tm0 hq dq.
    rewrite/tm_is_det IP hq in_fnd => ->/= {IH Hr}.
    apply: check_atoms_mp.
    apply/forallP => [[x xP]]; rewrite valPE [val _]/=.
    have xt : x \in domf (translatem sg sV s').
      admit.
    rewrite in_fnd ffunE valPE.
  Admitted. *)


  (* Lemma check_select v s q rs (sg:sigT) sV p (pP : p \in domf sg):
    vars_sigma s `<=` v -> vars q `<=` v ->
    all (fun x => check_rule sg (head x) (premises x)) rs ->
    sPsV s sg sV -> acyclic_sigma s -> call_is_det sg sV q -> get_tm_hd q = inl p ->
    all (fun x => check_atoms sg (translatem sg sV x.1) x.2)
      (select u p (flatten_term q) (flatten_mode sg.[pP]) (fresh_rules v rs).2 s).2.
  Proof.
    elim: rs v s q sg sV p pP => [|[hd bo] rs IH]//= v.
    move=> s q sg sV p pP S1 S2 /andP[Hh Hr] ss As dq hq.
    rewrite !push/=.
    set fr := fresh_rules _ _.
    rewrite {1}head_fresh_rule/= eq_sym.
    rewrite callable_rename1.
    case: eqP => //= IP; last by apply: IH.
    set f := fresh_rule _ _.
    case H: H => [s'|]; last by apply: IH.
    rewrite !push/=; apply/andP; split; last by apply: IH.
    move: Hh; rewrite/check_rule.
    rewrite IP in_fnd.
    have:= call_is_det_tm0 hq dq.
    rewrite/tm_is_det IP hq in_fnd => ->/= {IH Hr}.
    (* move: H; rewrite/f. *)
    (* rewrite premises_fresh_rule/=. *)
    set A := assume_tm _ _ _ _ _.
    move=> H1.
    rewrite premises_fresh_rule/=; set X := fresh_atoms _ _ _.
    apply: check_atoms_mp.
    set Y := X.1.2.
    have:= @check_atom_mp _ Y.
    apply: @check_atoms_mp Y _ _ _ _.
      set X := fresh_atoms _ _ _.
      Unshelve.
        apply: X.1.
      apply/forallP => [[x xP]]; rewrite valPE.
      rewrite premises_fresh_rule/=.
    move=> /check_atoms_mp.
    apply: check_atom_mp1 (pP) _ _ => //.
  Qed. *)
  
  (* Lemma check_rulesP p c fv s sV:
    check_rules p -> sPsV s (sig p) sV ->
    call_is_det p.(sig) sV (deref s c) ->
    all (fun x => check_atoms p.(sig) (translatem (sig p) sV x.1) x.2) (bc u p fv c s).2.
  Proof.
    case: p => [rs sg].
    rewrite/bc/=/check_rules/= => cr ss.
    case (boolP (acyclic_sigma s)) => //=As dc.
    case DR: get_tm_hd => //=[p].
    case: fndP => //= pP.
    rewrite !push/=.
    apply: check_select pP _ _ cr ss As dc DR.
      by rewrite -fsetUA fsubsetUl.
    by rewrite fsubsetU// fsubsetUr.
  Qed. *)

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

  Lemma det_check_big_or_help sT sV r0 rs: 
    all (fun x => check_atoms sT sV x.2) (r0 :: rs) ->
    all_but_last (fun x  => has_cut_seq x.2) (r0 :: rs) ->
    det_tree sT sV (big_or r0.2 rs).
  Proof.
    move=> /= /andP[].
    elim: rs r0 => [|x xs IH] r0/= c1; rewrite?push/=det_tree_big_and.
      rewrite cut_followed_by_det_nfa_and//.
    move=> /andP[h1 h2] /andP[cu1 +]/=.
    rewrite has_cut_seq_has_cut_big_and cu1 cut_followed_by_det_nfa_and//.
    by apply: IH.
  Qed.

  Definition deref_atom s a :=
    match a with
    | cut => cut
    | call t => call (deref s t)
    end.

  Definition deref_pair p := map (deref_atom p.1) p.2.

  Definition big_or_det sP rs :=
    all_but_last (fun x => has_cut_seq x.2) rs && all (fun x => check_atoms sP fmap0 (deref_pair x)) rs.
  
  Lemma all_but_last_map T f g l:
    @all_but_last T f (map g l) = @all_but_last T (fun x => f (g x)) l.
  Proof. by elim: l => //= x0 [|x1 xs]//= ->//. Qed.

  Lemma call_is_det_tm_is_det pr t: call_is_det pr fmap0 t -> tm_is_det pr t.
  Proof.
    rewrite/tm_is_det/call_is_det/check_tmM/=.
    case H: get_tm_hd => //=[p|[d|v]]/=; last first.
      by rewrite not_fnd//.
      by rewrite andbF.
    by case: fndP => //= ppr /andP[].
  Qed.

  Lemma flatten_term_ren_map s t:
    flatten_term (ren s t) = map (ren s) (flatten_term t).
  Proof. by elim: t => //=[f Hf a Ha]; rewrite map_rcons Hf//. Qed.

  Lemma flatten_term0_ren s t: size (flatten_term (ren s t)) = size (flatten_term t).
  Proof. by rewrite flatten_term_ren_map size_map. Qed.

  Lemma flatten_term0_rename v t m:
    size (flatten_term (rename v t m).2) = size (flatten_term t).
  Proof. by rewrite/rename !push/= flatten_term0_ren. Qed.

  Lemma get_tm_hd_ren s t:
    match get_tm_hd (ren s t) with
    | inl p => get_tm_hd t = inl p
    | inr (inl dt) => get_tm_hd t = inr (inl dt)
    | inr (inr v) =>
      exists2 x, get_tm_hd t = inr (inr x) & (s.[? x] = Some v \/ (x = v))
    end.
  Proof.
    elim: t => //= v; eexists; auto.
    by case: (fndP s v); auto.
  Qed.

  Lemma check_tm_ren0 sP s t modes sig: 
    check_tm sP empty (map (ren s) t) modes sig =
      check_tm sP empty t modes sig.
  Proof.
    elim: t modes sig => //=t0 ts IH [|[] ms]//= [//|x xs].
    rewrite IH; rewrite/get_sig; case: t0 => //= v.
    by rewrite !(@not_fnd _ _ fmap0)//.
  Qed.

  Lemma call_is_det_tm_ren0 sP s t: call_is_det sP empty (ren s t) = call_is_det sP empty t.
  Proof.
    rewrite/call_is_det/check_tmM.
    have := get_tm_hd_ren s t.
    case X: get_tm_hd => [p|[d|v]]/=; last first.
      by rewrite not_fnd//= => -[x ->]//= _; rewrite not_fnd.
      by move=> ->//=; rewrite !andbF.
    move=> ->/=; case: fndP => //= pP; case: is_det_sig; rewrite !(andbT,andbF)//.
    by rewrite flatten_term_ren_map check_tm_ren0.
  Qed.

  Lemma call_is_det_tm_rename0 sP v t r: call_is_det sP empty (rename v t r).2 = call_is_det sP empty t.
  Proof. by rewrite/rename !push/= call_is_det_tm_ren0. Qed.

  Lemma check_atom_fresh0 sP v bo r:
    check_atom sP empty (fresh_atom v bo r).2 = check_atom sP empty bo.
  Proof. by case: bo => //=t; rewrite !push/check_atom/= call_is_det_tm_rename0. Qed.

  Lemma check_atom_fresh0_all sP v bo r:
    all (check_atom sP empty) (fresh_atoms v bo r).2 = all (check_atom sP empty) bo.
  Proof. by elim: bo => //= x xs IH; rewrite !push/= check_atom_fresh0 IH. Qed.

  Lemma check_atoms_fresh0 sP v bo r:
    check_atoms sP empty (fresh_atoms v bo r).2 = check_atoms sP empty bo.
  Proof.
    elim: bo => //=-[|t] xs IH; rewrite !push/= check_atom_fresh0_all IH//.
    by rewrite /rename !push/= fresh_has_cut call_is_det_tm_ren0.
  Qed.

  Lemma check_atoms_fresh sP hd bo modes v s (r : {fmap V -> V}):
    check_atoms sP (assume_tm sP empty (map (ren r) hd) modes s) (fresh_atoms v bo r).2 =
      check_atoms sP (assume_tm sP empty hd modes s) bo.
  Proof.
    elim: hd modes s bo => //=[|h hs IH] m s bo.
      set X := match m with | [::] | _ => _ end.
      replace X with (@fmap0 V S).
        by rewrite check_atoms_fresh0.
      by rewrite{}/X; case: m => [|[]]; case: s => //.
    set X:= (match s with | [::] | _ => @fmap0 V S end).
    replace X with (@fmap0 V S); last by destruct s.
    clear X; case: m => //=; first by rewrite check_atoms_fresh0.
    move=> [] ms; last first.
      by rewrite check_atoms_fresh0.
    case: s => [|s sx]; first by rewrite check_atoms_fresh0.
    case: h => //v'; rewrite ren_V !(@not_fnd _ _ fmap0)//.
    case: fndP => v'r/=.
  Admitted.

  Lemma check_atoms_fresh_rename sP hd bo modes v s:
    check_atoms sP (assume_tm sP empty (flatten_term hd) modes s) bo ->
      check_atoms sP (assume_tm sP empty (flatten_term (rename v hd empty).2) modes s) 
        (fresh_atoms (rename v hd empty).1.1 bo (rename v hd empty).1.2).2.
  Proof.
    rewrite/rename !push/=; move: (_ `|` _) => fv.
    rewrite flatten_term_ren_map.
    by rewrite check_atoms_fresh.
  Qed.

  Lemma det_check_H sP modes q hd sig bo s s' froz:
    good_mode modes ->
    check_tm sP empty q modes sig ->
    check_atoms sP (assume_tm sP empty hd modes sig) bo ->
    H u froz modes q hd s = Some s' -> check_atoms sP empty [seq deref_atom s' i  | i <- bo].
  Proof.
    elim: hd modes sig bo s s' q => //=[|h hs IH] modes sig bo s s' q.
      set X:= (match modes with | [::] | _ => _ end).
      replace X with (@fmap0 V S); last by rewrite{}/X; case: modes => [|[] ms]; case: sig.
      clear X; case: modes; case: q => //=; case: sig => //= _ _ c [<-].
      admit.
    case: modes => //=; case: q => //=q0 qs m ms.
    case: m => //=; case: sig => //=[sx ss]; last first.
      move=> AO _ C; case U: unif.unify => //=[s''].
      admit.
  Admitted.

  Lemma det_check_bc pr c fv r s:
    check_program pr -> call_is_det pr.(sig) fmap0 (deref s c) -> 
    bc u pr fv c s = r ->
    big_or_det pr.(sig) r.2.
  Proof.
    rewrite/big_or_det => /andP[ME CR] CT <-{r}.
    rewrite mut_exclP//={ME}; last first.
      by apply: call_is_det_tm_is_det.
    rewrite/bc; set QUERY := deref s c in CT *.
    case AS: acyclic_sigma => //=.
    case TH: get_tm_hd => [p|]//=.
    case: fndP => //= ppr.
    rewrite !push/=.
    case: pr CR CT ppr => /= rs sig; rewrite/check_rules/= => CR CD ppr.
    move: CD; rewrite/call_is_det/check_tmM TH/= in_fnd.
    move=> /andP[].
    elim: rs CR => //= -[hd bo] rs IH /= /andP[H1 H2] H3 H4.
    rewrite !push/=.
    case: ifP => //= Hh; first by apply: IH.
    rewrite !head_fresh_rule/=.
    set FR := fresh_rules _ _ in IH *.
    set R := rename FR.1 _ _.
    case H: H => [s'|]; last by apply: IH.
    rewrite !push/= IH// andbT.
    rewrite/deref_pair/=/fresh_rule!push/= -/R.
    move: Hh; rewrite head_fresh_rule/= -/FR-/R eq_sym => /eqP Hh {IH}.
    have: vars QUERY `<=` FR.1.
      by apply/fsubset_trans/fresh_rules_sub; rewrite fsubsetU//fsubsetUr.
    move: FR @R H Hh => [v /= _] H Hh S {rs H2}.
    move: (get_frozen_vars _ _) H => /= froz.
    move: H1; rewrite/check_rule.
    have {}Hh := (proj1 (callable_rename _ _ _ _) Hh).
    rewrite Hh in_fnd /tm_is_det Hh in_fnd H4/=.
    move: H3.
    set modes := flatten_mode _.
    set sigF := flatten_sig _.
    move=> + /(check_atoms_fresh_rename v).
    set RT := rename _ _ _.
    set FA := fresh_atoms _ _ _.
    set Q := flatten_term _.
    set H := flatten_term _.
    apply: det_check_H.
  Admitted.


  
  Lemma det_check_big_or sV pr c fv fv' r0 rs s1:
    sPsV s1 (sig pr) sV ->
    check_program pr -> call_is_det pr.(sig) sV (deref s1 c) -> 
    bc u pr fv c s1 = (fv', r0 :: rs) ->
    det_tree pr.(sig) sV (big_or r0.2 rs).
  Proof.
    move=> ss /andP[ME CR] T B.
    apply/det_check_big_or_help => /=; last first.
      have:= mut_exclP fv ME _ => /(_ c s1); rewrite B/= => ->//.
      move: B; rewrite/bc; case: ifP => // As.
      case h: get_tm_hd => //[p] _.
      by apply: call_is_det_tm0 h T.
    Search bc.
    have: r0.1 \in pr.
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
    sPsV s1 (sig pr) sV ->
    check_program pr -> det_tree pr.(sig) sV A -> 
      step u pr fv s1 A = r ->
        det_tree pr.(sig) sV r.2.
  Proof.
    move=> + H + <-; clear r.
    elim_tree A s1 => ss.
    - case: t => [|c]//=; rewrite !push/=.
      case bc: bc => //=[fv'[|[s0 r0]rs]]//= H1.
      apply: det_check_big_or bc => //.
      by apply: call_is_det_deref.
    - rewrite/= => /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - rewrite/= !push/=.
      apply: HB => //=.
      admit.
    (* by rewrite /=!push/=; apply/HB. *)
    - move=> /=/andP[dB].
      rewrite step_and/=.
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      rewrite (fun_if (det_tree (sig pr) sV)).
      case SA: success => /=.
        have X' : sPsV (next_subst s1 A) pr sV by admit.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb.
          by case/orP=> [->//|/step_keep_cut->]//=; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /nilA /sA failed_step//= SA.
      case pA: (incomplete A).
        rewrite/nilA incpl_prune//= => /andP[+ ->]/=.
        by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
      by have:= succF_failF_paF SA fA pA.
  Admitted.

  Definition is_det p s v t := 
    forall r, runT' p v s t r -> r = Zero \/ exists s, r = (One s).

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

  Lemma det_check_tree: 
    forall s v p t fv, sPsV s (sig p) fv -> check_program p -> det_tree p.(sig) fv t -> is_det p s v t.
  Proof.
    rewrite/is_det.
    move=> s v p t sV ss H1 H2 r [b[v' R]].
    elim_run R ss H1 H2; last by apply/IH/det_check_prune/nA.
      by eauto.
      by move: NS; rewrite (det_check_prune_succ H2 sA).
    apply: IH => //=.
    apply: det_check_step eA => //.
  Qed.

  Theorem det_check_call:
    forall p s t v fv, sPsV s (sig p) fv ->
      check_program p -> call_is_det p.(sig) fv t -> is_det p s v (TA (call t)).
  Proof.
    move=> /= p t s v fv ss cp td r H.
    apply/det_check_tree/H => //=; eauto.
  Qed.

  Theorem det_check_calls:
    forall p t v, check_program p -> call_is_det p.(sig) fmap0 t -> is_det p empty v (TA (call t)).
  Proof.
    move=> /= p t v cp td r H.
    apply/det_check_tree/H; eauto.
    by apply/forallP => [[]]//.
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
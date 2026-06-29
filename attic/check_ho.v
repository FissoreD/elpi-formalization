From Equations Require Import Equations.
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

Fixpoint flatten_sig m :=
  match m with
  | arr m l r => l :: flatten_sig r
  | b _ => [::]
  end.

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
Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : seq Tm) (s : S): sigV :=
  match s, tm with
  | _, [::] => sV
  | arr output _ _, _ :: _ => sV
  | arr input ty tys, t :: ts =>
    let sV := match t with
    | Tm_V v =>
      match sV.[? v] with
      | None => sV.[v <- ty]
      | Some oldv =>
        if compat_type oldv ty then add v (min ty oldv) sV else sV
      end
    | _ => sV end in  (*TODO: complete this pattern*)
    assume_tm sP sV ts tys
  | b _, _ :: _ => sV (*should be a type error*)
  end.

Lemma assume_tm_all_out sP sV hs ss:
  all_out (flatten_mode ss) -> assume_tm sP sV hs ss = sV.
Proof. case: hs => //=; case: ss => //[[]]//. Qed.

Definition get_sig (sP:sigT) (sV:sigV) t :=
  match get_tm_hd t with
  | inl p => sP.[? p]
  | inr (inl _) => Some (b Exp)
  | inr (inr v) => sV.[? v]
  end.

Lemma get_sig_app s v f a: get_sig s v (Tm_App f a) = get_sig s v f.
Proof. by rewrite/get_sig get_tm_hd_app. Qed.

Lemma get_sig_V sp sv v: get_sig sp sv (Tm_V v) = sv.[?v].
Proof. by []. Qed.

Lemma get_sig_P sp sv p: get_sig sp sv (Tm_P p) = sp.[?p].
Proof. by []. Qed.

Inductive ch := TyErr | DetErr of S | Ok of S.

Definition is_ch (x : ch) := unit.
Lemma is_ch_inhab : forall x, is_ch x. Proof. exact (fun x => tt). Qed.
Definition ch_eqb (x y : ch) := 
  match x, y with
  | TyErr, TyErr => true
  | DetErr t1, DetErr t2 | Ok t1, Ok t2 => t1 == t2
  | _, _ => false
  end.
Lemma ch_eqb_correct : forall x, eqb_correct_on ch_eqb x. Proof.
  by case => //=[|s|s][|s'|s']//=/eqP->. Qed.
Lemma ch_eqb_refl : forall x, eqb_refl_on ch_eqb x. Proof. by case => [|?|?]//=; rewrite/eqb_refl_on//=. Qed.
Elpi derive.eqbOK.register_axiomx ch is_ch is_ch_inhab ch_eqb ch_eqb_correct ch_eqb_refl.
(* HB.instance Definition _ : hasDecEq ch := Equality.copy ch _. *)

(* Compute (TyErr == TyErr). *)

Fixpoint eat_ty n sig :=
  match n with
  | 0 => Some sig
  | n.+1 => match sig with arr _ _ r => eat_ty n r | _ => None end
  end.

Definition apply_ch f (s:option S) :=
  match s with
  | None => TyErr
  | Some x => f x
  end.

Fixpoint size_tm t : nat :=
  match t with
  | Tm_App l r => 1 + size_tm l + size_tm r
  | _ => 1
  end.

Definition size_tms t := foldr addn 0 (map size_tm t).
Definition size_tmsP t1 t2 : Prop := (size_tms t1) < (size_tms t2).

Lemma size_tmsP_cons t ts: size_tmsP ts (t :: ts).
Proof.
  rewrite/size_tmsP/size_tms/=; set X:= foldr _ _ _.
  case: t => //=t1 t2.
  rewrite addnC !addnA.
  do 2 apply: ltn_addr.
  by rewrite addnC.
Qed.

Lemma size_tmsP_ft t: size_tmsP (flatten_term t) [::t].
Proof.
  rewrite/size_tmsP/size_tms/= addn0.
  suffices : forall k, foldr addn k [seq size_tm i  | i <- flatten_term t] < size_tm t + k.
    by move=> /(_ 0); rewrite addn0.
  elim: t => //= f Hf a Ha k.
  rewrite map_rcons foldr_rcons.
  apply: leq_trans (Hf _) _.
  rewrite addnA//.
Qed.

Equations check_tm
  (sP : sigT) (sV : sigV) (tm : seq Tm) (s : S) : ch by wf (size_tms tm) lt :=

(* this takes into account partial application *)
check_tm sP sV [::] s := Ok s;
check_tm sP sV (_ :: ts) (arr output _ tys) := apply_ch Ok (eat_ty (size ts) tys);

check_tm sP sV (t :: ts) (arr input tyf tya) :=
  if tyf == b Exp then check_tm sP sV ts tya
  else
    match get_sig sP sV t with
    | None => TyErr
    | Some tyf' =>
      match check_tm sP sV (flatten_term t) tyf with
      | Ok tyf =>
          if compat_type tyf tyf' then
            if incl tyf tyf' then check_tm sP sV ts tya
            else apply_ch (fun x => DetErr (weak x)) (eat_ty (size ts) tya)
          else TyErr
      | DetErr tyf' =>
          if compat_type tyf tyf' then
            apply_ch (fun x => DetErr (weak x))
                    (eat_ty (size ts) tya)
          else TyErr
      | TyErr => TyErr
      end
    end;

check_tm sP sV (_ :: _) (b _) := TyErr.
Next Obligation. by apply/ltP; apply: size_tmsP_cons. Qed.
Next Obligation.
  apply/ltP/leq_trans; [apply: size_tmsP_ft|].
  by rewrite/size_tms/= addn0 leq_addr.
Qed.
Next Obligation. by apply/ltP; apply: size_tmsP_cons. Qed.

Definition check_tm_simpl := 
  (check_tm_equation_1,check_tm_equation_2,check_tm_equation_3,check_tm_equation_4).

Definition check_tmM sP sV t :=
  if get_sig sP sV t is Some s then check_tm sP sV (flatten_term t) s
  else TyErr.

(* returns the determinacy of the term t *)
Definition call_is_det sP sV t := 
  ch_eqb (check_tmM sP sV t) (Ok (b(d Func))).

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
      let sV := assume_tm sP empty (flatten_term head) sig in
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
      by rewrite/call_is_det/=/check_tmM /get_sig/get_tm_hd FmapE.fmapE/= orbT.
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
      rewrite/get_sig/get_tm_hd.
      rewrite [flatten_term _]/=.
      rewrite/assume_tm (@not_fnd _ _ empty F)//.
      rewrite/applySig/f.
      rewrite  FmapE.fmapE (@not_fnd _ _ empty)//.
      rewrite !FmapE.fmapE/=.
      by [].
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
      rewrite [flatten_term _]/=.
      rewrite/tm_is_det/get_tm_hd FmapE.fmapE.
      rewrite orFb.
      (* assume head *)
      rewrite/assume_tm (@not_fnd _ _ _ (IV 2))//.
      rewrite/applySig/f.
      rewrite !FmapE.fmapE not_fnd//=.
      rewrite andbT orbF.
      rewrite/call_is_det/check_tmM /get_tm_hd/get_sig.
      rewrite/get_tm_hd.
      by rewrite !FmapE.fmapE/=/get_sig/get_tm_hd.
    Qed.
  End WrongApply.

  Module map.
    Local Definition map := IP 0.
    Local Definition cons := ID 0.
    Local Definition nil := ID 1.
    Local Definition one := ID 2.
    Local Definition two := ID 3.
    Local Definition four := ID 5.

    Coercion Tm_P : P >-> Tm. 
    Coercion Tm_D : D >-> Tm. 
    Coercion Tm_V : V >-> Tm. 

    Local Definition prop := b (d Pred).
    Local Definition func := b (d Func).
    Definition exp := b Exp.

    Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
    Definition consS := arr output exp exp.
    Definition nilS := exp.

    Local Definition X := IV 1.
    Local Definition X' := IV 10.
    Local Definition Y := IV 2.
    Local Definition Y' := IV 20.
    Local Definition F := IV 3.

    Local Definition p' := {|
      sig := [fmap].[map <- mapS];
      rules := 
        mkR (Tm_App (Tm_App (Tm_App map F) nil) nil) [::] ::
        mkR (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons X) Y)) (Tm_App (Tm_App cons X') Y') ) 
          [:: call (Tm_App (Tm_App F X) X'); call (Tm_App (Tm_App (Tm_App map F) Y) Y')] :: [::]
    |}.

    Local Lemma gthm : get_tm_hd map = inl map.
    Proof. by []. Qed.

    Local Goal check_rules p'.
    Proof.
      rewrite/check_rules/= andbT; apply/andP; split.
        rewrite/check_rule !get_tm_hd_app gthm FmapE.fmapE eqxx.
        rewrite /tm_is_det !get_tm_hd_app gthm FmapE.fmapE eqxx.
        rewrite orFb.
        rewrite [flatten_term _]/=.
        by rewrite/assume_tm not_fnd//.
      rewrite/check_rule !get_tm_hd_app gthm FmapE.fmapE eqxx.
      rewrite /tm_is_det !get_tm_hd_app gthm FmapE.fmapE eqxx.
      rewrite orFb.
      rewrite [flatten_term _]/=.
      rewrite/assume_tm not_fnd///mapS.
      rewrite/check_atoms !orbF andbT.
      apply/andP; split.
        rewrite/call_is_det/check_tmM !get_sig_app get_sig_V FmapE.fmapE eqxx.
        rewrite !check_tm_simpl//.
      rewrite/call_is_det/check_tmM !get_sig_app get_sig_P FmapE.fmapE eqxx.
      rewrite !check_tm_simpl//=.
      by rewrite get_sig_V FmapE.fmapE/=.
    Qed.
  End map.
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
    elim: L => [|x xs IH]//= A.
      by rewrite orbF//=andbT.
    rewrite has_cut_big_and/= andbb IH.
    case: det_tree_seq; last by rewrite !andbF.
    by rewrite !andbT andbC -andbA andbb.
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

  (* Lemma check_tm_mp sP v0 v1 t m s1 s2:
    cond_inp2 m cincl s1 s2 -> size s1 = size s2 ->
    mpV v0 v1 -> check_tm sP v0 t m s1 -> check_tm sP v1 t m s2.
  Proof.
    move=> ++ H; elim: m t s1 s2 => //=.
      by move=> [|??]//=[]//[]//.
    move=> [] ms IH t [|s ss]//[|s1 ss1]//=; case: t => //=; last first.
      by move=> _ l _ [H1]; case: ifP => //.
    move=> t l /andP[CI H1] [S].
    case: ifP => // + /(IH _ _ _ H1 S).
    
    Unset Printing Coercions.
    rewrite/get_sig; case: t => //=[p|d|v]; .
    /andP[H2 H3]
    rewrite (IH _ _ _ H1)//= andbT.
    move: H2; rewrite /get_sig; case: t => //=[p|d|v].
      by case: fndP => //=pP H4; apply: cincl_trans H4 _.
      by case: s CI => //= -[]//=.
    case: fndP => //= vv0 CI'.
    have:= forallP H [`vv0]; case: fndP => //= vv1.
    rewrite valPE/= => Hx; apply: cincl_trans Hx _.
    by apply: cincl_trans CI' _.
  Qed. *)

  (* Lemma cond_inp2_cincl a b:
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
  Qed. *)

  (* Lemma check_atom_mp s a b t:
    mpV a b -> check_atom s a t -> check_atom s b t.
  Proof. by case: t => //=t; apply: call_is_det_mp. Qed. *)
  
  (* Lemma check_atoms_mp s a b t:
    mpV a b -> check_atoms s a t -> check_atoms s b t.
  Proof.
    move=> H; elim: t => //=[[|c] l IH].
      move=> /orP[|/IH->]; last rewrite orbT//.
      move=> /allP Hx; apply/orP; left; apply/allP => x xP.
      by apply/check_atom_mp/Hx.
    move=> /andP[+/IH->]; rewrite andbT.
    by move=> /orP[/call_is_det_mp|]->//; rewrite orbT.
  Qed. *)

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

  Lemma is_det_sig_eat_ty k ts sa:
    is_det_sig k -> eat_ty ts sa = Some k -> is_det_sig sa.
  Proof.
    elim: ts k sa => [|ts IH] k sa//=; first by move=> +[->].
    by move=> dk; case: sa => //m sf sa; apply: IH.
  Qed.

  Lemma is_det_sig_weak s: is_det_sig (weak s) = false.
  Proof. by elim: s => //=[[]//|[]]//. Qed.

  Lemma is_det_sig_check_tm sP sV q s:
    check_tm sP sV q s = Ok (b (d Func)) -> is_det_sig s.
  Proof.
    pattern sP, sV, q, s, (check_tm sP sV q s).
    apply: check_tm_elim => //; clear.
    - by move=> _ _ _ [->].
    - move=> sP sV t ts tyf tya H1 H2.
      case: eqP => // IE; case S: get_sig => //=[sig].
      case C: check_tm => [|sig'|sig']//.
        by case: ifP => //; case: eat_ty.
      by case: ifP => //CT; case: ifP => //; case eat_ty.
    - move=> _ _ _ ts tyf tya; case E: eat_ty => //=-[?]; subst.
      by apply: is_det_sig_eat_ty E.
  Qed.

  Lemma check_tm_is_det_sig pr t s k:
    is_det_sig k -> check_tm pr empty t s = Ok k ->
      is_det_sig s.
  Proof.
    elim: t s k => [|t ts IH] s k; first by rewrite check_tm_simpl => +[->].
    case: s => [b|[] f a] dk; rewrite check_tm_simpl//=; last first.
      case E: eat_ty => //=[d][?]; subst.
      by apply: is_det_sig_eat_ty E.
    case: eqP => /= _; first by apply: IH.
    case H: get_sig => //[s'].
    case C: check_tm => //[sig|sig].
      by case: ifP => //=; case: eat_ty.
    case: ifP => //CT; case I: incl; last by case: eat_ty.
    by apply: IH.
  Qed.

  Lemma call_is_det_tm_is_det pr t: call_is_det pr fmap0 t -> tm_is_det pr t.
  Proof.
    rewrite/call_is_det/check_tmM/get_sig/tm_is_det.
    case ht: get_tm_hd => [p|[d|v]]/=; last first.
      by rewrite not_fnd.
      by case: flatten_term.
    case: fndP => //pP.
    move=> /ch_eqb_correct.
    by apply: check_tm_is_det_sig.
  Qed.

  Lemma flatten_term_ren_map s t:
    flatten_term (ren s t) = map (ren s) (flatten_term t).
  Proof. by elim: t => //=[f Hf a Ha]; rewrite map_rcons Hf//. Qed.

  Lemma flatten_term_deref_map s t p: get_tm_hd t = inl p ->
    flatten_term (deref s t) = map (deref s) (flatten_term t).
  Proof. by elim: t => //=[f Hf a Ha] H; rewrite map_rcons Hf//. Qed.

  Lemma flatten_term_deref_mapD s t p: get_tm_hd t = inr (inl p) ->
    flatten_term (deref s t) = map (deref s) (flatten_term t).
  Proof. by elim: t => //=[f Hf a Ha] H; rewrite map_rcons Hf//. Qed.


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

  Lemma get_tm_hd_deref s t:
    match get_tm_hd t with
    | inl p => get_tm_hd (deref s t) = inl p
    | inr (inl dt) => get_tm_hd (deref s t) = inr (inl dt)
    | inr (inr v) =>
      get_tm_hd (deref s t) = 
        if s.[?v] is Some t then get_tm_hd t
        else inr (inr v)
    end.
  Proof. by elim: t => //= v; auto; case: (fndP s v). Qed.

  Lemma get_sig_ren0 sP s x: get_sig sP empty (ren s x)  = get_sig sP empty x.
  Proof. by rewrite/get_sig; have:= get_tm_hd_ren s x; case: get_tm_hd => [p|[d|v[v']]]->// _; rewrite !not_fnd. Qed.

  Lemma check_tm_ren0 sP s t sig: 
    check_tm sP empty (map (ren s) t) sig =
      check_tm sP empty t sig.
  Proof.
    (* P sP sV tm s (check_tm sP sV tm s) *)
    have /eqP := @eq_refl _ (@fmap0 V S).
    set X := empty; rewrite {2}/X; move: X => X.
    pattern sP, X, t, sig, (check_tm sP X t sig).
    apply: check_tm_elim; clear => sP sV.
    - by move=> sx ; rewrite check_tm_simpl//.
    - by move=> t0 tl b ->; rewrite check_tm_simpl.
    - move=> t ts tyf tya IH1 IH2 ?; subst => /=.
      rewrite !check_tm_simpl size_map.
      rewrite IH1//; case: eqP => //= IE.
      rewrite get_sig_ren0; case G: get_sig => [sig|]//=.
      by rewrite flatten_term_ren_map IH2//; case C: check_tm => //=.
    by move=> t ts ty tys ->/=; rewrite check_tm_simpl size_map.
  Qed.

  Lemma call_is_det_tm_ren0 sP s t: call_is_det sP empty (ren s t) = call_is_det sP empty t.
  Proof.
    rewrite/call_is_det/check_tmM/get_sig.
    have:= get_tm_hd_ren s t.
    rewrite flatten_term_ren_map.
    case: get_tm_hd => [p|[d|v[v']]]->; last first.
      by move=> _; rewrite !not_fnd.
      by case: flatten_term => //.
    case: fndP => //=pP.
    by rewrite check_tm_ren0.
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

  Definition isOk t := match t with Ok _ => true | _ => false end.
  Coercion isOk : ch >-> bool.

  Definition isOkP t r: t = Ok r -> isOk t.
  Proof. by move=>->. Qed.

  Definition relSS (sP:sigT) (s:Sigma) (sV:sigV) :=
    [forall x : domf sV,
      let sig := sV.[valP x] in
      (* TODO: change check_tmM so that it does not check for deterministic signature of the pred *)
      if s.[? val x] is Some t then 
        match check_tmM sP empty (deref s t) with
        | Ok sig' => cincl sig' sig
        | DetErr sig' =>
          if compat_type sig' sig then sig == weak sig
          else TyErr
        | TyErr => false
        end
      else false].

  Lemma check_atoms_fresh sP hd bo v s (r : {fmap V -> V}):
    (* TODO: instead of empty, I need sV and (compose r sV) *)
    check_atoms sP (assume_tm sP empty (map (ren r) hd) s) (fresh_atoms v bo r).2 =
      check_atoms sP (assume_tm sP empty hd s) bo.
  Proof.
    elim: hd s bo => //=[|h hs IH] s bo.
      set X := match s with | b _ | _ => _ end.
      replace X with (@fmap0 V S).
        by rewrite check_atoms_fresh0.
      by rewrite{}/X; case: s => [|[]].
    case: s => //[b|[] tl tr]; only 1,3: by rewrite check_atoms_fresh0.
    case: h => [p|d|v'|f a]/=; only 1, 2, 4: by rewrite IH.
    rewrite !(@not_fnd _ _ fmap0)//.
    (* TODO: should have a weaker IH *)
  Admitted.

  Lemma check_atoms_fresh_rename sP hd bo v s:
    check_atoms sP (assume_tm sP empty (flatten_term hd) s) bo ->
      check_atoms sP (assume_tm sP empty (flatten_term (rename v hd empty).2) s) 
        (fresh_atoms (rename v hd empty).1.1 bo (rename v hd empty).1.2).2.
  Proof.
    rewrite/rename !push/=; move: (_ `|` _) => fv.
    rewrite flatten_term_ren_map.
    by rewrite check_atoms_fresh.
  Qed.

  Lemma flatten_term_deref t p s: 
    get_tm_hd t = inl p ->
    flatten_term (deref s t) = map (deref s) (flatten_term t).
  Proof. by elim: t p => //=f Hf a Ha p H; rewrite map_rcons (Hf _ H). Qed.

  Lemma has_cut_deref_atom  s xs:
    has_cut_seq xs -> has_cut_seq [seq deref_atom s i  | i <- xs].
  Proof. by elim: xs => //= -[]//. Qed.

  Lemma get_tm_hd_vars t v:
    get_tm_hd t = inr (inr v) ->
      v \in vars t.
  Proof. by elim: t => //=[_[->]|f Hf a Ha /Hf]; rewrite finmap.inE// => ->. Qed.

  Lemma get_sig_deref sP s sV t sig:
    acyclic_sigma s ->
    relSS sP s sV ->
    get_sig sP sV t = Some sig -> 
    exists2 sig', get_sig sP empty (deref s t) = Some sig' & cincl sig' sig.
  Proof.
    rewrite/get_sig.
    move=> A R; elim: t sig => [p|d|v|f Hf a Ha]//=sig.
      by case: fndP => //pP[<-]; eexists => //; apply: cincl_refl.
      by move=> [<-]; eexists; split => //; apply: cincl_refl.
    case: fndP => //vV[<-].
    have:= forallP R [`vV] => /=; rewrite valPE.
    case: fndP => //= vs; rewrite/check_tmM.
    rewrite/get_sig.
    have:= deref2 (Tm_V v) A; rewrite deref_V in_fnd => ->.
    rewrite [get_tm_hd _]/=; case G: get_tm_hd => [p|[d|v']]//; last first.
    - rewrite not_fnd//.
    - case F: flatten_term; rewrite check_tm_simpl => //.
      by simpl in F; case: sV.[vV] => //[[]]// _;eexists => //.
    - case: fndP => //=pP H.
      eexists => //.
      move: H; case C: check_tm => //[sig'|sig'].
        case: ifP => // CT /eqP W; rewrite W.
        admit.
      admit.
  Admitted.

  (* TODO: the premise check_tm sP sV t sig should be
     r = DetErr t | Ok t
     and
     the output should be more_precise then r
  *)
  Lemma check_tm_deref sP sV s t sig:
    acyclic_sigma s ->
    relSS sP s sV ->
    check_tm sP sV t sig -> check_tm sP empty [seq deref s i  | i <- t] sig.
  Proof.
    move=> A.
    pattern sP, sV, t, sig, (check_tm sP sV t sig).
    apply: check_tm_elim => //; clear -A; last first.
      by move=> *; rewrite/= check_tm_simpl size_map//.
    move=> sP sV t ts tyf tya IH1 IH2 R.
    rewrite /=!check_tm_simpl.
    case: eqP => //IE/=; subst; first by auto.
    case G: get_sig => //=[sig].
    have [sig' G' I] := @get_sig_deref sP s sV t sig A R G.
    rewrite G'/=; rewrite size_map.
    case C: check_tm => //[sig''|sig''].
      by case: ifP => //CS; case e: eat_ty.
    have:= IH2 sig R (isOkP C).
  Admitted.

  Lemma call_is_det_deref sP sV s t:
    acyclic_sigma s ->
    relSS sP s sV ->
    call_is_det sP sV t -> call_is_det sP empty (deref s t).
  Proof.
    rewrite/call_is_det/check_tmM => A R /ch_eqb_correct.
    case X: get_sig => //[s']; move: X => G Ch.
    (* have Ch' := check_tm_deref A R (isOkP Ch). *)
    have [sig' G' CI] := get_sig_deref A R G.
    rewrite G'.
    rewrite/ch_eqb.
    (* case C: check_tm => //=. *)
    (* apply: ch_eqb_refl. *)
    move: G G'; rewrite/get_sig.
    have:= get_tm_hd_deref s t.
    case H: get_tm_hd => [p|[d|v]]->//.
      case: fndP => //= pP [?][?]; subst. admit.
      move=> [?][?]; subst. admit.
    case: fndP => //=vV [?]; subst.
    have:= forallP R [`vV]; case: fndP => //=vS; rewrite/check_tmM/get_sig.
    rewrite valPE.
    have:= deref2 (Tm_V v) A; rewrite deref_V in_fnd/= => ->.
    case G': get_tm_hd => //[p|[d|v']]//=; last by rewrite not_fnd.
      case: fndP => //pP + [?]; subst. admit.
    move=> + [?]; subst.
    admit.
  Admitted.

  Lemma check_atoms_deref_all sP sV xs s:
    acyclic_sigma s ->
    relSS sP s sV ->
    all (check_atom sP sV) xs ->
      all (check_atom sP empty) [seq deref_atom s i  | i <- xs].
  Proof. 
    move=> A R; elim: xs => [|[|t] xs IH]//= /andP[+{}/IH->]//; rewrite andbT.
    by apply: call_is_det_deref. 
  Qed.

  Lemma check_atoms_deref sP sV s bo:
    acyclic_sigma s -> relSS sP s sV ->
    check_atoms sP sV bo ->
    check_atoms sP empty [seq deref_atom s i  | i <- bo].
  Proof.
    move=> A R; elim: bo => //= -[|t]//= xs IH.
      by move=> /orP[/check_atoms_deref_all->|/IH->]; rewrite//orbT.
    move=> /andP[+/IH->]//.
    by move=> /orP[/call_is_det_deref->|/has_cut_deref_atom->]//; rewrite orbT.
  Qed.

  Lemma relSS0 sP s: relSS sP s empty.
  Proof. by apply/forallP => //=-[]//. Qed.

  Lemma det_check_H sP q hd sig bo s s' froz sV:
    (* get_frozen_vars modes q `<=` froz -> *)
    acyclic_sigma s ->
    let modes := flatten_mode sig in
    relSS sP s sV ->
    good_mode modes ->
    check_tm sP empty q sig ->
    check_atoms sP (assume_tm sP sV hd sig) bo ->
    H u froz modes q hd s = Some s' -> check_atoms sP empty [seq deref_atom s' i  | i <- bo].
  Proof.
    elim: hd sig bo s s' q sV => //=[|h hs IH] sig bo s s' q sV A REL.
      set X:= (match sig with | b _ | _ => _ end).
      replace X with sV; last by rewrite{}/X; case: sig REL => [|[] ms].
      clear X; case: sig => //=[b|m tf ta]; case: q => //=.
      by move=> _ _ + [<-]; apply: check_atoms_deref.
    case: sig => [b|[] tf ta]/=; case: q => //=q0 qs GM; last first.
      move=> TR C; case U: unif.unify => //=[s''] H.
      apply: check_atoms_deref C.
        by apply: acyclic_sigma_H (unif_acyclic A U) H.
      (* should prove transitivity of relSS over unify and H *)
      admit.
    case M: matching => //=[s''] TR Ch  H.
    have A' := (matching_acyclic A M).
    apply: IH Ch H => //; last first.
      move: TR; rewrite check_tm_simpl; case: eqP => // IE.
      case G: get_sig => //[sx].
      case C: check_tm => //[sig|sig].
        by case: ifP => //; case: eat_ty.
      by case: ifP => //CT; case: ifP => I//; case: eat_ty.
    have R' : relSS sP s'' sV.
      (* same proof as above *)
      admit.
    case: h M => //v M.
    case: fndP => //=vV.
      case: ifP => // C.
      apply/forallP => [[x xP]]; rewrite valPE ffunE/=.
      rewrite/= !finmap.inE in xP.
      have [|sm D1 D2] := montanari_extP A _ M; subst.
        (* should be OK *)
        admit.
      rewrite fnd_cat.
      have xs: x \in domf s.
        by move: xP; case: eqP =>//=[?|? {C}vV]; subst;
        have:= forallP REL [`vV]; rewrite valPE; case: fndP.
      rewrite xs in_fnd.
      rewrite/deref_sig2 ffunE valPE.
      rewrite derefxx; last first.
        apply/forallP => -[y yP]; rewrite valPE [val _]/=.
        rewrite fnd_cat (in_fnd yP) ifF//=; last first.
          by have /negbTE := fdisjointP_sym D1 _ yP.
        (* should be ok by adding in montanari_extP that vars sm not in ...  *)
        admit.
      (* should be ok *)
      replace (deref _ _) with (deref sm s.[xs]) by admit.
      move: xP; case: eqP => //xv; subst; rewrite (orTb,orFb).
        move=> _.
        have:= forallP REL [`vV]; rewrite valPE in_fnd/=.
        have:= deref2 (Tm_V v) A; rewrite deref_V in_fnd/= => ->.
        rewrite/check_tmM/get_sig.
        have:= get_tm_hd_deref sm s.[xs].
        case G: get_tm_hd => [p|[d|v']]->; last first.
        - by rewrite not_fnd.
        - rewrite (flatten_term_deref_mapD _ G).
          case F: flatten_term => //=.
          case Ch: check_tm => //[sig].
          move: Ch; rewrite check_tm_simpl => -[?]; subst.
          move: C; case VV: sV.[vV] => //=[[]]//=.
          by case: tf {TR} => //[[]]//.
        - case: fndP => //=pP.
          rewrite (flatten_term_deref_map _ G).
          case Ch: check_tm => //[sig|sig].
            case: ifP => //=C'/eqP W.
            (* should improve lemma check_tm_deref to consider DetErr case *)
            admit.
          have Asm : acyclic_sigma sm by admit.
          have := check_tm_deref Asm (relSS0 _ _) (isOkP Ch).
          case Ch': check_tm => //= [sig'] _.
          (* should import check_tm_deref to relate the input and output sig *)
          admit.
      move=> xV.
      have:= forallP REL [`xV]; rewrite valPE/= in_fnd.
      have:= deref2 (Tm_V x) A; rewrite deref_V in_fnd/= => ->.
      rewrite/check_tmM/get_sig.
      have:= get_tm_hd_deref sm s.[xs].
      case G: get_tm_hd => [p|[d|v']]->; last first.
      - by rewrite not_fnd.
      - rewrite (flatten_term_deref_mapD _ G).
        case F: flatten_term => //=.
        case Ch: check_tm => //[sig].
        move: Ch; rewrite check_tm_simpl => -[?]; subst.
        by rewrite in_fnd//.
      - case: fndP => //=pP.
        rewrite (flatten_term_deref_map _ G).
        case Ch: check_tm => //[sig|sig].
          case: ifP => //=C'/eqP W.
          (* should improve lemma check_tm_deref to consider DetErr case *)
          admit.
        have Asm : acyclic_sigma sm by admit.
        have := check_tm_deref Asm (relSS0 _ _) (isOkP Ch).
        case Ch': check_tm => //= [sig'] _.
        (* should import check_tm_deref to relate the input and output sig *)
        admit.
    admit.
  Admitted.

  Lemma all_disjoint_flatten_term s l:
    vars l # s -> all (fun x : Tm => vars x # s) (flatten_term l).
  Proof. by elim: l => //=f Hf a Ha; rewrite fdisjointUX all_rcons => /andP[/Hf->->]. Qed.

  Lemma get_frozen_vars_sub m l: get_frozen_vars m (flatten_term l) `<=` vars l.
  Proof.
    apply/fsubset_trans/vars_tms_flatten_term; rewrite/vars_tms.
    move: (flatten_term _) m; elim => {l}[|l ls IH]//=[|m ms]//=.
    case: m => /=.
      by rewrite fsetUS//=.
    by rewrite fsubsetU//IH orbT.
  Qed.

  Lemma det_check_bc pr c fv r s:
    check_program pr -> call_is_det pr.(sig) fmap0 (deref s c) -> 
    bc u pr fv c s = r ->
    big_or_det pr.(sig) r.2.
  Proof.
    rewrite/big_or_det => /andP[ME CR] CT <-{r}.
    rewrite mut_exclP//=; last first.
      by apply: call_is_det_tm_is_det.
    rewrite/bc; set QUERY := deref s c in CT *.
    case AS: acyclic_sigma => //=.
    case TH: get_tm_hd => [p|]//=.
    case: fndP => //= ppr.
    rewrite !push/=.
    case: pr ME CR CT ppr => /= rs sig; rewrite/check_rules/= => ME CR CD ppr.
    move: CD; rewrite/call_is_det/check_tmM/get_sig TH/= in_fnd.
    move=> /ch_eqb_correct.
    case C: check_tm => [||[[|[]]|]]//= _.
    move: ME; rewrite/mut_excl push/= => /andP[GM _].
    elim: rs CR => //= -[hd bo] rs IH /= /andP[H1 H2].
    rewrite !push/=.
    case: ifP => //= Hh; first by apply: IH.
    rewrite !head_fresh_rule/=.
    set FR := fresh_rules _ _ in IH *.
    set R := rename FR.1 _ _.
    case H: H => [s'|]; last by apply: IH.
    rewrite !push/= IH// andbT.
    rewrite/deref_pair/=/fresh_rule!push/= -/R.
    move: Hh; rewrite head_fresh_rule/= -/FR-/R eq_sym => /eqP Hh {IH}.
    move: H1; rewrite/check_rule.
    have {}Hh := (proj1 (callable_rename _ _ _ _) Hh).
    rewrite Hh in_fnd /tm_is_det Hh in_fnd /=.
    have {}GM := forallP GM [`ppr]; rewrite valPE// in GM.
    rewrite (is_det_sig_check_tm C)//=.
    move: H2.
    (* set modes := flatten_mode _. *)
    (* set sigF := flatten_sig _. *)
    move=> + /(check_atoms_fresh_rename FR.1).
    move: H.
    set RT := rename _ _ _.
    set FA := fresh_atoms _ _ _.
    set Q := flatten_term _.
    set H' := flatten_term _ => H H1 Hx.
    apply: det_check_H Hx H => //.
      by apply/forallP => -[]//.
    rewrite C//.
  Qed.
  
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
From mathcomp Require Import all_ssreflect.

Section Lookup.
  Set Implicit Arguments.
  Variables (K : eqType) (V : Type).

  Definition remove k (L : seq (K*V)) := filter (fun y => k != y.1) L.
  
  (* get the first value (option) for key k *)
  Fixpoint lookup (k : K) (l : seq (K * V)) : option V :=
    match l with
    | [::] => None
    | (k',v)::xs => if k' == k then Some v else lookup k xs
    end.

  Definition key_absent k (l: seq (K * V)) := 
    match lookup k l with None => true | _ => false end.

  Fixpoint valid_sig (L : seq (K*V)) :=
    match L with
    | [::] => true
    | x::xs => key_absent x.1 xs && valid_sig xs
    end.

  Fixpoint add k v l : (seq (K*V)) :=
    match l with
    | [::] => [::(k, v)]
    | x :: xs => if x.1 == k then (k, v) :: xs else x :: add k v xs
    end.

  Lemma valid_sig_add_diff {k k' v' l}:
    size [seq y <- l | k == y.1] = 0 ->
      k <> k' ->
        size [seq y <- add k' v' l | k == y.1] = 0.
  Proof.
    elim: l k k' v' => //=.
      move=> k k' v' _; case: eqP => //.
    move=> [k v] l IH k1 k2 v'.
    case:eqP => //= H1 H2 H3.
    have IH' := IH _ _ _ H2 H3.
    case:eqP => //= H4; subst; case: eqP => //=.
  Qed.

  Lemma key_absent_add_diff {k k' v} l:
    k <> k' -> key_absent k' (add k v l) = key_absent k' l.
  Proof.
    rewrite/key_absent.
    elim: l k k' v => //=[|[k v]xs IH] k1 k2 v1//=; repeat case: eqP => //=; try congruence.
    move=> H1 H2 H3.
    by apply: IH.
  Qed.

  Lemma valid_sig_add {l k v}:
    valid_sig l -> valid_sig (add k v l).
  Proof.
    elim: l k v => //= [[k v]] l IH k' v'/= /andP[H1 H2].
    case:eqP => H3; subst => /=.
      rewrite H1//.
    rewrite IH//andbT key_absent_add_diff//; congruence.
  Qed.

  Goal forall k v l, size (add k v l) <> 0.
  Proof. move=> ??[]//=*; case: ifP => //. Qed.

End Lookup.
Arguments lookup {_ _}.
Arguments remove {_ _}.
Arguments add {_ _}.
Arguments valid_sig {_ _}.
Arguments key_absent {_ _}.



Section lookup.
  Lemma key_absent_remove {T: eqType} {K:Type} {k} {l: seq (T*K)}:
    (key_absent k l) -> remove k l = l.
  Proof.
    rewrite/key_absent.
    elim: l k => //= [[k v]] xs IH k'; case: eqP => //= H1 H2.
    rewrite IH//.
    case:eqP => //; congruence.
  Qed.

  Lemma lookup_remove_None {T: eqType} {K:Type} {k} {l: seq (T*K)}:
    (lookup k (remove k l)) = None.
  Proof.
    elim: l k => //= -[k v] l IH k'/=.
    case:eqP => //= H; rewrite IH; case: eqP; congruence.
  Qed.

  Lemma lookup_remove_diff {T: eqType} {K:Type} {k k'} {l: seq (T*K)}:
     k' <> k ->
      lookup k (remove k' l) = lookup k l.
  Proof.
    elim: l k k' => //= -[k v] l IH k1 k2 H.
    case:eqP => //= H1; subst.
      by case:eqP => //= _; apply: IH.
    case: eqP => //= H2; subst.
    by apply: IH.
  Qed.

  Lemma remove_comm {T: eqType} {K:Type} {x y} {l: seq (T*K)}:
    remove x (remove y l) = remove y (remove x l).
  Proof.
    elim: l x y => //= -[k v] xs IH/= x y.
    case: eqP => H/=; subst.
      case: eqP => H1/=; subst.
        apply: IH.
      rewrite eqxx/=; apply: IH.
    case:eqP => //=H1; subst.
    case:eqP => //= _; f_equal.
    apply: IH.
  Qed.

  Lemma lookup_cat {T : eqType} {K:Type} {k} {X Y : seq (T * K)}:
      lookup k (X ++ Y) = 
        if key_absent k X then lookup k Y
        else lookup k X.
  Proof.
    rewrite/key_absent.
    elim: X k Y => [|[k v] xs IH] k' ys//=.
    case:eqP => //<-{k'}.
  Qed.

  Lemma valid_sig_cat {T : eqType} {K:Type} {k} {X Y : seq (T * K)}:
      valid_sig (X ++ k ::  Y) ->
        key_absent k.1 X.
  Proof.
    rewrite/key_absent.
    elim: X k Y => //= [[k v] xs] IH [k' v'] ys/= /andP[H1 H2].
    have/= {IH}:= IH _ _ H2.
    move: H1; rewrite/key_absent.
    rewrite lookup_cat.
    rewrite/key_absent.
    case:eqP => H//; subst.
    case: lookup => //=.
    by rewrite eqxx.
  Qed.

  Lemma add2  {T: eqType} {K:Type} {k v v1} {A:seq (T*K)} : add k v (add k v1 A) = add k v A.
  Proof.
    elim: A k v v1 => //=[|[k v] xs IH] k' v' v2/=.
      rewrite eqxx => //.
    case: eqP => //= H; subst.
      rewrite eqxx//=.
    case: eqP => //=; rewrite IH//.
  Qed.

  Lemma add_cat {T: eqType} {K:Type} (L: seq (T*K)) {k v1 v2 xs}:
    key_absent k L ->
    add k v1 (L ++ (k, v2) :: xs) = (L ++ (k, v1) :: xs).
  Proof.
    rewrite/key_absent.
    elim: L k v1 v2 xs => //= [|[k v]xs IH] k1 v1 v2 ys/=.
      by rewrite eqxx.
    case: eqP => H//; subst.
    move=> /IH->//.
  Qed.

  Lemma lookup_add_same {T: eqType} {K:Type} {S: seq (T*K)} {k v}:
    lookup k (add k v S) = Some v.
  Proof.
    elim: S k v => //= [|[k v] xs IH] k1 k2/=; case: eqP => //= H; subst; case: eqP => //.
  Qed.

  Lemma lookup_add_Some {T: eqType} {K:Type} {S: seq (T*K)} {k k' v' v}:
    lookup k (add k' v' S) = Some v ->
      if k' == k then v = v'
      else lookup k S = Some v.
  Proof.
    elim: S k k' v v' => //=[|[k v] xs IH] k1 k2 v1 v2.
    - case: eqP => //=; congruence.
    - case: eqP => /= H; subst.
        case: eqP => //=; congruence.
      case: eqP => //= H1; subst.
        case: eqP => //=; congruence.
      apply: IH.
  Qed.

  Lemma lookup_add_diff {T: eqType} {K:Type} {k k' v} {S: seq (T*K)}:
      k <> k' -> lookup k' (add k v S) = lookup k' S.
  Proof.
    elim: S k k' v => //= [|[k v] xs IH] k1 k2 v1/=.
      case:eqP => //=.
    case:eqP => H1 => //= H2.
      repeat case:eqP => //=; congruence.
    (repeat case: eqP) => // H.
    by apply: IH.
  Qed.

  Lemma lookup_add_Some2 {T: eqType} {K:Type} {kB k'} k v {S: seq (T*K)}:
    lookup k' S = Some kB ->
    exists kB',
      lookup k' (add k v S) = Some kB'.
  Proof.
    elim: S k k' kB v => [|[k v] xs IH]//= k1 k2 v1 v2/=.
    case: eqP => H1//=; subst.
      move=> [?]; subst.
      case: eqP => H; subst => /=; rewrite eqxx; by eexists.
    case: eqP => H2 H3; subst => /=; case: eqP => H4; subst => //.
      by rewrite H3; eexists.
    by apply: IH H3.
  Qed.

  Lemma add_comm {T: eqType} {K:Type} {k1 k2 m1 m2}  {S: seq (T*K)}:
    k1 <> k2 -> add k1 m1 (add k2 m2 S) = add k2 m2 (add k1 m1 S).
  Proof.
    elim: S k1 k2 m1 m2 => //=[|[k v]xs IH] k1 k2 m1 m2 H/=.
      do 2 case: eqP => //=; try congruence.
      admit. (*should be ok by ordering element*)
    case eqP => //=H1; subst.
      repeat case: eqP; try congruence.
      move=> /=.
      rewrite eqxx//.
    repeat case: eqP => /=; try congruence.
    move=> H3 H4.
    by f_equal; apply: IH.
  Admitted.
  
End lookup.


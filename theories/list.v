From det Require Import prelude.
From mathcomp Require Import all_ssreflect.

Section aux.
  Lemma ltn_leq_trans m n p :
    m < n -> n <= p -> m < p.
  Proof.
    move=> Hmn Hnp.
    apply: leq_trans Hmn Hnp.
  Qed.

  Lemma add_succ {x}: x = x.+1 -> False.
  Proof. elim: x => // n H; inversion 1; auto. Qed.

  Lemma flatten_empty {T R : Type} {l: list T}:
    @flatten R [seq [::] | _ <- l] = [::].
  Proof. elim: l => //. Qed.

  Lemma size_list {T : Type} {l1 l2: list T}: l1 = l2 -> size l1 = size l2.
  Proof. move=>->//. Qed.

  Lemma cat_nil {T: Type} {l1 l2: list T}: l2 = l1 ++ l2 -> l1 = [::].
  Proof.
    elim: l2 l1 => [|x xs IH] l1.
      rewrite cats0//.
    case: l1 => //y ys[<-].
    rewrite (catA _ [::x])=>/IH.
    case: ys => //.
  Qed.

  Lemma cat_nil1 {T: Type} {l1 l2: list T}: l2 = l2 ++ l1 -> l1 = [::].
  Proof.
    elim: l2 l1 => [|x xs IH] l1.
      case: l1 =>//.
    rewrite cat_cons=>-[].
    apply: IH.
  Qed.

  Lemma map_cats0 {T R : Type} (F : list T -> list R) (g:list (list T)): map (fun x => F x ++ [::]) g = map F g.
  Proof. elim: g => //=x xs->; rewrite cats0//. Qed.

  Lemma map_map_cats0 {T R : Type} (F: list T -> list R) g: map (map (fun x => F x ++ [::])) g = map (map F) g.
  Proof. elim: g => //= x xs->; rewrite map_cats0//. Qed.

  Lemma map_cats_same {T : Type} (X Y:list (list T)) hd: 
    X = Y -> [seq x ++ hd | x <- X] = [seq x ++ hd | x <- Y].
  Proof.
    move=>->//.
  Qed.

  Lemma map_cats_same1 {T R : Type} (P F: list T -> list R) X Y hd: 
    map P X = map F Y -> [seq P x ++ hd | x <- X] = [seq F x ++ hd | x <- Y].
  Proof.
    elim: X Y => //=.
      move=>[]//.
    move=> x xs IH []//=y ys [H1 H2].
    rewrite (IH ys)// H1//.
  Qed.

  Lemma cons_false {T: Type} {x:T} {xs}: x :: xs = xs -> False.
  Proof. elim: xs x => //x xs IH y[_/IH]//. Qed.

  Lemma addSn_false {a b}: a = a + b.+1 -> False.
  Proof. elim: a b => // n H n1 []/H//. Qed.

  Lemma cat_same_tl {T : Type} {l1 l2 l3: list T}: l1 ++ l3 = l2 ++ l3 -> l1 = l2.
  Proof. 
    elim: l1 l2 l3 => //.
      move=>[]//x xs l3/=.
      rewrite -cat_cons.
      move=>/cat_nil//.
    move=> x xs IH [|y ys]//l3.
      move=>/=/esym; rewrite -cat_cons => /cat_nil//.
    move=>[<-]/IH->//.
  Qed.

  Lemma split_list_size {T : Type} (x y : nat) (z : seq T) :
    x + y <= size z ->
    exists r s : seq T, size r = x /\ r ++ s = z.
  Proof.
    move=> Hle.
    exists (take x z), (drop x z).
    split; last first.
    - rewrite cat_take_drop//.
    - rewrite size_take.
      have {}Hle: x <= size z.
        apply: leq_trans (leq_addr _ _) Hle.
      case: (@eqVneq _ x (size z)).
        move=>->; rewrite if_same//.
      move=> H.
      have:= ltn_neqAle x (size z).
      rewrite Hle H =>->//.
  Qed.

  Lemma cat_cat_size {T:Type} {A B C D : list T}:
    size A = size C -> A ++ B = C ++ D -> ((A = C) * (B = D))%type.
  Proof.
    elim: A B C D => [|x xs IH] B []//=y ys D [H1][H2 H3]; subst.
    have {}IH := IH _ _ _ H1 H3.
    rewrite !IH//.
  Qed.
    Lemma size_exists {T:Type} (xs : seq T) n :
    size xs <= n -> exists t, t + size xs = n.
  Proof.
    move=> H.
    exists (n - size xs).
    rewrite addnC.
    apply: subnKC H.
  Qed.

  Lemma size_exists2 {T : Type} (lA lB : seq T) n :
    size lB + size lA <= n -> exists t, size lA + t = n.
  Proof.
    move=> H.
    have Hle: size lA <= n.
      by apply: leq_trans H; rewrite leq_addl.
    exists (n - size lA).
    apply: subnKC Hle.
  Qed.

  Lemma leq_exists a b:
    a <= b -> exists x, a + x = b.
  Proof.
    move=> H; exists (b - a).
    rewrite addnC subnK//.
  Qed.


  Lemma suffix_consL {T:eqType} (x:T) l1 l2:
    suffix l1 (x::l2) -> l1 = (x::l2) \/ suffix l1 l2.
  Proof.
    move=> /suffixP[[]]/=; auto.
    move=> a l [->->]; right.
    by apply/suffix_catr/seq.suffix_refl.
  Qed.
End aux.

Class IsList (Th Tl : Type)  := {
  nilC : Tl;
  consC : Th -> Tl -> Tl;
  appendC : Tl -> Tl -> Tl;
  eqB : Tl -> Tl -> bool;
  size   : Tl -> nat;
  take   : nat -> Tl -> Tl;
  drop   : nat -> Tl -> Tl;
  behead : Tl -> Tl;
  suffix : Tl -> Tl -> bool;
  all: (Th -> bool) -> Tl -> bool;
  map: (Th -> Th) -> Tl -> Tl;
  mem: Th -> Tl -> bool;

  cat_take_drop : forall (n0 : nat) s, appendC (take n0 s) (drop n0 s) = s;
  cat_cons : forall x s1 s2, appendC (consC x s1) s2 = consC x (appendC s1 s2);
  cats0  : forall (x: Tl), appendC x nilC = x;
  cats20 : forall l1 l2, appendC l1 l2 = nilC -> l1 = nilC /\ l2 = nilC;
  cat0s  : forall (x: Tl), appendC nilC x = x;
  catA   : forall l1 l2 l3, appendC l1 (appendC l2 l3) = appendC (appendC l1 l2) l3;
  suffix0s : forall l, suffix nilC l;
  suffixs0 : forall l, suffix l nilC = (eqB l nilC);
  take_size : forall s, take (size s) s = s;
  drop_size : forall s, drop (size s) s = nilC;
  size_nil: size nilC = 0;
  drop0 l : drop 0 l = l;
  take0 l : take 0 l = nilC;
  drop_nil n : drop n nilC = nilC;
  take_nil n : take n nilC = nilC;
  eqb_refl l1: eqB l1 l1;
  eqBP l1 l2: reflect (l1 = l2) (eqB l1 l2);
  size_cat l1 l2: size (appendC l1 l2) = size l1 + size l2;
  suffix_refl xs : suffix xs xs;
  suffix_catr xs ys zs : suffix xs ys -> suffix xs (appendC zs ys);
  take_size_cat n s1 s2: size s1 = n -> take n (appendC s1 s2) = s1;
  drop_size_cat n s1 s2: size s1 = n -> drop n (appendC s1 s2) = s2;
  take_cons n x xs: take n.+1 (consC x xs) = consC x (take n xs);
  drop_cons n x xs: drop n.+1 (consC x xs) = (drop n xs);
  behead_cons x xs: behead (consC x xs) = xs;
  suffixP s1 s2: (exists s2', s2 = appendC s2' s1) -> (suffix s1 s2);
  suffixP1 s1 s2: (suffix s1 s2) -> (exists s2', s2 = appendC s2' s1);
  size_suffix s1 s2: suffix s1 s2 -> size s1 <= size s2;
  suffix_catl: forall s1 s2 s3 s3', size s3 = size s3' ->
    suffix (appendC s1 s3) (appendC s2 s3') = (eqB s3 s3') && suffix s1 s2;
  suffix_cons: forall x l1 l2, suffix l1 (consC x l2) -> l1 = consC x l2 \/ suffix l1 l2;
  all_cat p l1 l2: all p (appendC l1 l2) = all p l1 && all p l2;
  all_cons p x xs: all p (consC x xs) = p x && all p xs; 
  size_cons x xs: size (consC x xs) = (size xs).+1;
  map_cat F l1 l2 : map F (appendC l1 l2) = appendC (map F l1) (map F l2);
  map_cons F l1 l2 : map F (consC l1 l2) = consC (F l1) (map F l2);
  size_map F l1 : size (map F l1) = size l1;
  map_id l1 : map id l1 = l1;
  append_same_len {l1 l1' l2 l2'}: 
    size l1 = size l1' -> size l2 = size l2' -> appendC l1 l2 = appendC l1' l2' -> ((l1 = l1') * (l2 = l2'))%type;
  append_sameR {l1 l2 l3}: appendC l1 l3 = appendC l2 l3 -> l1 = l2; 
  take_cat (n0 : nat) s1 s2:
    take n0 (appendC s1 s2) =
    (if n0 < size s1 then take n0 s1 else appendC s1 (take (n0 - size s1) s2));
  size_take n0 s: size (take n0 s) = (if n0 < size s then n0 else size s);
  take_drop i j s: take i (drop j s) = drop j (take (i + j) s);
  take_min i j s: take (minn i j) s = take i (take j s);
  size_drop n0 s: size (drop n0 s) = size s - n0;
  take_oversize [n : nat] [s]: size s <= n -> take n s = s;
  map_take n F L: take n (map F L) = map F (take n L)
}.
Declare Scope SE.
Global Infix "++" := appendC : SE.
Global Open Scope SE.
Arguments nilC : simpl never.
Global Arguments consC {_ _ _}: simpl never.
Arguments appendC: simpl never.
Arguments eqB : simpl never.
Arguments size : simpl never.
Arguments take : simpl never.
Arguments drop : simpl never.
Arguments behead : simpl never.
Arguments suffix : simpl never.
Arguments all : simpl never.
Arguments map : simpl never.
Arguments mem : simpl never.


Section mkIsList.

  Variable X : eqType.
  Variable alts : eqType.
  Variable nil : alts.
  Variable cons : X -> alts -> alts.

  Local Notation "[ :: ]" := nil (format "[ :: ]").
  Local Notation "[ :: x & s ]" := (cons x s) (format "'[hv' [ :: '['  x ']' '/ ' &  s ] ']'").

  Variable seq2alts : seq X -> alts.
  Variable alts2seq : alts -> seq X.
  Variable alts2seqs : forall x xs, alts2seq [:: x & xs ] = [:: x & alts2seq xs]%SEQ.
  Variable alts2seq0 : alts2seq [::] = [::]%SEQ.
  Variable seq2altss : forall x xs, seq2alts [:: x & xs ]%SEQ = [:: x & seq2alts xs].
  Variable seq2alts0 : seq2alts [::]%SEQ = [::].
  Variable alts2seqK : forall l, alts2seq (seq2alts l) = l.
  Variable seq2altsK : forall l, seq2alts (alts2seq l) = l.
  Variable seq2alts_inj : forall l1 l2,  seq2alts l1 = seq2alts l2 -> l1 = l2.
  Variable alts2seq_inj : forall l1 l2,  alts2seq l1 = alts2seq l2 -> l1 = l2.

  Definition altK := (alts2seqK,seq2altsK).
 
  Definition append_alts l1 l2 := seq2alts (cat (alts2seq l1) (alts2seq l2)).

  Definition all_alts p l := seq.all p (alts2seq l).

  Definition size_alts l1 := seq.size (alts2seq l1).

  Definition take_alts n l1 := seq2alts (seq.take n (alts2seq l1)).

  Definition drop_alts n l1 := seq2alts (seq.drop n (alts2seq l1)).

  Definition behead_alts l := seq2alts (seq.behead (alts2seq l)).

  Definition suffix_alts l1 l2 := seq.suffix (alts2seq l1) (alts2seq l2).

  Lemma suffixA_refl A: suffix_alts A A.
  Proof. by rewrite /suffix_alts seq.suffix_refl. Qed.

  Lemma size_cat_alts xs ys:
    size_alts (append_alts xs ys) = (size_alts xs) + (size_alts ys).
  Proof. by rewrite /size_alts/append_alts !altK seq.size_cat. Qed.

  Lemma suffixPA s1 s2: (exists s2', s2 = append_alts s2' s1) -> (suffix_alts s1 s2).
  Proof.
    move=> [s3 H]; rewrite /suffix_alts; apply/seq.suffixP.
    by exists (alts2seq s3); rewrite H /append_alts !altK.
  Qed.

  Lemma suffixPA1 s1 s2: (suffix_alts s1 s2) -> (exists s2', s2 = append_alts s2' s1).
  Proof.
    by move=> /seq.suffixP/= [s3 H]; exists (seq2alts s3); rewrite /append_alts !altK -H altK.
  Qed.

  Lemma catAA x y z: append_alts x (append_alts y z) = append_alts (append_alts x y) z.
  Proof. by rewrite /append_alts !altK seq.catA. Qed.

  Lemma cats0A l: append_alts l nil = l.
  Proof. by rewrite /append_alts alts2seq0 seq.cats0 altK. Qed.

  Lemma suffix_catlA s1 s2 s3 s3':
    size_alts s3 = size_alts s3' ->
    suffix_alts (append_alts s1 s3) (append_alts s2 s3') = (s3 == s3') && suffix_alts s1 s2.
  Proof.
    rewrite /append_alts /size_alts /suffix_alts !altK => H; rewrite seq.suffix_catl //.
    rewrite -[s3 as X in X == _]altK -[s3' as X in _ == X]altK; case: eqP => [->|]//=.
      by rewrite eqxx.
    by case: eqP=> //; rewrite !altK => ->.
  Qed.

  Definition mapA F l := seq2alts (seq.map F (alts2seq l)).

  Definition memA e l := e \in (alts2seq l).

  Lemma take_dropA (i j : nat) (s : alts) :
    take_alts i (drop_alts j s) =
    drop_alts j (take_alts (i + j) s).
  Proof.
    by rewrite /take_alts /drop_alts altK seq.take_drop !altK.
  Qed.

  Lemma take_minA (i j : nat) (s : alts) :
    take_alts (minn i j) s = take_alts i (take_alts j s).
  Proof.
    by rewrite /take_alts altK seq.take_min.
  Qed.

  #[refine] Local Instance mkIsList : @IsList X alts :=
    {| 
    nilC := nil; consC := cons;
    appendC := append_alts; size := size_alts; take := take_alts; drop := drop_alts;
    behead := behead_alts; eqB x y := x == y; suffix:= suffix_alts; all:= all_alts;
    map := mapA; mem := memA; take_drop := take_dropA; take_min := take_minA;
    suffix_catl := suffix_catlA;cats0:= cats0A; catA := catAA; size_cat:= size_cat_alts;
    suffix_refl := suffixA_refl; suffixP := suffixPA; suffixP1 := suffixPA1
    |}.
  Proof.
    all: try by move=> //.
    all: rewrite /append_alts /take_alts /drop_alts /size_alts /suffix_alts /mapA /behead_alts /all_alts =>>; rewrite ?altK ?alts2seq0 ?alts2seqs ?seq2alts0 ?seq2altss //.
    all: rewrite ?seq.size_drop ?seq.map_id ?seq.size_map ?altK //.
    all: rewrite ?seq.take0 ?seq.drop0 ?seq.take_cat ?seq.drop_cat ?seq.suffix0s ?seq.suffixs0 ?altK //.
    all: rewrite ?seq.cat_take_drop ?seq.map_cat ?seq.size_take ?altK //.
    all: rewrite ?seq.all_cat ?altK //.
    - rewrite -seq2alts0 => /seq2alts_inj.
      rewrite -[X in X = seq2alts _]altK.
      rewrite -[X in _ /\ X = seq2alts _]altK.
      by case: (alts2seq _) => //= ->.
    - by apply/eqP/eqP => [|->]; rewrite -alts2seq0 // => H; rewrite -[[::]]altK -H altK.
    - by rewrite seq.take_size altK.
    - by rewrite seq.drop_size.
    - exact eqP.
    - by move/seq.suffix_catr.
    - by move->; rewrite ltnn subnn seq.take0 seq.cats0 altK.
    - by move->; rewrite ltnn subnn seq.drop0 altK.
    - by apply: seq.size_suffix.
    - move=> /suffix_consL[]; auto ; rewrite -alts2seqs => /alts2seq_inj; auto.
    - by move=> /cat_cat_size H1 /cat_cat_size H2 /seq2alts_inj /H1 [/alts2seq_inj-> /alts2seq_inj->].
    - by move => /seq2alts_inj /cat_same_tl /alts2seq_inj.
    - by rewrite (fun_if seq2alts).
    - by move=> /seq.take_oversize ->; rewrite altK.
    - by rewrite seq.map_take//.
  Defined.

End mkIsList.

Arguments mkIsList {_ _ _ _}.

From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

(*BEGIN*)
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
    seq.suffix l1 (x::l2) -> l1 = (x::l2)%SEQ \/ seq.suffix l1 l2.
  Proof.
    move=> /seq.suffixP[[]]/=; auto.
    move=> a l [->->]; right.
    by apply/seq.suffix_catr/seq.suffix_refl.
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
    size l1 = size l1' -> size l2 = size l2' -> appendC l1 l2 = appendC l1' l2' -> (l1 = l1' /\ l2 = l2')%type2;
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


Global Notation "x ::: xs" :=
  (consC x xs)
  (at level 3, no associativity, only parsing)
  : SE.

Global Notation "x :: xs" :=
  (consC x xs)
  (at level 60, no associativity, only parsing)
  : SE.

(*SNIP: elpi_def*)
Inductive alts := no_alt | more_alt of (Sigma * goals) & alts
with goals := no_goals | more_goals of (A * alts) & goals .
(*ENDSNIP: elpi_def*)

Declare Scope alts_scope.
Delimit Scope alts_scope with A.
Bind Scope alts_scope with alts.

Declare Scope goals_scope.
Delimit Scope goals_scope with G.
Bind Scope goals_scope with goals.

Notation "[ :: ]" := no_goals (format "[ :: ]") : goals_scope.
Notation "[ :: ]" := no_alt (format "[ :: ]") : alts_scope.

Notation "[ :: x1 ]" := (more_alt x1%G [::]) (format "[ ::  x1 ]") : alts_scope.
Notation "[ :: x1 ]" := (more_goals x1%A [::]) (format "[ ::  x1 ]") : goals_scope.

Notation "[ :: x & s ]" := (more_alt x%G s) (format "'[hv' [ :: '['  x ']' '/ ' &  s ] ']'") : alts_scope.
Notation "[ :: x & s ]" := (more_goals x%A s) (format "'[hv' [ :: '['  x ']' '/ ' &  s ] ']'") : goals_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (more_alt x1 (more_alt x2 .. (more_alt xn s) ..))
  (format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : alts_scope.
Notation "[ :: x1 , x2 , .. , xn & s ]" := (more_goals x1 (more_goals x2 .. (more_goals xn s) ..))
  (format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : goals_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (more_alt x1 (more_alt x2 .. (more_alt xn [::]) ..))
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : alts_scope.
Notation "[ :: x1 ; x2 ; .. ; xn ]" := (more_goals x1 (more_goals x2 .. (more_goals xn [::]) ..))
  (format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : goals_scope.


Open Scope goals_scope.
Open Scope alts_scope.

Fixpoint eqbA t1 t2 :=
  match t1, t2 with
  | no_alt, no_alt => true
  | more_alt (s1,h1) t1, more_alt (s2, h2) t2 => (s1 == s2) && eqbGs h1 h2 && eqbA t1 t2
  | _, _ => false
  end
with eqbGs t1 t2 :=
  match t1, t2 with
  | no_goals, no_goals => true
  | more_goals (a1,h1) t1, more_goals (a2,h2) t2 => (a1 == a2) && eqbA h1 h2 && eqbGs t1 t2
  | _, _ => false
  end.

Lemma eqb_reflA l : eqbA l l
  with eqb_reflG l : eqbGs l l.
Proof.
  {
    case: l => /=//.
    move=> [s1 g] gs; rewrite eqxx eqb_reflA eqb_reflG//.
  }
  case: l => /=//.
  move=> [a al] /= gs; rewrite ?eqxx eqb_reflG//eqb_reflA//.
Qed.

Lemma eqbPA l1 l2 : reflect (l1 = l2) (eqbA l1 l2)
  with eqbPG l1 l2 : reflect (l1 = l2) (eqbGs l1 l2).
Proof.
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> ??; constructor => //.
    - move=> []?; constructor => //.
    - move=> [s1 x] xs [s2 y] ys.
      case: eqP => //=?; last first; subst.
        constructor; congruence.
      apply: (iffP andP) => [[/eqbPG -> /eqbPA -> //]|[-> ->]].
      by split; [ apply/eqbPG| apply/eqbPA].
  }
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> ??; constructor => //.
    - move=> []?; constructor => //.
    - move=> [s1 x] xs [s2 y] ys.
      case: eqP => //=?; last first; subst.
        constructor; congruence.
      apply: (iffP andP) => [[/eqbPA -> /eqbPG -> //]|[-> ->]].
      by split; [ apply/eqbPA| apply/eqbPG].
  }
Qed.

Lemma goals_eqb_OK : Equality.axiom eqbGs.
Proof. apply: iffP2 eqbPG eqb_reflG. Qed.
HB.instance Definition _ : hasDecEq goals := hasDecEq.Build goals goals_eqb_OK.

Lemma alts_eqb_OK : Equality.axiom eqbA.
Proof. apply: iffP2 eqbPA eqb_reflA. Qed.
HB.instance Definition _ : hasDecEq alts := hasDecEq.Build alts alts_eqb_OK.

  Fixpoint seq2alts (l : seq (Sigma * goals)) : alts :=
    match l with
    | [::]%SEQ => [::]
    | [:: x & xs]%SEQ => [:: x & seq2alts xs]
    end.

  Fixpoint alts2seq (a : alts) : seq (Sigma * goals) :=
    match a with
    | [::] => [::]%SEQ
    | [:: x & xs] => [:: x & alts2seq xs]%SEQ
    end.
  Lemma alts2seqs : forall x xs, alts2seq [:: x & xs ] = [:: x & alts2seq xs]%SEQ. by []. Qed.
  Lemma alts2seq0 : alts2seq [::] = [::]%SEQ. by []. Qed.
  Lemma seq2altss : forall x xs, seq2alts [:: x & xs ]%SEQ = [:: x & seq2alts xs]. by []. Qed.
  Lemma seq2alts0 : seq2alts [::]%SEQ = [::]. by []. Qed.
  Lemma alts2seqK : forall l, alts2seq (seq2alts l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2altsK : forall l, seq2alts (alts2seq l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2alts_inj : forall l1 l2,  seq2alts l1 = seq2alts l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]alts2seqK -[l2]alts2seqK H. Qed.
  Lemma alts2seq_inj : forall l1 l2,  alts2seq l1 = alts2seq l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]seq2altsK -[l2]seq2altsK H. Qed.

  Global Instance IsList_alts : @IsList (Sigma * goals)%type alts :=
    mkIsList seq2alts alts2seq alts2seqs alts2seq0 seq2altss seq2alts0
      alts2seqK seq2altsK seq2alts_inj alts2seq_inj.

  Fixpoint seq2goals (l : seq (A * alts)) : goals :=
    match l with
    | [::]%SEQ => [::]%G
    | [:: x & xs]%SEQ => [:: x & seq2goals xs]%G
    end.

  Fixpoint goals2seq (a : goals) : seq (A * alts) :=
    match a with
    | [::]%G => [::]%SEQ
    | [:: x & xs]%G => [:: x & goals2seq xs]%SEQ
    end.
  Lemma goals2seqs : forall x xs, goals2seq [:: x & xs ]%G = [:: x & goals2seq xs]%SEQ. by []. Qed.
  Lemma goals2seq0 : goals2seq [::]%G = [::]%SEQ. by []. Qed.
  Lemma seq2goalss : forall x xs, seq2goals [:: x & xs ]%SEQ = [:: x & seq2goals xs]%G. by []. Qed.
  Lemma seq2goals0 : seq2goals [::]%SEQ = [::]%G. by []. Qed.
  Lemma goals2seqK : forall l, goals2seq (seq2goals l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2goalsK : forall l, seq2goals (goals2seq l) = l.
  Proof. by elim => //= x xs ->. Qed.
  Lemma seq2goals_inj : forall l1 l2,  seq2goals l1 = seq2goals l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]goals2seqK -[l2]goals2seqK H. Qed.
  Lemma goals2seq_inj : forall l1 l2,  goals2seq l1 = goals2seq l2 -> l1 = l2.
  by move=> l1 l2 H; rewrite -[l1]seq2goalsK -[l2]seq2goalsK H. Qed.

  Global Instance IsList_goals : @IsList (A * alts)%type goals :=
    mkIsList seq2goals goals2seq goals2seqs goals2seq0 seq2goalss seq2goals0
      goals2seqK seq2goalsK seq2goals_inj goals2seq_inj.

Ltac fConsA x xs := change (more_alt x xs) with (consC x xs).
Ltac fConsG x xs := change (more_goals x xs) with (consC x xs).
Ltac fNilA := change no_alt with (@nilC _ _ IsList_alts).
Ltac fNilG := change no_goals with nilC.

Lemma seq2alts_cat : forall l1 l2,  seq2alts (l1 ++ l2) = (seq2alts l1 ++ seq2alts l2).
Proof. by elim => //=[|x xs IH] l2; rewrite (cat0s, cat_cons)//IH. Qed.
Lemma seq2goals_cat : forall l1 l2,  seq2goals (l1 ++ l2) = (seq2goals l1 ++ seq2goals l2).
Proof. by elim => //=[|x xs IH] l2; rewrite (cat0s, cat_cons)//IH. Qed.

Lemma cat_right_same {l1 l2} (l3:alts): 
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof.
  elim: l1 l2 l3 => //.
    move=>[]//x xs l3/=.
    fConsA x xs; fNilA.
    rewrite cat0s => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite size_cons size_cat.
    by rewrite addnC -addnS => /addSn_false.
  move=> x xs IH [|y ys]//l3; fNilA.
    fConsA x xs => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite cat_cons size_cons !size_cat size_nil.
    by rewrite addnC -addnS => /esym /addSn_false.
  move=>[<-]/IH->//.
Qed.


Definition if_cut F (g : A * alts) :=
  match g with
  | (lang.cut, a) => F a
  | _ => true
  end.

Definition apply_cut F (g : A * alts) : A * alts :=
  match g with
  | (a, ca) => (a, F ca)
  end.


Definition add_ca alts := apply_cut (fun x => x ++ alts).

Definition save_goals (a: alts) (gs b:goals) := map (add_ca a) b ++ gs.

Definition save_alts (a : alts) (gs: goals) (bs : alts) := 
  map (fun '((s,x): Sigma * goals) => (s, save_goals a gs x)) bs.

  Definition empty_ca_G (g : A * alts) :=
  match g with (_,[::]) => true | _ => false end.
Definition empty_caG goals := all empty_ca_G goals.
Definition empty_ca alts := all (fun x => empty_caG (snd x)) alts.

Definition a2g (a : A) : (A * alts) := (a,[::]).

Definition a2gs (b: seq A) := seq2goals [seq a2g x | x <- b].

Definition aa2gs (b: (seq (Sigma * R))) : alts := seq2alts [seq (x.1, a2gs x.2.(premises)) | x <- b].

Definition a2gs1 (b : Sigma * R) :=
  a2gs b.2.(premises).

Section Nur.

Variable u : Unif.
Variable p : program.

From det Require Import finmap.
Open Scope fset_scope.
Inductive nur : fvS -> Sigma -> goals ->  alts -> Sigma -> alts -> Prop :=
| StopE s a fv : nur fv s nilC a s a
| CutE s s1 a ca r gl fv : nur fv s gl ca s1 r -> nur fv s [:: (cut, ca) & gl]%G a s1 r
| CallE s s1 a b bs gl r t ca fv fv': 
  bc u p fv t s = (fv', [:: b & bs ]%SEQ) -> 
    nur fv' b.1 (save_goals a gl (a2gs1 b)) (save_alts a gl (aa2gs bs) ++ a) s1 r -> 
      nur fv s [:: (call t, ca) & gl]%G a s1 r
| FailE s s1 s2 t gl a al r ca fv fv': 
  bc u p fv t s = (fv',[::]%SEQ) -> nur fv' s1 a al s2 r -> nur fv s [:: (call t, ca) & gl]%G [:: (s1, a) & al] s2 r.

Lemma nur_consistent fv s G x xs1 xs2 s1 s2 :
  nur fv s G x s1 xs1 -> nur fv s G x s2 xs2 -> xs1 = xs2 /\ s1 = s2.
Proof.
  move=> H; elim: H xs2 s2 => //; clear.
  - inversion 1 => //.
  - move=> s a ca r gl fv H IH xs2.
    by inversion 1; subst; auto.
  - move=> s s1 a b bs gl r t ca ?? H H1 IH xs2 s2 H2.
    apply: IH.
    inversion H2; subst; move: H10; rewrite H => //-[???]; subst.
    assumption.
  - move=> s s1 s2 t gl a al r ca ?? H H1 IH xs2 s3 H2.
    apply: IH.
    inversion H2; subst => //; congruence.
Qed.

End Nur. 
(*END*)
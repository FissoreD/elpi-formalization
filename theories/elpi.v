From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

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

  (* Lemma cats20 {T: Type} {X Y : list T}: X ++ Y = [::] -> X = [::] /\ Y = [::].
  Proof. by destruct X. Qed. *)

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


End aux.

Class IsList {Th Tl : Type}  := {
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
  suffixP s1 s2: reflect (exists s2', s2 = appendC s2' s1) (suffix s1 s2);
  size_suffix s1 s2: suffix s1 s2 -> size s1 <= size s2;
  suffix_catl: forall s1 s2 s3 s3', size s3 = size s3' ->
    suffix (appendC s1 s3) (appendC s2 s3') = (eqB s3 s3') && suffix s1 s2;
  all_cat p l1 l2: all p (appendC l1 l2) = all p l1 && all p l2;
  all_cons p x xs: all p (consC x xs) = p x && all p xs; 
  size_cons x xs: size (consC x xs) = (size xs).+1;
  map_cat F l1 l2 : map F (appendC l1 l2) = appendC (map F l1) (map F l2);
  map_cons F l1 l2 : map F (consC l1 l2) = consC (F l1) (map F l2);
  size_map F l1 : size (map F l1) = size l1;
  map_id l1 : map id l1 = l1;
}.
Declare Scope SE.
Global Infix "++" := appendC : SE.
Open Scope SE.
Arguments nilC : simpl never.
Arguments consC : simpl never.
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

Global Notation "x ::: xs" :=
  (consC x xs)
  (at level 3, no associativity)
  : SE.

Global Notation "-[]" :=
  (nilC)
  (at level 3, no associativity,only printing)
  : SE.

Global Notation "(( x ))" := (consC x nilC)
  (at level 3, no associativity,only printing)
  : SE.

Inductive G := 
  | call : program -> Callable -> G
  | cut : alts -> G
with alts :=
  | no_alt
  | more_alt : (Sigma * goals) -> alts -> alts
with goals :=
  | no_goals
  | more_goals : G -> goals -> goals .

Fixpoint eqbA t1 t2 :=
  match t1, t2 with
  | no_alt, no_alt => true
  | more_alt (s1,h1) t1, more_alt (s2, h2) t2 => (s1 == s2) && eqbGs h1 h2 && eqbA t1 t2
  | _, _ => false
  end
with eqbGs t1 t2 :=
  match t1, t2 with
  | no_goals, no_goals => true
  | more_goals h1 t1, more_goals h2 t2 => eqbG h1 h2 && eqbGs t1 t2
  | _, _ => false
  end
with eqbG t1 t2 :=
  match t1, t2 with
  | call p1 t1, call p2 t2 => (p1 == p2) && (t1 == t2)
  | cut ca1, cut ca2 => eqbA ca1 ca2
  | _, _ => false
  end.

Lemma eqb_reflA l : eqbA l l
  with eqb_reflG l : eqbGs l l
  with eqb_G_refl l : eqbG l l.
Proof.
  {
    case: l => /=//.
    move=> [s1 g] gs; rewrite eqxx eqb_reflA eqb_reflG//.
  }
  case: l => /=//.
  move=> [p t|ca]/=gs; rewrite ?eqxx eqb_reflG//eqb_reflA//.
  case: l => //=p t; rewrite !eqxx//.
Qed.

Lemma eqbPA l1 l2 : reflect (l1 = l2) (eqbA l1 l2)
  with eqbPG l1 l2 : reflect (l1 = l2) (eqbGs l1 l2)
  with eqbP_G l1 l2 : reflect (l1 = l2) (eqbG l1 l2).
Proof.
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> g gx; constructor => //.
    - move=> [s g] gs; constructor => //.
    - move=> [s1 x] xs [s2 y] ys.
      case: eqP => //=?; last first; subst.
        constructor; congruence.
      case X: eqbGs => /=.
        case Y: eqbA => /=; constructor.
          have:= eqbPA ys xs; rewrite Y.
          inversion 1; subst.
          have:= eqbPG y x; rewrite X.
          inversion 1; subst => //.
        have:= eqbPA ys xs; rewrite Y; inversion 1.
        move=> [??]; subst; auto.
      have:= eqbPG y x; rewrite X; inversion 1; constructor.
      move=>[??]; subst; auto.
  }
  {
    case: l1; case: l2 => /=.
    - constructor => //.
    - move=> g gx; constructor => //.
    - move=> g gs; constructor => //.
    - move=> x xs y ys.
      case X: eqbG => /=.
        case Y: eqbGs => /=; constructor.
          have:= eqbPG ys xs; rewrite Y.
          inversion 1; subst.
          have:= eqbP_G y x; rewrite X.
          inversion 1; subst => //.
        have:= eqbPG ys xs; rewrite Y; inversion 1.
        move=> [??]; subst; auto.
      have:= eqbP_G y x; rewrite X; inversion 1; constructor.
      move=>[??]; subst; auto.
  }
  case: l1 => [p t|ca].
  - case X: eqbG; constructor; case: l2 X => //=??.
      move=>/andP[/eqP->/eqP->//].
    move=> +[??]; subst; rewrite !eqxx//.
  - case X: eqbG; constructor; case: l2 X => //=ca' H.
      have:= eqbPA ca ca'; rewrite H; inversion 1; subst => //.
    have:= eqbPA ca ca'; rewrite H; inversion 1; subst; congruence.
Qed.

Lemma G_eqb_OK : Equality.axiom eqbG.
Proof. apply: iffP2 eqbP_G eqb_G_refl. Qed.
HB.instance Definition _ : hasDecEq G := hasDecEq.Build G G_eqb_OK.

Lemma goals_eqb_OK : Equality.axiom eqbGs.
Proof. apply: iffP2 eqbPG eqb_reflG. Qed.
HB.instance Definition _ : hasDecEq goals := hasDecEq.Build goals goals_eqb_OK.

Lemma alts_eqb_OK : Equality.axiom eqbA.
Proof. apply: iffP2 eqbPA eqb_reflA. Qed.
HB.instance Definition _ : hasDecEq alts := hasDecEq.Build alts alts_eqb_OK.

Section alts.
  Fixpoint append_alts l1 l2 := 
    match l1 with
    | no_alt => l2
    | more_alt hd tl => more_alt hd (append_alts tl l2)
    end.

  Fixpoint all_alts p l :=
    match l with
    | no_alt => true
    | more_alt hd tl => p hd && all_alts p tl
    end.

  Fixpoint size_alts l1 := 
    match l1 with
    | no_alt => 0
    | more_alt _ l1 => (size_alts l1).+1
    end.

  Fixpoint take_alts n l1 :=
    match n, l1 with
    | 0, _ | _, no_alt => no_alt
    | n.+1, more_alt x l => more_alt x (take_alts n l)
    end.

  Fixpoint drop_alts n l1 :=
    match n, l1 with
    | 0, l | _, (no_alt as l) => l
    | n.+1, more_alt _ l => drop_alts n l
    end.

  Definition behead_alts l :=
    match l with
    | no_alt => no_alt
    | more_alt _ l => l
    end.

  Fixpoint suffix_alts l1 l2 :=
    if l1 == l2 then true
    else 
    match l2 with
    | no_alt => false
    | more_alt _ xs => suffix_alts l1 xs
    end.

  Lemma suffixPA s1 s2: reflect (exists s2', s2 = append_alts s2' s1) (suffix_alts s1 s2).
  Proof.
    elim: s2 s1 => //=.
      move=>[|[S g] gs]; constructor.
        by exists no_alt.
      by move=>[]-[]//.
    move=> [s g] gs IH s1.
    case: ifP.
      move=>/eqbPA->; constructor; exists no_alt => //.
    move=> H.
    have [H1|H1] := IH s1; constructor.
      case: H1 => x->; exists (more_alt (s, g) x) => //.
    move=> [x H2]; apply: H1.
    case: x H2 => [|[s2 x] xs]/=.
      move=>?; subst.
      rewrite eqxx// in H.
    move=>[_ _ ->]; exists xs => //.
  Qed.

  Lemma catAA x y z: append_alts x (append_alts y z) = append_alts (append_alts x y) z.
  Proof. elim: x y z => //= -[s x] xs IH y z; rewrite IH//. Qed.

  Lemma cats0A l: append_alts l no_alt = l.
  Proof. elim: l => //= -[s x] xs ->//. Qed.  

  Lemma size_cat_alts xs ys:
    size_alts (append_alts xs ys) = (size_alts xs) + (size_alts ys).
  Proof. elim: xs ys => //= _ xs IH ys; rewrite IH; lia. Qed.

  Lemma suffix_catlA s1 s2 s3 s3':
    size_alts s3 = size_alts s3' ->
    suffix_alts (append_alts s1 s3) (append_alts s2 s3') = (s3 == s3') && suffix_alts s1 s2.
  Proof.
    elim: s3 s3' s1 s2 => //=.
      move=>[]//= s1 s2; rewrite !cats0A//.
    move=> [sb1 g] gs IH []//=[sb2 y] ys s1 s2 [H1].
    have:= IH _ _ _ H1.
    case: eqP => /=.
      move=>?; subst.
  Admitted.

  Fixpoint mapA F l :=
    match l with
    | no_alt => no_alt
    | more_alt x xs => more_alt (F x) (mapA F xs)
    end.

  Fixpoint memA e l := 
    match l with
    | no_alt => false
    | more_alt x xs => (e == x) || memA e xs
    end.

  #[refine] Global Instance IsList_alts : @IsList (Sigma * goals) alts :=
    {| 
    nilC := no_alt; consC := more_alt;
    appendC := append_alts; size := size_alts; take := take_alts; drop := drop_alts;
    behead := behead_alts; eqB x y := x == y; suffix:= suffix_alts; all:= all_alts;
    map := mapA; mem := memA
    |}.
  Proof.
    all: try by move=> //.
    move=> n; elim: n =>// n IH []//=g gs; rewrite IH//.
    move=> l1; elim: l1 => //= x xs->//.
    move=> l1; elim: l1 => //=x xs IH l2 l3; rewrite IH//.
    move=> l1; elim: l1 => //=x xs IH l2 l3; rewrite IH//.
    move=> l; elim: l => //.
    move=> l; elim: l => //-[s x]//=.
    move=> l; elim: l => //=-[s x] xs->//.
    move=> n; elim: n => //=.
    move=> n; elim: n => //=.
    move=> n; elim: n => //=.
    apply: eqbPA.
    apply: size_cat_alts.
    move=> xs; elim: xs => //=x xs H; rewrite eqxx//.
    move=> ++zs; elim: zs => //=x xs IH ys zs; case: ifP => // _; apply: IH.
    move=> n; elim: n => [|n IH] []//=g xs ys []/IH->//.
    move=> n; elim: n => [|n IH][]//= _ xs ys []/IH->//.
    apply: suffixPA.
    move=>s1 s2 /suffixPA [x ->]; rewrite size_cat_alts; lia.
    apply: suffix_catlA.
    move=> p l1; elim: l1 => //= g gs IH l2; rewrite IH -andbA//.
    move=> F l1; elim: l1 => //=x xs IH l1; rewrite IH//.
    move=> F l1; elim: l1 => //=_ xs->//.
    move=>l; elim: l => //=g gs->//.
  Defined.
End alts.

Section goals.
  Fixpoint append_goals l1 l2 := 
    match l1 with
    | no_goals => l2
    | more_goals hd tl => more_goals hd (append_goals tl l2)
    end.

  Fixpoint all_goals p l :=
    match l with
    | no_goals => true
    | more_goals hd tl => p hd && all_goals p tl
    end.

  Fixpoint size_goals l1 := 
    match l1 with
    | no_goals => 0
    | more_goals _ l1 => (size_goals l1).+1
    end.

  Fixpoint take_goals n l1 :=
    match n, l1 with
    | 0, _ | _, no_goals => no_goals
    | n.+1, more_goals x l => more_goals x (take_goals n l)
    end.

  Fixpoint drop_goals n l1 :=
    match n, l1 with
    | 0, l | _, (no_goals as l) => l
    | n.+1, more_goals _ l => drop_goals n l
    end.

  Definition behead_goals l :=
    match l with
    | no_goals => no_goals
    | more_goals _ l => l
    end.

  Fixpoint suffix_goals l1 l2 :=
    if l1 == l2 then true
    else 
    match l2 with
    | no_goals => false
    | more_goals x xs => suffix_goals l1 xs
    end.

  Fixpoint mapG F l :=
    match l with
    | no_goals => no_goals
    | more_goals x xs => more_goals (F x) (mapG F xs)
    end.

  Lemma suffixPG s1 s2: reflect (exists s2', s2 = append_goals s2' s1) (suffix_goals s1 s2).
  Proof.
    elim: s2 s1 => //=.
      move=>[|g gs]; constructor.
        by exists no_goals.
      by move=>[]-[]//.
    move=> g gs IH s1.
    case: ifP.
      move=>/eqbPG->; constructor; exists no_goals => //.
    move=>/eqP H.
    have [H1|H1] := IH s1; constructor.
      case: H1 => x->; exists (more_goals g x) => //.
    move=> [x H2]; apply: H1.
    case: x H2 => [|x xs]/=.
      by move=>?; subst.
    move=>[_->]; exists xs => //.
  Qed.

  Lemma catAG x y z: append_goals x (append_goals y z) = append_goals (append_goals x y) z.
  Proof. elim: x y z => //= x xs IH y z; rewrite IH//. Qed.

  Lemma cats0G l: append_goals l no_goals = l.
  Proof. elim: l => //= x xs ->//. Qed.  

  Lemma size_cat_goal xs ys:
    size_goals (append_goals xs ys) = (size_goals xs) + (size_goals ys).
  Proof. elim: xs ys => //= _ xs IH ys; rewrite IH; lia. Qed.

  Lemma suffix_catlG s1 s2 s3 s3':
    size_goals s3 = size_goals s3' ->
    suffix_goals (append_goals s1 s3) (append_goals s2 s3') = (s3 == s3') && suffix_goals s1 s2.
  Proof.
    elim: s3 s3' s1 s2 => //=.
      move=>[]//= s1 s2; rewrite !cats0G//.
    move=> g gs IH []//=y ys s1 s2 [H1].
    have:= IH _ _ _ H1.
    case: eqP => /=.
      move=>?; subst.
  Admitted.

  Fixpoint memG e l := 
    match l with
    | no_goals => false
    | more_goals x xs => (e == x) || memG e xs
    end.    

  #[refine] Global Instance IsList_goals : @IsList G goals :=
    {| nilC := no_goals; consC := more_goals; map:= mapG;
        appendC := append_goals; size := size_goals; take:= take_goals; drop := drop_goals;
        behead := behead_goals; suffix := suffix_goals; eqB x y := x == y; all:= all_goals;
        mem := memG |}.
  Proof.
    all: try by move=>//.
    move=> n; elim: n =>// n IH []//=g gs; rewrite IH//.
    move=> l1; elim: l1 => //= x xs->//.
    move=> l1; elim: l1 => //=x xs IH l2 l3; rewrite IH//.
    move=> l1; elim: l1 => //=x xs IH l2 l3; rewrite IH//.
    move=> l; elim: l => //.
    move=> l; elim: l => //=x xs->//.
    move=> l; elim: l => //=x xs->//.
    move=> n; elim: n => //.
    move=> n; elim: n => //.
    move=> n; elim: n => //.
    apply: eqbPG.
    move=> l1; elim: l1 => //= _ x IH l2; rewrite IH; lia.
    move=> xs; elim: xs => //=x xs H; rewrite eqxx//.
    move=> ++zs; elim: zs => //=x xs IH ys zs; case: ifP => // _; apply: IH.
    move=> n; elim: n => [|n IH] []//=g xs ys []/IH->//.
    move=> n; elim: n => [|n IH][]//= _ xs ys []/IH->//.
    apply: suffixPG.
    move=>s1 s2 /suffixPG [x ->]; rewrite size_cat_goal; lia.
    apply: suffix_catlG.
    move=> p l1; elim: l1 => //= g gs IH l2; rewrite IH -andbA//.
    move=> F l1; elim: l1 => //=x xs IH l1; rewrite IH//.
    move=> F l1; elim: l1 => //=_ xs->//.
    move=> l; elim: l => //=x xs->//.
  Defined.
End goals.


Ltac fConsA x xs := change (more_alt x xs) with (consC x xs).
Ltac fConsG x xs := change (more_goals x xs) with (consC x xs).
Ltac fNilA := change no_alt with (@nilC _ _ IsList_alts).
Ltac fNilG := change no_goals with nilC.

(* Elpi Tactic fold_goal.
Elpi Accumulate lp:{{
  solve (goal _ _ Gty _ _ as R) Y :- 
    % refine Gty R Y,
    (pi x y\ sizecopy {{more_alt lp:x lp:y}} {{@consC lp:X lp:Y lp:Z lp:x lp:y}}) ==>
    copy Gty Z,
    coq.say {coq.term->string Gty},
    coq.say {coq.term->string Z},
    % std.spy!(refine Z R Y),
    true
    .
}}. *)

Lemma cat_right_same {l1 l2} (l3:alts): 
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof.
  elim: l1 l2 l3 => //.
    move=>[]//x xs l3/=.
    fConsA x xs; fNilA.
    rewrite cat0s => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite size_cons size_cat; lia.
  move=> x xs IH [|y ys]//l3; fNilA.
    fConsA x xs => H.
    have:= f_equal size H.
    move=> /(_ _ IsList_alts).
    rewrite cat_cons size_cons !size_cat size_nil; lia.
  move=>[<-]/IH->//.
Qed.


Definition if_cut F g :=
  match g with
  | cut a => F a
  | _ => true
  end.

Definition apply_cut F g :=
  match g with
  | cut a => cut (F a) 
  | _ => g
  end.


Definition add_ca alts a :=
  match a with
  | cut a1 => cut (a1 ++ alts)
  | call pr t => call pr t
  end.

Fixpoint add_ca_deep (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, add_ca_deep_goals bt xs) ::: (add_ca_deep bt tl)
  end
with add_ca_deep_goals bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (add_ca_deep_g bt hd) ::: (add_ca_deep_goals bt tl)
  end
with add_ca_deep_g bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut ((add_ca_deep bt ca) ++ bt)
  end.

Definition save_goals (a: alts) (gs b:goals) := map (add_ca a) b ++ gs.

Definition save_alts (a : alts) (gs: goals) (bs : alts) := 
  map (fun '((s,x): Sigma * goals) => (s, save_goals a gs x)) bs.

Definition empty_ca_G g :=
  match g with call _ _ | cut no_alt => true | _ => false end.
Definition empty_caG goals := all empty_ca_G goals.
Definition empty_ca alts := all (fun x => empty_caG (snd x)) alts.

Definition a2g p A :=
  match A with
  | ACut => cut nilC
  | ACall t => call p t
  end.

Fixpoint a2gs p (b: seq A) := 
  match b with
  | nil => nilC
  | x::xs => (a2g p x) ::: (a2gs p xs)
  end.

Fixpoint aa2gs p (b: (seq (Sigma * R))) := 
  match b with
  | nil => nilC
  | x::xs => (x.1, a2gs p x.2.(premises)) ::: (aa2gs p xs)
  end.

Definition a2gs1 p (b : Sigma * R) :=
  a2gs p b.2.(premises).

Section Nur.

Variable u : Unif.

Inductive nur : Sigma -> goals ->  alts -> Sigma -> alts -> Prop :=
| StopE s a : nur s nilC a s a
| CutE s s1 a ca r gl : nur s gl ca s1 r -> nur s ((cut ca) ::: gl) a s1 r
| CallE p s s1 a b bs gl r t : 
  F u p t s = [:: b & bs ] -> 
    nur b.1 (save_goals a gl (a2gs1 p b)) (save_alts a gl ((aa2gs p) bs) ++ a) s1 r -> 
      nur s ((call p t) ::: gl) a s1 r
| FailE p s s1 s2 t gl a al r : 
  F u p t s = [::] -> nur s1 a al s2 r -> nur s ((call p t) ::: gl) ((s1, a) ::: al) s2 r.

Lemma nur_consistent {s G x xs1 xs2 s1 s2} :
  nur s G x s1 xs1 -> nur s G x s2 xs2 -> xs1 = xs2 /\ s1 = s2.
Proof.
  move=> H; elim: H xs2 s2 => //; clear.
  - inversion 1 => //.
  - move=> p s a ca r gl H IH xs2.
    by inversion 1; subst; auto.
  - move=> p s s1 a b bs gl r t H H1 IH xs2 s2 H2.
    apply: IH.
    inversion H2; subst; move: H9; rewrite H => //-[??]; subst.
    apply: H10.
  - move=> p1 s s1 s2 t gl a al r H H1 IH xs2 s3 H2.
    apply: IH.
    inversion H2; subst => //.
    congruence.
Qed.

End Nur. 
Definition get_ca g :=
  match g with
  | cut a => a 
  | _ => nilC
  end.

Definition is_cutb' A := match A with cut _ => true | _ => false end.
Definition cuts' A := all is_cutb' A.

Lemma cuts_cat {x y} : cuts' (x ++ y) = cuts' x && cuts' y.
Proof. rewrite/cuts' all_cat//. Qed.

Lemma add_ca_empty1 l: add_ca nilC l = l.
Proof. case: l => //= l1; rewrite cats0//. Qed.

Lemma cut_add_ca {l x}: is_cutb' (add_ca l x) = is_cutb' x.
Proof. case: x => //=*. Qed.

Definition make_lB0 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, x ++ lB0)) xs.

Definition make_lB01 (xs:alts) (lB0: goals) := map (fun '(s,x) => (s, lB0 ++ x)) xs.

Fixpoint add_deep (bt: alts) (l: goals) (A : alts) : alts :=
  match A with
  | no_alt => nilC
  | more_alt (s,hd) tl => (s,add_deepG bt l hd) ::: (add_deep bt l tl)
  end
  with add_deepG (bt: alts) (l: goals) (A : goals) :=
  match A with
  | no_goals => nilC
  | more_goals hd tl => (add_deep_G bt l hd) ::: (add_deepG bt l tl)
  end
  with add_deep_G bt l A :=
  match A with
  | cut ca => 
    let s := size ca - size bt in
    let xx := (add_deep bt l (ca)) in
    cut (make_lB0 (take s xx) l ++ drop s ca)
  | call pr t => call pr t 
  end.

Definition kill (A: goals) := map (apply_cut (fun x => nilC)) A.

  (* bt is the backtracking list for the cut-alternatives
    this list is important since in this tree:
          or   
        /  \  
        or   K 
      /  \    
      !    J   
    K is in bt but not J, i.e. we have to consider two different levels:
    the "siblings" on the right of a cut are NOT alternatives
    the "great^n uncles" on the right of a cut ARE alternatives
  *)

Fixpoint state_to_list (A: state) s (bt : alts) : alts :=
match A with
| OK => (s, nilC) ::: nilC
| Top => (s, nilC) ::: nilC
| Bot => nilC
| Dead => nilC
| CutS => (s, ((cut nilC) ::: nilC)) ::: nilC
| CallS pr t => (s, ((call pr t) ::: nilC)) ::: nilC
| Or A s1 B => 
  let lB := state_to_list B s1 nilC in
  let lA := state_to_list A s lB in
  add_ca_deep bt (lA ++ lB)
| And A B0 B =>
  let lB0 := state_to_list B0 s bt in
  let lA   := state_to_list A s bt in
  if lA is more_alt (slA, x) xs then 
    (* lA is split into the current goal x and the future alternatives xs *)
    (* in a valid state lB0 has length 0 or 1 (it is a (potentially killed) base and) *)
    match lB0 with
    | no_alt => 
      (* the reset point is empty: it kill all the alternatives in the cut-to *)
      let lB   := state_to_list B slA bt in
      make_lB01 lB (kill x)
    | more_alt (sB0,hd) no_alt =>
      (* the reset point exists, it has to be added to all cut-to alternatives *)
      let xz := add_deepG bt hd x in
      let xs := add_deep bt hd xs in 
      (* each alt in xs must have hd has rightmost conjunct  *)
      let xs := make_lB0 xs hd in
      (* xs are alternatives that should be added in the deep cuts in B *)
      let lB   := state_to_list B slA (xs ++ bt) in
      (* lB are alternatives, each of them have x has head *)
      (make_lB01 lB xz) ++ xs
    | _ => nilC (*unreachable in a valid_state*)
    end
  else nilC
end.

(* Definition empty_sig : sigT := fun _ => b(d Func).

Definition empty_prog := {|
    modes := (fix rec (t : Tm) := match t with Comb h _ => o :: rec h | Code _ | Data _ => [::] end);
    sig := empty_sig;
    rules := [::];
|}.

Fixpoint list_to_state (l: alts) : state :=
  match l with
  | no_alt => Bot
  | more_alt x no_alt => 
    let l := goals_to_state x.2 Bot in
    Or Bot x.1 l
  | more_alt x (more_alt y ys as t) => 
    let t := goals_to_state x.2 (list_to_state t) in
    Or Bot x.1 t
  end
with goals_to_state (l:goals) t: (state):=
  match l with
  | no_goals => (Or Top empty t)
  | more_goals x xs => 
    let '(l, rr) := goal_to_state x t in
    let r := goals_to_state xs t  in
    match rr with
    | Some _ => 
      (* let spref := list_to_state pref in
      let ssuff := list_to_state suff in *)
      (r)
    | None => 
      (And l r r)
    end
  end
with goal_to_state (l:G) (t:state) :=
  match l with
  | call pr tm => (CallS pr tm, None)
  | cut ca => 
      (* let s := size t - size ca in *)
      (* (CutS, None) *)
      (CutS, Some ((list_to_state ca), ca))
  end
. *)

Global Notation "-nilCG" :=
  (@nilC _ _ IsList_goals)
  (at level 2, no associativity, only parsing)
  : SE.
Global Notation "-nilCA" :=
  (@nilC _ _ IsList_alts)
  (at level 2, no associativity, only parsing)
  : SE.

Section test.
  Variable u : Unif.
  Variable s1 : Sigma.
  Variable p : program.
  Variable sx : Sigma.
  Variable p1 : program.
  Notation g := (And (Or OK s1 CutS) CutS OK).
  Goal next_alt (Some sx) g = Some (s1, And (Or Dead s1 CutS) CutS CutS).
  Proof. move => //=. Qed.
  Goal clean_success g = And (Or OK s1 CutS) CutS Bot.
  Proof. move => //=. Qed.

  Goal valid_state ((And (Or OK s1 CutS) CutS Bot)).
  Proof. move=> //=. Abort.
  Goal valid_state ((And (Or Dead s1 CutS) CutS CutS)).
  Proof. move=> //=. Abort.

  Goal forall s3 l,
    state_to_list (And (Or OK s1 CutS) CutS Bot) s3 l = 
      state_to_list (And (Or Dead s1 CutS) CutS CutS) s3 l.
  Proof.
    move=>s3 l/=.
    rewrite /=!cat0s ?cat0s.
    rewrite subnn take0 drop0//.
  Qed.
End test.

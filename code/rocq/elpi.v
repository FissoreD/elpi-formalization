From mathcomp Require Import all_ssreflect.
From det Require Import lang valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

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

  Lemma cats20 {T: Type} {X Y : list T}: X ++ Y = [::] -> X = [::] /\ Y = [::].
  Proof. by destruct X. Qed.

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

  Lemma map_cats0 {T : Type} (g:list (list T)): map (fun x => x ++ [::]) g = g.
  Proof. elim: g => //=x xs->; rewrite cats0//. Qed.

  Lemma map_cats_same {T : Type} (X Y:list (list T)) hd: 
    X = Y -> [seq x ++ hd | x <- X] = [seq x ++ hd | x <- Y].
  Proof.
    move=>->//.
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

Module Nur (U : Unif).

  Module VS := valid_state(U).
  Import VS RunP Run Language.
  
  Inductive G := 
    | call : program -> Tm -> G
    | cut : list (list G) -> G
    .

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

  derive G.
  HB.instance Definition _ := hasDecEq.Build G G_eqb_OK.

  Definition alt := (list G).

  Definition a2g p A :=
    match A with
    | Cut => cut [::]
    | Call t => call p t
    end.

  Definition a2gs p (b : Sigma * R) :=
    map (a2g p) b.2.(premises).

  Section add_ca.

    Definition add_ca alts a :=
      match a with
      | cut a1 => cut (a1 ++ alts)
      | call pr t => call pr t
      end.

    Lemma add_ca_empty {lA}:
      map (add_ca [::]) lA = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs IH.
      rewrite IH; case: x => // l; rewrite cats0//if_same//.
    Qed.

    Lemma map_add0_cas_empty {lA}:
      map (map (add_ca [::])) lA  = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs ->.
      f_equal; apply add_ca_empty.
    Qed.
  End add_ca.


  Definition save_alt a gs b := map (add_ca a) b ++ gs.
  Definition more_alt a bs gs := map (save_alt a gs) bs ++ a.

  Inductive nur : Sigma -> list G ->  list alt -> Sigma -> list alt -> Prop :=
  | StopE s a : nur s [::] a s a
  | CutE s s1 a ca r gl : nur s gl ca s1 r -> nur s [:: cut ca & gl] a s1 r
  | CallE p s s1 a b bs gl r t : 
    F p t s = [:: b & bs ] -> 
      nur s (save_alt a (a2gs p b) gl) (more_alt a (map (a2gs p) bs) gl) s1 r -> 
        nur s [::call p t & gl] a s1 r
  | FailE p s s1 t gl a al r : 
    F p t s = [::] -> nur s a al s1 r -> nur s [::call p t & gl] (a :: al) s1 r.

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
    - move=> p1 s s1 t gl a al r H H1 IH xs2 s2 H2.
      apply: IH.
      inversion H2; subst => //.
      congruence.
  Qed.

  Definition get_ca g :=
    match g with
    | cut a => a 
    | _ => [::]
    end.

  Definition is_cutb' A := match A with cut _ => true | _ => false end.
  Definition cuts' A := all is_cutb' A.

  Lemma cuts_cat {x y} : cuts' (x ++ y) = cuts' x && cuts' y.
  Proof. rewrite/cuts' all_cat//. Qed.

  Fixpoint add_ca_deep n tl (alts: seq (seq G)) := (*always:= adds always alts to cut *)
    match n with
    | 0 => alts
    | n.+1 => map (map (fun x => (add_ca tl (apply_cut (add_ca_deep n tl) x)))) alts
    end.

  (* Definition add_ca1 tl a := add_ca_deep (size a) tl a. *)

  Lemma add_ca_empty1 l: add_ca [::] l = l.
  Proof. case: l => //= l1; rewrite cats0//. Qed.

  Lemma map_add1_cas_empty {T: Type} (lA: (list T)) F:
    (map (fun x => add_ca [::] (F x))) lA  = (map F) lA.
  Proof.
    rewrite /add_ca; elim: lA => //= x xs ->.
    case: (F x)=>//=l; rewrite cats0//.
  Qed.


  Lemma map_map_add1_cas_empty {T: Type} (lA: list (list T)) F:
    map (map (fun x => add_ca [::] (F x))) lA  = map (map F) lA.
  Proof.
    rewrite /add_ca; elim: lA => //= x xs ->.
    f_equal; apply: map_add1_cas_empty.
  Qed.

  Lemma cut_add_ca {l x}: is_cutb' (add_ca l x) = is_cutb' x.
  Proof. case: x => //=*. Qed.

  Lemma cuts_add_ca {x l} : cuts' [seq add_ca l j | j <- x] = cuts' x.
  Proof. elim: x l => // x xs H/= l; rewrite H cut_add_ca//. Qed.

  Definition make_lB0 (xs:seq alt) (lB0: alt) := map (fun x => x ++ lB0) xs.

  Definition add_deep_help add_deep (bt:seq alt) (n:nat) hd :=
    apply_cut (fun x =>
      let s := size x - size bt in
      make_lB0 (add_deep bt n hd (take s x)) hd ++ drop s x).

  Fixpoint add_deep bt n (l: alt) (A: seq alt) :=
    match n with
    | 0 => A
    | n.+1 =>
      map (map (add_deep_help add_deep bt n l)) A
    end. 

  Definition add_deep_ bt n (l: alt) (A: alt) :=
    match n with
    | 0 => A
    | n.+1 => (map (add_deep_help add_deep bt n l)) A
    end.

  Definition kill (A: alt) := map (apply_cut (fun x => [::])) A.


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

  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
    | OK => [::[::]]
    | Top => [::[::]]
    | Bot => [::]
    | Dead => [::]
    | Goal _ Cut => [::[::cut [::]]]
    | Goal pr (Call t) => [::[::call pr t]]
    | Or A _ B => 
      let lB := state_to_list B [::] in
      let lA := state_to_list A lB in
      add_ca_deep (size (lA ++ lB)) bt (lA ++ lB)
    | And A B0 B =>
      let lB0 := state_to_list B0 bt in
      let lA   := state_to_list A bt in
      if lA is x :: xs then 
        (* lA is split into the current goal x and the future alternatives xs *)
        (* in a valid state lB0 has length 0 or 1 (it is a (potentially killed) base and) *)
        match lB0 with
        | [::] => 
          (* the reset point is empty: it kill all the alternatives in the cut-to *)
          let lB   := state_to_list B bt in
          [seq (kill x) ++ y | y <- lB]
        | [::hd] =>
        (* 
          invariant every cut-to has bt has tail or is empty
        *)
          (* the reset point exists, it has to be added to all cut-to alternatives *)
          let x := add_deep_ bt (size xs).+1 hd x in
          let xs := add_deep bt (size xs) hd xs in 
          (* each alt in xs must have hd has rightmost conjunct  *)
          let xs := make_lB0 xs hd in
          (* xs are alternatives that should be added in the deep cuts in B *)
          let lB   := state_to_list B (xs ++ bt) in
          (* lB are alternatives, each of them have x has head *)
          [seq x ++ y | y <- lB] ++ xs
        | _ => [::] (*unreachable in a valid_state*)
        end
      else [::]
    end.
End Nur.

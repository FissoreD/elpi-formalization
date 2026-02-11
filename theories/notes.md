# Status quo = Elpi Run and Nur

- [The language: lang.v](#the-language-langv)
- [The interpreter: runT.v](#the-interpreter-runv)
  - [Useful lemmas](#useful-lemmas)
- [Tests: runT\_test.v](#tests-run_testv)
- [Properties of runT: runT\_prop.v](#properties-of-runT-run_propv)
- [Determinacy checking: check.v](#determinacy-checking-checkv)
- [Valid tree: valid\_tree.v](#valid-tree-valid_treev)
- [Elpi interpreter: elpi.v](#elpi-interpreter-elpiv)
  - [Tree\_to\_list](#tree_to_list)
    - [Important lemmas](#important-lemmas)
  - [Valid list](#valid-list)
- [Tree to list tests: elpi\_test.v](#tree-to-list-tests-elpi_testv)
- [Semantics equivalence](#semantics-equivalence)
- [Add\_ca\_deep:](#add_ca_deep)
- [Add\_deep](#add_deep)


## The language: lang.v

This file describes the Elpi language in tree-like operational semantics.

The main inductives of the language are:

- term (`Tm`): A term is either a term constructors `Data` (representing lists,
  natural numbers, etc.), which carry an integer as a unique identifier.
  Predicates are defined with `Code` and represent either variables `v` or
  predicates `p`. (In the future, we might remove `Code` and expose `v` and `p`
  directly in the type `Tm`). A call is binary and is represented by the `Comb`
  constructor.
- atom (`A`): An atom is either a cut or a call. A call contains a term `Tm`.
- rule (`R`): A rule is a record containing a head of type `Tm` and a body,
  which is a list of atoms.
  > Note: A rule always contains goals in conjunction. This is an important
  > property of a "valid tree."
- substitution (`Sigma`): A function mapping variable identifiers to terms.
- program (`program`): A record consisting of a list of rules, modes, and
  signatures (the last two fields are not relevant for now).

> Note: A query is a term.

## The interpreter: runT.v

The interpreter is a functor that takes a module of type **Unif** as input.
Every file working with the interpreter is also a functor expecting **Unif** as
input. This strategy allows us to provide unification on the fly when needed
during tests (e.g., in `run_test.v`). Moreover, in a real-world scenario, we can
assume the user may provide their own unification procedure, which may or may
not accept the pattern-fragment or non-pattern fragment unification (i.e.,
non-decidable choices). **Unif** requires two functions to be implemented:
`unify` for unifying output terms and `matching` for input terms.

The function **F** is responsible for finding the rules applicable to a query.
It works in tandem with the functions **select** and **H**: the former filters
rules based on their head, while the latter tests whether the head of a given
rule unifies with the current query.

We represent a tree in a tree-like structure using the `tree` inductive.

```coq
Inductive tree :=
  (* concrete base cases *)
  | KO : tree (* the fail predicate *)
  | Top : tree (* the true predicate *)
  | Goal : program -> A -> tree (* an atom to be runT in a program *)

  (* meta-level atoms *)
  | OK : tree    (* a meta tree identifying an explored and successful tree *)
  | Dead : tree  (* a meta tree identifying an explored and failed tree *)

  (* recursive cases *)
  | Or  : tree -> Sigma -> tree -> tree  (* Or A s B := A is lhs, B is rhs, s is the subst from which to launch B *)
  | And : tree -> tree -> tree -> tree. (* And A B0 B := A is lhs, B is rhs, B0 is used to reset B for backtracking *)
```

> Note: The program stored in the goal is currently redundant. In a valid tree,
> all goals should point to the same program. However, in the context of adding
> the implication constructor, we could imagine the program dynamically
> changing.


The evolution of a tree is achieved through small-step semantics. We define
three functions and four inductives to animate a program. Specifically:

- **step_res**:
    ```coq
    Inductive step_res :=
    | Expanded    of Sigma & tree
    | CutBrothers of Sigma & tree
    | Failed     of tree
    | Success     of Sigma & tree.
    ```
  This inductive indicates whether a tree evolution succeeds, fails, resolves
  a cut, or processes a non-cut query. It is used by the small-step semantics.

- **step**: This function is the core of the interpreter. It takes a tree
  and a substitution, steping the current tree. If the tree is a meta-level
  tree, it returns either a success with the input substitution and tree or a
  failure with the current tree. If the tree is a concrete base case, it
  returns either `Expanded` or `CutBrother`.
  > Note: In the case of a call, the function returns a new tree where the
  goal is replaced by a disjunction of the bodies of all rules the can be
  used on the current query. The **F** function is used to retrieve these clauses.

  The shape of this expansion is as follows:

  $$\bot \lor_{s1} (r_{11} \land r_{12} \land ... \land r_{1x} \land \top)
  \lor_{s2} (r_{21} \land r_{22} \land ... \land r_{2y} \land \top)
  \lor_{s3} \dots \lor_{sm} (r_{m1} \land r_{m2} \land ... \land r_{mz}
  \land \top)$$

  For a query $q$ with $m$ rules having unifying heads, the disjunction consists
  of $m+1$ disjuncts. The first is $\bot$, and the subsequent disjuncts contain
  the conjunctions of the premises of each rule, ending with $\top$. Each
  disjunct, except the first, stores the substitution for launching the premises
  in the immediately superior `Or` node. For example, the first rule uses the
  substitution $s_1$. Reset points in the $\land$ nodes are implicitly equal to
  their right-hand side. For instance, the reset point of the first `And` is
  $r_{12} \land ... \land r_{1x}$. Reset points currently have no role but will
  be explained in the `next_alt` procedure.

  The expansion for the `Or` tree checks if the left-hand side is dead (i.e.,
  the tree has been fully explored with failure). If so, it steps the right-
  hand side of the `Or` with the substitution written in it. Otherwise, it
  explores the left-hand side. Note that within an `Or` node, a **CutBrother**
  is never returned as `step_res`. This is because cuts cannot escape an `Or`
  in our language; they are compartmentalized within `And`. If the expansion of
  the left-hand side returns a cut, the right-hand side is **hard-cut** away.
  Hard-cutting replaces all nodes (including reset points in the `And`) with
  the `KO` tree.

  The expansion for the `And` node first steps the left-hand side. If it
  resolves successfully, it then steps the right-hand side. If the left-hand
  side succeeds and the right-hand side turns into a **CutBrother**, the left-
  hand side is **soft-cut** away. Soft-cutting replaces all non-meta-level
  atoms with `KO`.

- **exp_res**: This is essentially an enhanced boolean indicating whether the
  execution of a query will eventually succeed or fail (both cases refer to
  outputs without backtracking).

- **expandedb**: This inductive iterates over the `step` function until it
  reaches either a **Failed** or a **Success**. The last argument of `expandedb`
  is a bool indicating
  whether, during the resolution of the query, there is a superficial cut (i.e.,
  a cut whose effect should be visible outside the current tree).

- **runT**: This inductive represents the interpreter of our language. It
  iterates over **expandedb** until reaching a success. If **expandedb** results
  in a failure, it backtracks and continues calling **expandedb**.

- **next_alt**: Backtracking is enabled by the `next_alt` procedure. It takes a
  tree and erases (i.e., replaces with `Dead`) the internal nodes representing
  a previous failure. It also returns the substitution for launching the new
  tree within **runT**. `next_alt` is implemented with knowledge of how
  `step` works, choosing which atoms to keep or erase based on their status
  (e.g., `is_dead` or `failed`).
   > Note 1: The function can be significantly simplified under the assumption
   > that the input tree is valid. However, since we want our interpreter to
   > behave correctly in any tree, the function is more complex.

   > Note 2: In `next_alt`, the reset point stored inside the $\land$ nodes is
   > used. When a subtree in the left-hand side of a conjunction is killed,
   > the new left-hand side is launched with the reset point. For example, in
   > the following program:
   ```prolog
   p :- q X, r X.
   q 1.
   q 2.
   r 2.
   ```
   > Given the initial query $p$, running with an empty substitution produces
   > the tree: $\bot \lor_\varnothing (q\ X \land_{r X} r\ X)$    
   > Then $DEAD \lor_\varnothing (q\ X \land_{r X} r\ X)$ (backtracking on
   > $\bot$, substitution is empty).  
   > Then $DEAD \lor_\varnothing ((\bot \lor_{X=1} \top \lor_{X=2} \top)
   > \land_{r X} r\ X)$ (expansion of $q\ X$, substitution is empty).  
   > Then $DEAD \lor_\varnothing ((DEAD \lor_{X=1} \top \lor_{X=2} \top)
   > \land_{r X} r\ X)$ (backtracking on $\bot$, substitution is $X=1$).  
   > Then $DEAD \lor_\varnothing ((DEAD \lor \top \lor_{X=2} \top)
   > \land_{r X} \bot)$ (no solution for $r\ 1$).  
   > Then $DEAD \lor_\varnothing ((DEAD \lor_{X=1} DEAD \lor_{X=2} \top)
   > \land_{r X} r\ X)$ (backtracking discards the first $\top$, since it causes a
   > failure, and it resets the right-hand side of the `And`, substitution is
   > $X=2$).  
   > Then $DEAD \lor_\varnothing ((DEAD \lor_{X=1} DEAD \lor_{X=2} \top)
   > \land_{r X} \top)$ (success with substitution $X=2$).  
   > Finally, the tree $DEAD \lor_\varnothing ((DEAD \lor_{X=1} DEAD
   > \lor_{X=2} \top) \land_{r X} \bot)$ is returned after calling
   > `clean_success`.

- **clean_success**: This function is used by **runT**. If the interpretation
  of a tree succeeds, the returned tree is cleaned of its successful path.

### Useful lemmas
Beside these functions/inductives definitions, we provide some properties
that can be derived.
The more interesting and used are:

- the small lemmas in the section `tree_op` relating the success, failed,
  is_dead, cutr and cutl functions. (The is_ko definition is no longer useful,
  it should be cleaned up in a future version)
- `step_success : step s1 A = Success s2 B -> ((s1 = s2) * (A = B))%type.`
- `step_solved_success : step s1 A = Success s2 B -> (success A * success B)%type.` (*which can only return the first projection, due to the previous lemma*)
- `step_not_dead : is_dead A = false -> step s A = r -> is_dead (get_tree r) = false`
- `step_failure_failed : step s1 A = Failed B -> (failed A * failed B)%type.`
-  `failed_step : failed A -> step s1 A = Failed A.`
-  `next_alt_none : next_alt s1 A = None -> forall s2, next_alt s2 A = None.`
- `next_alt_some : next_alt s1 A = Some (s2, B) -> (forall s3, exists s4, next_alt s3 A = Some (s4, B)).`

> Note: the key of the interpretation of a query is of course the substitution,
> we haven't really pay lot of attention of it, but looking to the code, we see
> how it flows smothly trhough every inductives and fixpoints and how it is
> updated accordingly in the natural way.

## Tests: run_test.v

This file contains tests for the execution of **runT** in a custom environment
where a Unif module is defined for simple term unification. The file is expected
to pass all tests without issues.

## Properties of runT: run_prop.v

In `run_prop`, we tree properties of the interpreter, proving that `expandedb`
and `runT` are consistent, i.e., they always produce the same outputs given the
same inputs (`expanded_consistent` and `runT_det`).

The `same_structure` postulate asserts that the structure of a tree is
preserved by `step` and `expandedb`, i.e., they maintain the structure of
`And` and `Or` nodes.

We prove `expanded_and_complete`:
```
expandedb s (And A B0 B) (Done s' C) b ->
  exists s'' A' B' b1 b2, 
    expandedb s A (Done s'' A') b1 /\ 
      expandedb s'' B (Done s' B') b2 /\ 
        b = b1 || b2`.
```

We prove `expanded_and_correct`:
```
expandedb s0 A (Done s1 B) -> 
  expandedb s1 C (Done s2 D) b ->
    expandedb s0 (And A B0 C) 
      (Done s2 (And (if b then cutl B else B) (if b then cutl B0 else B0) D)).
```

We prove `expanded_and_fail`:
```
expandedb s (And A B0 B) (Failed C) ->
  (exists C', expandedb s A (Failed C')) \/ 
    (exists s' A' B', expandedb s A (Done s' A') /\ expandedb s' B (Failed B')).
```
> TODO: Refine this proof to specify that C is `And A' B0' B'` and eliminate
> the existential quantifiers `C', A', B'`.

We prove `expanded_and_fail_left`:
```
expandedb s A (Failed FA) ->
  forall B, expandedb s (And A B0 B) (Failed (And FA B0 B)).
```

We prooe `run_and_fail_both`:
```
run_and_fail_both:
  expandedb s A (Done s' SA) -> expandedb s' B (Failed FB) b ->
      expandedb s (And A B0 B) (Failed (And (if b then cutl SA else SA) (if b then cutl B0 else B0) FB)).
```

We prove `expanded_or_correct_left`:
```
expandedb s A (Done s' A') b ->
  forall s2 B,
    expandedb s (Or A s2 B) (Done s' (Or A' s2 (if b then cutr B else B))).
```

We prove `expanded_or_complete_done`:
```
expandedb s (Or A s2 B) (Done s' (Or A' s2 B')) b ->
  (is_dead A = false /\ 
    exists b, expandedb s A (Done s' A') b /\ B' = if b then cutr B else B) \/ 
      (is_dead A /\ A = A' /\ expandedb s B (Done s' B')).
```

We prove `expanded_or_correct_left_fail`:
```
is_dead A = false ->
  expandedb s A (Failed A') b ->
    forall s2 B, 
      expandedb s (Or A s2 B) (Failed (Or A' s2 (if b then cutr B else B))).
```

## Determinacy checking: check.v

We prove `main`:
```
all_cut_followed_by_det sP sV -> det_term sP sV t ->
  is_det (Goal p (Call t)).
```

This is a simplified version of determinacy checking. It trees that in a
program where all rules of deterministic predicates include a cut followed by
calls to deterministic predicates, a query to a deterministic predicate will
produce no choice points.

```
Definition is_det A := forall s s' B,
  runT s A s' B -> forall s2, next_alt s2 B = None.
```

`is_det` asserts that running a tree `A` from a substitution `s` results in a
tree `B` with no alternatives.

> TODO: Add checks for good-calls of predicate and variable refinement.

> NOTE: In future versions, mutual exclusion on inputs will depend on
> assumptions about the `matching` procedure, as mutual exclusion strongly
> relies on `matching`.

## Valid tree: valid_tree.v

The concept of a valid tree has been introduced to model the "real" Elpi
interpreter. It defines the invariant of the `runT` procedure, i.e., the
structure of a tree preserved during goal interpretation.

A valid tree includes `Goals`, `Top`, `KO`, and `OK`. A `Dead` tree is
invalid, since a `Dead` tree is meaningless.

The tree `Or A s B` is valid if:
- `A` is dead, then `B` must be valid.
- Otherwise, `A` is valid, and `B` remains untouched. `B` must be a basic `Or`
  tree or a `bbOr` tree, which is either a disjunction of conjunctions where
  each conjunction is a `Goal`, or a disjunction of conjunctions where each
  conjunction is `KO` (to account for superficial cuts in `A` that could
  invalidate `B`).

The tree `And A B0 B` is valid if:
- `A` is valid, and:
  - If `A` is successful (i.e., it has a path to `OK`), then `B` is valid.
  - Otherwise, `B` equals `B0`, as it has not been explored yet.

Additionally, the reset point must be a basic `And` tree, or a `bbAnd` tree,
which is a conjunction of `Goals` or a conjunction of `KO`.

We prove the following properties:

- `bbAnd_valid`: `bbAnd B -> valid_tree B.`
- `bbOr_valid`: `bbOr B -> valid_tree B.`
- `valid_tree_step`: `valid_tree A -> step s A = r -> valid_tree (get_tree r).`
- `valid_tree_expanded`: `valid_tree A -> expandedb s1 A r -> valid_tree (get_tree_exp r).`
- `valid_tree_next_alt`: `valid_tree A -> next_alt s1 A = Some (s2, B) -> valid_tree B.`
- `valid_tree_clean_success`: `valid_tree A -> valid_tree (clean_success A).`
- `valid_tree_run`: `valid_tree A -> runT s1 A s2 B -> valid_tree B.`  


## Elpi interpreter: elpi.v

Elpi's interpreter employs a two-dimensional list-like data structure to
represent the tree. The first dimension tracks alternatives (i.e., choice
points created during query execution), while the second dimension represents
atoms in conjunction. The hard-cut operator stores the "cut-to" alternatives,
which act as a pointer to a suffix of the list. Upon encountering a cut, the
interpreter uses the "cut-to" as the new alternatives (i.e. some alternatives
are thrown away).

To represent this interpreter, we define a basic datatype for the language's
atoms. The atom type in `lang.v` cannot be reused because `cut` is ad-hoc in
this representation.

```coq
Inductive G :=
  | call : program -> Tm -> G
  | cut : list (list G) -> G.
```

The translation of a tree atom (`A`) to a list atom (`G`) is defined as follows:
```coq
Definition a2g p A :=
  match A with
  | Cut => cut [::]
  | Call t => call p t
  end.
```

The interpreter is defined as:
```coq
Inductive runE : Sigma -> list G -> list alt -> Sigma -> list alt -> Prop :=
| StopE s a : runE s [::] a s a
| CutE s s1 a ca r gl : runE s gl ca s1 r -> runE s [:: cut ca & gl] a s1 r
| CallE p s s1 a b bs gl r t :
    F p t s = [:: b & bs ] ->
    runE s (save_alt a (a2gs p b) gl) (more_alt a (map (a2gs p) bs) gl) s1 r ->
    runE s [::call p t & gl] a s1 r
| BackE p s s1 t gl a al r :
    F p t s = [::] -> runE s a al s1 r -> runE s [::call p t & gl] (a :: al) s1 r.
```
> TODO: *The substitutions are incorrect; they should be stored in the
disjuncts.*

```coq
Definition add_ca alts a :=
  match a with
  | cut a1 => cut (a1 ++ alts)
  | call pr t => call pr t
  end.
Definition save_alt a gs b := map (add_ca a) b ++ gs.
Definition more_alt a bs gs := map (save_alt a gs) bs ++ a.
```

The interesting case in `CallE` involves finding the rules applicable to a term `t` in
a program `p`. Since the term and program types originate from `lang`, we reuse
`F` to find these rules. The list of goals is then updated using auxiliary
functions `add_ca`, `save_alt`, and `more_alt`.

### Tree_to_list

To reuse proofs for determinacy checking on the tree-like `tree` for the list
representation, we provide a translation from a `tree` to a `list (list G)`.
This translation is implemented using the fixpoint `tree_to_list`:

```coq
Inductive G' :=
| call' : program -> Tm -> G'
| cut' : bool -> list (list G') -> G'.

Fixpoint tree_to_list_aux A bt :=
  match A with
  | OK => [::[::]]
  | Top => [::[::]]
  | KO => [::]
  | Dead => [::]
  | Goal _ Cut => [::[::cut' false [::]]]
  | Goal pr (Call t) => [::[::call' pr t]]
  | Or A _ B => 
    let lB := tree_to_list_aux B [::] in
    let lA := tree_to_list_aux A lB in
    (* here we are adding bt to lA. In the example above J in not in bt  *)
    (* since bt are at least grand-parents alts, then we force the insertion 
        in the cuts of lA *)
    incr_cuts (map (map (add_ca true bt)) (lA ++ lB))
  | And A B0 B =>
    let lA   := tree_to_list_aux A bt in
    let lB   := tree_to_list_aux B bt in
    let lB0 := tree_to_list_aux B0 bt in
    if lA is x :: xs then add_alt x xs lB0 lB
    else [::]
  end.
```

The function takes a tree and a list of alternatives (`bt` for backtrack
points), which are used to construct the "cut-to" in `Or` nodes. Initially,
`bt` is an empty list.

The `OK` and `Top` nodes represent future success in `runT`, so they are
collapsed into `[::[::]]`, corresponding to success in the list semantics.
Similarly, `Dead` and `KO` represent future failures and are translated into
an empty list.

To distinguish superficial cuts from deep cuts (i.e., cuts whose effects are
visible or not outside), we introduce a temporary `G'` inductive carrying a
boolean on the cut node. This boolean indicates whether the cut is deep. For
example, in the tree `((! \/ A) /\ !) \/ C`, the first cut is deep for `C`.

Graphically:
```
      ∨        1
     / \
    ∧   C      2 
   / \
  ∨   !        3
 / \
!   A          4
```

In the graph, the level difference between the first cut and `C` is >= 2;
therefore, the "cut-to" alternatives of the first cut point to `C`. However,
this cut discards `A` because their level difference is < 2. Similarly, the
second cut discards `C` because their level difference is < 2.

When translating a goal or a cut, we naturally translate it to the `G'` type,
fixing the cut level to `false` (superficial) with empty cut alternatives.

The translation of the tree `Or A _ B` involves translating `B` with an empty
`bt` list to obtain `lB`, and `A` with `lB` as the `bt` list to obtain `lA`. `B`
serves as a potential choice point for all deep cuts inside `A`, while `A` does
not create choice points for `B`. Finally, `bt` is added to all cuts inside `lA
++ lB`. After this step, all the boolean in the cut are change to tree, since 
the cut inside a or become deep.

> TODO: Consider substitutions in the translation of `Or` trees.

```coq
Definition add_deep_help add_deep (n:nat) l :=
  (apply_cut (fun x => map (fun x => x ++ l) ((add_deep n l) x))).

Fixpoint add_deep n (l: alt') (A: seq alt') :=
  match n with
  | 0 => A
  | n.+1 =>
    map (map (add_deep_help add_deep n l)) A
  end. 

Definition ad l As := (add_deep (size As) l) (As).

(* Add alternatives only to deep cuts. *)
Definition make_lB lB tl := map (map (add_ca false tl)) lB.

Definition make_lB0 (xs:seq alt') (lB0: alt') := map (fun x => x ++ lB0) xs.

Definition add_alt (x: alt') (xs lB0 lB:list alt') : list alt' :=
  match lB0 with
  (* In a valid tree, lB0 is either cut away (length 0) or a base_and (length 1). *)
  | [::hd] =>
      match ad hd (x::xs) with
      | x::xs =>
          let: tl := make_lB0 xs hd in
          let: lB := make_lB lB tl in
          [seq x ++ y | y <- lB] ++ tl
      | [::] => [::]
      end
  | [::] =>
      (* If the reset point is nil, xs are killed (append KO to all alternatives). *)
      [seq x ++ y | y <- lB]
  | _ => [::] (* Unreachable. *)
  end.
```

The translation of the tree `And A B0 B` is more complex. It starts by
translating `A`, `B0`, and `B` into `lA`, `lB`, and `lB0`, respectively. Then:
- If `lA` is `x :: xs`, and assuming a valid tree:
  - If `lB0` is empty, `tl` is killed, and only `lB` is returned.
  - Otherwise, `lB0` (length 1) is recursively added deeply inside all "cut-to"
    alternatives in `x::xs`. `lB0` is appended to all alternatives in `xs` to
    obtain `tl`.
  - `tl` is added as a new choice point to all deep cuts inside `lB`.
  - Finally, `x` is returned with the goal formed by `lB`, concatenated with
    `tl`.
- If `lA` is empty, there are no alternatives in the left-hand side of the
  conjunction, so the empty list is returned.


The function G2Gs translates objects of type G' into G. This way the
boolean in the cut' is removed. 


#### Important lemmas
We have two foundamental lemmas that should be used a lot when working with the
`add_alt` procedure. They are:

- `base_and_ko_tree_to_list: base_and_ko A -> tree_to_list_aux A l = [::]`
- `base_and_tree_to_list {A}: base_and A -> exists hd, forall l, tree_to_list_aux A l = [::hd].`

They are used to make add_alt caluclate and show that the reset point is
either an empty list or a list of length 1.

Another important lemma is:
` base_and_empty_ca: base_and A -> tree_to_list_aux A l = B -> (all empty_ca1) (seq.head [::] B).`  
saying that in conjunction of goals, all cut-to alternatives are empty


### Valid list

We define the notion of a valid list in the Elpi interpreter using the
`valid_ca` function. This function ensures that the "cut-to" alternatives
always point to a suffix in the list of alternatives. It performs a deep
traversal through all cuts in the alternatives and requires a fuel parameter.

The complete definition of a valid list is as follows:

```coq
Fixpoint all_tail {T:Type} F (l1 l2:list T) :=
  match l1 with
  | [::] => true
  | x::xs => F x (behead l2) && all_tail F xs (behead l2)
  end.

Fixpoint valid_ca_aux n L1 L2 :=
  match n with
  | 0 => true
  | n.+1 =>
    all_tail (fun xs ys => all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs) L1 L2
  end.

Definition valid_ca L := valid_ca_aux (size L) L L.
```

`all_tail` is an auxiliary higher-order function that applies its higher-order argument to
the head and tail of two lists, repeating until the first list is exhausted.
The lemmas involving `all_tail` and `valid_ca_aux` assume that `size l1 <= size
l2`.

Note that `valid_ca` operates on the `G'` type, which includes a boolean flag.
When verifying suffixes, the boolean is removed from the lists using the
`G2Gs` function.

In the rest of the file, we prove several properties relating a tree `A` and
a tree `B` that are connected through calls to `next_alt`, `step`,
`expandedb`, and similar functions.

## Tree to list tests: elpi_test.v

This file contains tests verifying the correct behavior of the `tree_to_list`
function.

## Semantics equivalence

The primary lemma we aim to prove is as follows:

```coq
Lemma runElpi A :
  forall s B s1 b,
    valid_tree A ->
    runT s A s1 B b ->
      exists x xs, tree_to_list A [::] = x :: xs /\
        runE s x xs s1 (tree_to_list B [::]).
```

The proof proceeds by induction on `runT`, addressing the cases of success and
backtracking separately. These cases are handled using auxiliary lemmas.

# WIP:

## Add_ca_deep:
This function recursively appends the `bt` alternatives to all cut-to lists. 
It is applied in the `Or` case. For instance, given `A \/ B` with `bt` as 
cut-to alternatives, we aim to ensure that every cut-to list includes `bt` 
as its tail.
As an example, consider `(A \/ B) \/ C`. In this case, `C` should be added 
to all cut-to lists of `A` and `B`.

## Add_deep
This function addresses the `And` case. It recursively appends the reset point
to all cut-to alternatives within the alternatives created by the current
sub-tree. For example, consider the tree `(A /\_{B0} B) \/ C`. When compiling
`A` and `B`, `C` is used as the backtracking tree. If `A` is the
list `x::xs`, then `x` should treat `B` as its natural execution tail, while
`xs` should use `B0` as its execution tail. This implies that `B0` is appended
as a tail-conjunct to all cut-to alternatives in `x` and `xs` that do not
come from `C`.

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic

namespace GraphMSO

/--
An inductive rooted tree whose nodes carry bags of graph vertices.

A leaf is represented as `node bag 0 ...`, so there is only one constructor and
no duplicate leaf/nonleaf encoding.
-/
inductive DecompositionTree (V : Type) : Type where
  | node (bag : Set V) (arity : Nat) (child : Fin arity -> DecompositionTree V) :
      DecompositionTree V

namespace DecompositionTree

variable {V : Type}

/-- The bag attached to the root. -/
def rootBag : DecompositionTree V -> Set V
  | .node bag _ _ => bag

/-- The number of children of the root. -/
def arity : DecompositionTree V -> Nat
  | .node _ arity _ => arity

/-- The `i`th child subtree. -/
def child : (T : DecompositionTree V) -> Fin (arity T) -> DecompositionTree V
  | .node _ _ child, i => child i

/-- A one-node tree. -/
def leaf (bag : Set V) : DecompositionTree V :=
  .node bag 0 (fun i => Fin.elim0 i)

/-- The tree contains `v` in at least one bag. -/
inductive ContainsVertex : DecompositionTree V -> V -> Prop
  | root (bag : Set V) arity child v (hv : v ∈ bag) :
      ContainsVertex (DecompositionTree.node bag arity child) v
  | child (bag : Set V) arity child v (i : Fin arity)
      (hchild : ContainsVertex (child i) v) :
      ContainsVertex (DecompositionTree.node bag arity child) v

/-- The tree contains `u` and `v` together in at least one bag. -/
inductive ContainsEdge : DecompositionTree V -> V -> V -> Prop
  | root (bag : Set V) arity child u v (hu : u ∈ bag) (hv : v ∈ bag) :
      ContainsEdge (DecompositionTree.node bag arity child) u v
  | child (bag : Set V) arity child u v (i : Fin arity)
      (hchild : ContainsEdge (child i) u v) :
      ContainsEdge (DecompositionTree.node bag arity child) u v

/-- Every bag in the tree satisfies `P`. -/
inductive AllBags (P : Set V -> Prop) : DecompositionTree V -> Prop
  | node (bag : Set V) arity child (hroot : P bag)
      (hchild : forall i : Fin arity, AllBags P (child i)) :
      AllBags P (DecompositionTree.node bag arity child)

/-- Every bag in the tree is finite. -/
def BagsFinite (T : DecompositionTree V) : Prop :=
  T.AllBags Set.Finite

/--
For one graph vertex `v`, the bags containing `v` form a connected rooted subtree.

Inductively, every child satisfies the property; if the root bag contains `v`,
then every child branch containing `v` starts with a child root bag containing
`v`; and if the root bag does not contain `v`, then at most one child branch can
contain `v`.
-/
inductive RunningIntersectionAt : DecompositionTree V -> V -> Prop
  | node (bag : Set V) arity child v
      (hchild : forall i : Fin arity, RunningIntersectionAt (child i) v)
      (hroot : v ∈ bag ->
        forall i : Fin arity, ContainsVertex (child i) v -> v ∈ rootBag (child i))
      (hunique : v ∉ bag ->
        forall i j : Fin arity, ContainsVertex (child i) v -> ContainsVertex (child j) v ->
          i = j) :
      RunningIntersectionAt (DecompositionTree.node bag arity child) v

/-- The running-intersection property for all graph vertices. -/
def RunningIntersection (T : DecompositionTree V) : Prop :=
  forall v : V, T.RunningIntersectionAt v

@[simp] theorem containsVertex_leaf_iff (bag : Set V) (v : V) :
    (leaf bag).ContainsVertex v ↔ v ∈ bag := by
  unfold leaf
  constructor
  · intro h
    cases h with
    | root _ _ _ _ hv => exact hv
    | child _ _ _ _ i _ => exact Fin.elim0 i
  · intro hv; exact .root _ _ _ _ hv

@[simp] theorem containsEdge_leaf_iff (bag : Set V) (u v : V) :
    (leaf bag).ContainsEdge u v ↔ u ∈ bag ∧ v ∈ bag := by
  unfold leaf
  constructor
  · intro h
    cases h with
    | root _ _ _ _ _ hu hv => exact ⟨hu, hv⟩
    | child _ _ _ _ _ i _ => exact Fin.elim0 i
  · intro ⟨hu, hv⟩; exact .root _ _ _ _ _ hu hv

/-- The running-intersection property holds trivially at a leaf (no children). -/
theorem runningIntersectionAt_leaf (bag : Set V) (v : V) :
    (leaf bag).RunningIntersectionAt v :=
  .node bag 0 (fun i => Fin.elim0 i) v (fun i => Fin.elim0 i)
    (fun _ i => Fin.elim0 i) (fun _ i => Fin.elim0 i)

@[simp] theorem containsVertex_unary_iff (bag : Set V) (c : DecompositionTree V) (v : V) :
    (DecompositionTree.node bag 1 (fun _ => c)).ContainsVertex v ↔ v ∈ bag ∨ c.ContainsVertex v := by
  constructor
  · intro h
    cases h with
    | root _ _ _ _ hv => exact Or.inl hv
    | child _ _ _ _ i hc => exact Or.inr hc
  · rintro (hv | hc)
    · exact .root _ _ _ _ hv
    · exact .child _ _ _ _ 0 hc

@[simp] theorem containsEdge_unary_iff (bag : Set V) (c : DecompositionTree V) (u v : V) :
    (DecompositionTree.node bag 1 (fun _ => c)).ContainsEdge u v
      ↔ (u ∈ bag ∧ v ∈ bag) ∨ c.ContainsEdge u v := by
  constructor
  · intro h
    cases h with
    | root _ _ _ _ _ hu hv => exact Or.inl ⟨hu, hv⟩
    | child _ _ _ _ _ i hc => exact Or.inr hc
  · rintro (⟨hu, hv⟩ | hc)
    · exact .root _ _ _ _ _ hu hv
    · exact .child _ _ _ _ _ 0 hc

/-- Running intersection at a unary node: it suffices to know it for the single
child and that the shared vertex carries down into the child bag. -/
theorem runningIntersectionAt_unary (bag : Set V) (c : DecompositionTree V) (v : V)
    (hchild : c.RunningIntersectionAt v)
    (hroot : v ∈ bag -> c.ContainsVertex v -> v ∈ c.rootBag) :
    (DecompositionTree.node bag 1 (fun _ => c)).RunningIntersectionAt v :=
  .node bag 1 (fun _ => c) v (fun _ => hchild) (fun hv _ hc => hroot hv hc)
    (fun _ i j _ _ => Subsingleton.elim i j)

/--
`T.WidthAtMost k` means that every bag of `T` has at most `k + 1` vertices.
This is the usual `width(T) <= k` condition, phrased without taking a maximum.
-/
def WidthAtMost (T : DecompositionTree V) (k : Nat) : Prop :=
  T.AllBags (fun bag => bag.ncard <= k + 1)

/-- Unfolding lemma: `AllBags P` at a node splits into the root bag and the children. -/
theorem allBags_node_iff (P : Set V -> Prop) (bag : Set V) (arity : Nat)
    (child : Fin arity -> DecompositionTree V) :
    AllBags P (.node bag arity child) ↔ P bag ∧ ∀ i, AllBags P (child i) := by
  constructor
  · intro h; cases h with | node _ _ _ hroot hchild => exact ⟨hroot, hchild⟩
  · exact fun ⟨hroot, hchild⟩ => .node bag arity child hroot hchild

/-- The maximum cardinality among all bags of `T`, computed by recursion on the tree. -/
noncomputable def maxBagCard : DecompositionTree V -> Nat
  | .node bag arity child =>
      max bag.ncard ((Finset.univ : Finset (Fin arity)).sup fun i => (child i).maxBagCard)

@[simp] theorem maxBagCard_leaf (bag : Set V) : (leaf bag).maxBagCard = bag.ncard := by
  simp [maxBagCard, leaf]

/--
`T.width` is `maxBagCard T - 1`, matching the usual convention
`width(T) = (largest bag size) - 1`.
-/
noncomputable def width (T : DecompositionTree V) : Nat := T.maxBagCard - 1

/-- `WidthAtMost k` is exactly the bound `maxBagCard ≤ k + 1`. -/
theorem widthAtMost_iff_maxBagCard_le (T : DecompositionTree V) (k : Nat) :
    T.WidthAtMost k ↔ T.maxBagCard ≤ k + 1 := by
  induction T with
  | node bag arity child ih =>
    simp only [WidthAtMost, allBags_node_iff, maxBagCard, max_le_iff, Finset.sup_le_iff,
      Finset.mem_univ, true_implies]
    exact and_congr Iff.rfl (forall_congr' fun i => ih i)

/-- `WidthAtMost k` is exactly `width ≤ k`. -/
theorem widthAtMost_iff_width_le (T : DecompositionTree V) (k : Nat) :
    T.WidthAtMost k ↔ T.width ≤ k := by
  rw [widthAtMost_iff_maxBagCard_le, width]; omega

/-! ### Rooted node addressing

A node of a rooted decomposition tree is addressed by the list of child indices on
the path from the root, with `[]` denoting the root. This gives the
`parent`/`child`, adhesion, cone, `BAGS(v)`, topmost-node, and connectivity
vocabulary used by the lecture-note tree-decomposition encoding. The ancestor
relation is mathlib's list-prefix order `<+:`. -/

/-- Follow a path of child indices from the root, returning the subtree rooted at
the addressed node, or `none` if some index is out of range. -/
def nodeAt : DecompositionTree V -> List Nat -> Option (DecompositionTree V)
  | T, [] => some T
  | .node _ arity child, i :: rest =>
      if h : i < arity then (child ⟨i, h⟩).nodeAt rest else none

@[simp] theorem nodeAt_nil (T : DecompositionTree V) : T.nodeAt [] = some T := by
  cases T; rfl

theorem nodeAt_node_cons (bag : Set V) (arity : Nat)
    (child : Fin arity -> DecompositionTree V) (i : Nat) (rest : List Nat) :
    (DecompositionTree.node bag arity child).nodeAt (i :: rest)
      = if h : i < arity then (child ⟨i, h⟩).nodeAt rest else none := rfl

/-- `p` addresses an actual node of `T`. -/
def IsNode (T : DecompositionTree V) (p : List Nat) : Prop := (T.nodeAt p).isSome

@[simp] theorem isNode_nil (T : DecompositionTree V) : T.IsNode [] := by
  cases T; rfl

/-- The bag at node `p`, or `∅` when `p` is not a node. -/
def bagAt (T : DecompositionTree V) (p : List Nat) : Set V :=
  match T.nodeAt p with
  | some s => s.rootBag
  | none => ∅

@[simp] theorem bagAt_nil (T : DecompositionTree V) : T.bagAt [] = T.rootBag := by
  cases T; rfl

/-- The cone at `p`: every vertex appearing somewhere in the subtree rooted at `p`. -/
def coneAt (T : DecompositionTree V) (p : List Nat) : Set V :=
  match T.nodeAt p with
  | some s => { v | s.ContainsVertex v }
  | none => ∅

/-- The parent of a node drops the last child index; the root `[]` is its own
parent by convention. -/
def parent (p : List Nat) : List Nat := p.dropLast

@[simp] theorem parent_append_singleton (p : List Nat) (i : Nat) :
    parent (p ++ [i]) = p := by simp [parent]

/-- `q` is a child of `p` in `T`. -/
def IsChild (T : DecompositionTree V) (p q : List Nat) : Prop :=
  ∃ s, T.nodeAt p = some s ∧ ∃ i : Fin s.arity, q = p ++ [(i : Nat)]

/-- The adhesion of node `p`: the overlap between its bag and its parent's bag
(`∅` at the root, which has no parent). -/
def adhesionAt (T : DecompositionTree V) : List Nat -> Set V
  | [] => ∅
  | i :: rest => T.bagAt (i :: rest) ∩ T.bagAt (parent (i :: rest))

/-- `BAGS T v` is the set of nodes whose bag contains `v`. -/
def BAGS (T : DecompositionTree V) (v : V) : Set (List Nat) := { p | v ∈ T.bagAt p }

theorem mem_BAGS {T : DecompositionTree V} {v : V} {p : List Nat} :
    p ∈ T.BAGS v ↔ ∃ s, T.nodeAt p = some s ∧ v ∈ s.rootBag := by
  simp only [BAGS, Set.mem_setOf_eq, bagAt]
  cases h : T.nodeAt p with
  | none => simp
  | some s => simp

/-- `r` is the topmost node of `S`: it lies in `S` and is an ancestor (list-prefix)
of every node of `S`. -/
def IsTopmost (S : Set (List Nat)) (r : List Nat) : Prop :=
  r ∈ S ∧ ∀ p ∈ S, r <+: p

/-- A set of tree nodes is connected when it has a topmost node and is convex below
it: every node lying between the topmost node and a member of `S` is itself in `S`.
On a tree this is exactly the induced-subgraph connectivity condition. -/
def IsConnectedNodeSet (S : Set (List Nat)) : Prop :=
  ∃ r, IsTopmost S r ∧ ∀ p ∈ S, ∀ q, r <+: q -> q <+: p -> q ∈ S

/-! #### `BAGS(v)` is a connected node set

Under the running-intersection property, the nodes containing a fixed vertex `v`
form a connected rooted subtree: there is a topmost node (closest to the root)
containing `v`, and the set is convex below it. -/

theorem mem_bags_nil (T : DecompositionTree V) (v : V) :
    [] ∈ T.BAGS v ↔ v ∈ T.rootBag := by
  simp only [BAGS, Set.mem_setOf_eq, bagAt_nil]

theorem mem_bags_cons_iff (bag : Set V) (arity : Nat) (child : Fin arity -> DecompositionTree V)
    (i : Nat) (rest : List Nat) (v : V) :
    (i :: rest) ∈ BAGS (.node bag arity child) v ↔
      ∃ h : i < arity, rest ∈ (child ⟨i, h⟩).BAGS v := by
  simp only [BAGS, Set.mem_setOf_eq, bagAt, nodeAt_node_cons]
  by_cases h : i < arity
  · simp only [dif_pos h]
    exact ⟨fun hm => ⟨h, hm⟩, fun ⟨_, hm⟩ => hm⟩
  · simp only [dif_neg h]
    constructor
    · intro hm; simp at hm
    · rintro ⟨h', _⟩; exact absurd h' h

theorem mem_bags_cons_fin (bag : Set V) (arity : Nat) (child : Fin arity -> DecompositionTree V)
    (j : Fin arity) (rest : List Nat) (v : V) :
    ((j : Nat) :: rest) ∈ BAGS (.node bag arity child) v ↔ rest ∈ (child j).BAGS v := by
  rw [mem_bags_cons_iff]
  exact ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨j.2, hm⟩⟩

/-- Inversion for the running-intersection property at a node. -/
theorem RunningIntersectionAt.node_inv {bag : Set V} {arity : Nat}
    {child : Fin arity -> DecompositionTree V} {v : V}
    (h : RunningIntersectionAt (.node bag arity child) v) :
    (∀ i, (child i).RunningIntersectionAt v) ∧
      (v ∈ bag -> ∀ i, (child i).ContainsVertex v -> v ∈ (child i).rootBag) ∧
      (v ∉ bag -> ∀ i j, (child i).ContainsVertex v -> (child j).ContainsVertex v -> i = j) := by
  cases h with
  | node _ _ _ _ hchild hroot hunique => exact ⟨hchild, hroot, hunique⟩

/-- A node of `BAGS T v` witnesses that `T` contains `v`. -/
theorem containsVertex_of_mem_bags {v : V} {p : List Nat} :
    ∀ {T : DecompositionTree V}, p ∈ T.BAGS v -> T.ContainsVertex v := by
  induction p with
  | nil =>
    intro T hp
    cases T with
    | node bag arity child => rw [mem_bags_nil] at hp; exact .root _ _ _ _ hp
  | cons i rest ih =>
    intro T hp
    cases T with
    | node bag arity child =>
      rw [mem_bags_cons_iff] at hp
      obtain ⟨h, hmem⟩ := hp
      exact .child _ _ _ _ ⟨i, h⟩ (ih hmem)

/-- If the root bag contains `v`, then `BAGS T v` is closed under taking ancestors
(prefixes): every node between the root and a node containing `v` also contains `v`. -/
theorem bags_prefixClosed {v : V} {p : List Nat} :
    ∀ {T : DecompositionTree V}, T.RunningIntersectionAt v -> v ∈ T.rootBag ->
      p ∈ T.BAGS v -> ∀ {q : List Nat}, q <+: p -> q ∈ T.BAGS v := by
  induction p with
  | nil =>
    intro T _ hroot_mem _ q hq
    rw [List.prefix_nil] at hq; subst hq
    rw [mem_bags_nil]; exact hroot_mem
  | cons i rest ih =>
    intro T hT hroot_mem hp q hq
    cases T with
    | node bag arity child =>
      rw [mem_bags_cons_iff] at hp
      obtain ⟨h, hmem⟩ := hp
      obtain ⟨hchild, hrootRI, _⟩ := hT.node_inv
      cases q with
      | nil => rw [mem_bags_nil]; exact hroot_mem
      | cons k rest' =>
        rw [List.cons_prefix_cons] at hq
        obtain ⟨hki, hq'⟩ := hq
        rw [hki, mem_bags_cons_iff]
        refine ⟨h, ?_⟩
        have hcv : (child ⟨i, h⟩).ContainsVertex v := containsVertex_of_mem_bags hmem
        have hvr : v ∈ (child ⟨i, h⟩).rootBag := hrootRI hroot_mem ⟨i, h⟩ hcv
        exact ih (hchild ⟨i, h⟩) hvr hmem hq'

/-- **Running intersection implies `BAGS(v)` is connected.** For each vertex `v`
appearing in `T`, the set of nodes whose bag contains `v` is a connected node set. -/
theorem isConnectedNodeSet_bags {v : V} :
    ∀ {T : DecompositionTree V}, T.RunningIntersectionAt v -> T.ContainsVertex v ->
      IsConnectedNodeSet (T.BAGS v) := by
  intro T
  induction T with
  | node bag arity child ih =>
    intro hT hcv
    by_cases hbag : v ∈ bag
    · -- Case A: the root contains `v`, so the topmost node is the root `[]`.
      refine ⟨[], ⟨?_, ?_⟩, ?_⟩
      · rw [mem_bags_nil]; exact hbag
      · intro p _; exact List.nil_prefix
      · intro p hp q _ hqp
        exact bags_prefixClosed hT hbag hp hqp
    · -- Case B: `v` lies in a unique child subtree `i₀`.
      obtain ⟨i₀, hcv₀⟩ : ∃ i, (child i).ContainsVertex v := by
        cases hcv with
        | root _ _ _ _ hv => exact absurd hv hbag
        | child _ _ _ _ i hc => exact ⟨i, hc⟩
      obtain ⟨hchild, _, hunique⟩ := hT.node_inv
      obtain ⟨r₀, ⟨hr₀mem, hr₀top⟩, hr₀conv⟩ := ih i₀ (hchild i₀) hcv₀
      refine ⟨(i₀ : Nat) :: r₀, ⟨?_, ?_⟩, ?_⟩
      · rw [mem_bags_cons_fin]; exact hr₀mem
      · intro p hp
        cases p with
        | nil => rw [mem_bags_nil] at hp; exact absurd hp hbag
        | cons k rest =>
          rw [mem_bags_cons_iff] at hp
          obtain ⟨hk, hmem⟩ := hp
          have hcvk : (child ⟨k, hk⟩).ContainsVertex v := containsVertex_of_mem_bags hmem
          have hki₀ : (⟨k, hk⟩ : Fin arity) = i₀ := hunique hbag ⟨k, hk⟩ i₀ hcvk hcv₀
          rw [List.cons_prefix_cons]
          exact ⟨congrArg Fin.val hki₀.symm, hr₀top rest (hki₀ ▸ hmem)⟩
      · intro p hp q hrq hqp
        cases p with
        | nil => rw [mem_bags_nil] at hp; exact absurd hp hbag
        | cons k rest =>
          rw [mem_bags_cons_iff] at hp
          obtain ⟨hk, hmem⟩ := hp
          have hcvk : (child ⟨k, hk⟩).ContainsVertex v := containsVertex_of_mem_bags hmem
          have hki₀ : (⟨k, hk⟩ : Fin arity) = i₀ := hunique hbag ⟨k, hk⟩ i₀ hcvk hcv₀
          have hrest : rest ∈ (child i₀).BAGS v := hki₀ ▸ hmem
          obtain ⟨t, rfl⟩ := hrq
          rw [List.cons_append] at hqp ⊢
          rw [mem_bags_cons_fin]
          rw [List.cons_prefix_cons] at hqp
          exact hr₀conv rest hrest (r₀ ++ t) ⟨t, rfl⟩ hqp.2

/-- A node set has at most one topmost node. -/
theorem IsTopmost.unique {S : Set (List Nat)} {r r' : List Nat}
    (h : IsTopmost S r) (h' : IsTopmost S r') : r = r' :=
  (h.2 r' h'.1).sublist.antisymm (h'.2 r h.1).sublist

/-! ### Bag-injective colorings

For a width-`ω` decomposition the lecture note rainbow-colors vertices with `ω + 1`
colors so that the vertices of each bag get pairwise distinct colors. This is
exactly a coloring that is injective on every bag. -/

/-- A vertex coloring that is injective on every bag of `T`. With `n = ω + 1`
colors this is the rainbow coloring of a width-`ω` decomposition. -/
def IsBagColoring (T : DecompositionTree V) {n : Nat} (c : V -> Fin n) : Prop :=
  T.AllBags (fun bag => Set.InjOn c bag)

/-- A set injected into `Fin (n + 1)` has at most `n + 1` elements. -/
theorem ncard_le_of_injOn_fin {n : Nat} {c : V -> Fin (n + 1)} {s : Set V}
    (h : Set.InjOn c s) : s.ncard ≤ n + 1 := by
  rw [← Set.ncard_image_of_injOn h]
  calc (c '' s).ncard
      ≤ (Set.univ : Set (Fin (n + 1))).ncard := Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = n + 1 := by simp

/-- A bag-injective coloring with `n + 1` colors witnesses width at most `n`. -/
theorem widthAtMost_of_isBagColoring {n : Nat} {T : DecompositionTree V}
    {c : V -> Fin (n + 1)} (h : T.IsBagColoring c) : T.WidthAtMost n := by
  induction T with
  | node bag arity child ih =>
    rw [IsBagColoring, allBags_node_iff] at h
    rw [WidthAtMost, allBags_node_iff]
    exact ⟨ncard_le_of_injOn_fin h.1, fun i => ih i (h.2 i)⟩

/-- `AllBags P` yields `P` at the root bag. -/
theorem AllBags.rootBag {P : Set V -> Prop} {T : DecompositionTree V} (h : AllBags P T) :
    P T.rootBag := by
  cases T with | node bag arity child => cases h with | node _ _ _ hroot _ => exact hroot

/-- A bag-injective coloring only depends on the colors of vertices in the tree. -/
theorem isBagColoring_congr {n : Nat} {f g : V -> Fin n} :
    ∀ {T : DecompositionTree V}, T.IsBagColoring f ->
      (∀ v, T.ContainsVertex v -> f v = g v) -> T.IsBagColoring g := by
  intro T
  induction T with
  | node bag arity child ih =>
    intro hf h
    simp only [IsBagColoring, allBags_node_iff] at hf ⊢
    obtain ⟨hbag, hch⟩ := hf
    refine ⟨?_, fun i => ih i (hch i) (fun v hv => h v (.child _ _ _ _ i hv))⟩
    intro x hx y hy hxy
    apply hbag hx hy
    rw [h x (.root _ _ _ _ hx), h y (.root _ _ _ _ hy)]
    exact hxy

/-- Extend a coloring injective on `t` to one injective on `t ∪ u`, as long as the
palette `Fin k` is large enough to fit `t ∪ u`. -/
theorem exists_injOn_extend {k : Nat} {c₀ : V -> Fin k} {t : Set V}
    (ht : t.Finite) (hinj : Set.InjOn c₀ t) :
    ∀ {u : Set V}, u.Finite -> Disjoint t u -> (t ∪ u).ncard ≤ k ->
      ∃ c : V -> Fin k, Set.InjOn c (t ∪ u) ∧ Set.EqOn c c₀ t := by
  classical
  intro u hu
  induction u, hu using Set.Finite.induction_on with
  | empty =>
    intro _ _
    refine ⟨c₀, ?_, fun _ _ => rfl⟩
    simpa using hinj
  | @insert a u' ha hu' ih =>
    intro hdisj hcard
    have ha_t : a ∉ t := Set.disjoint_right.mp hdisj (Set.mem_insert a u')
    have hfin' : (t ∪ u').Finite := ht.union hu'
    have ha' : a ∉ t ∪ u' := by simp only [Set.mem_union, not_or]; exact ⟨ha_t, ha⟩
    have hins : t ∪ insert a u' = insert a (t ∪ u') := Set.union_insert
    have hcard' : (t ∪ u').ncard < k := by
      have h1 : (insert a (t ∪ u')).ncard = (t ∪ u').ncard + 1 :=
        Set.ncard_insert_of_notMem ha' hfin'
      rw [hins, h1] at hcard; omega
    obtain ⟨c', hc'inj, hc'eq⟩ := ih (hdisj.mono_right (Set.subset_insert a u')) (by
      rw [hins] at hcard
      exact le_trans (Set.ncard_le_ncard (Set.subset_insert a (t ∪ u')) (hfin'.insert a)) hcard)
    obtain ⟨color, -, hcolor⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (s := c' '' (t ∪ u')) (t := (Set.univ : Set (Fin k)))
      (by
        have hle : (c' '' (t ∪ u')).ncard ≤ (t ∪ u').ncard := Set.ncard_image_le hfin'
        rw [Set.ncard_univ]
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
        omega)
    have heq : Set.EqOn (Function.update c' a color) c' (t ∪ u') := by
      intro x hx
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha')]
    refine ⟨Function.update c' a color, ?_, ?_⟩
    · rw [hins, Set.injOn_insert ha']
      refine ⟨hc'inj.congr heq.symm, ?_⟩
      rw [Function.update_self, Set.image_congr heq]
      exact hcolor
    · intro x hx
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha_t)]
      exact hc'eq hx

/-- **Existence of a bag-injective coloring, relative form.** Given any injective
coloring of the root bag, a width-`ω` decomposition with the running-intersection
property extends it to a coloring injective on every bag. -/
theorem exists_isBagColoring_extend {ω : Nat} :
    ∀ {T : DecompositionTree V}, T.RunningIntersection -> T.BagsFinite -> T.WidthAtMost ω ->
      ∀ {c₀ : V -> Fin (ω + 1)}, Set.InjOn c₀ T.rootBag ->
        ∃ c : V -> Fin (ω + 1), T.IsBagColoring c ∧ Set.EqOn c c₀ T.rootBag := by
  classical
  intro T
  induction T with
  | node bag arity child ih =>
    intro hRI hFin hW c₀ hc₀
    simp only [WidthAtMost, BagsFinite, allBags_node_iff] at hW hFin
    obtain ⟨hFinBag, hFinChild⟩ := hFin
    obtain ⟨hWBag, hWChild⟩ := hW
    -- For each child, build a bag-injective coloring agreeing with `c₀` on the overlap.
    have key : ∀ i, ∃ c_i : V -> Fin (ω + 1),
        (child i).IsBagColoring c_i ∧ Set.EqOn c_i c₀ (bag ∩ (child i).rootBag) := by
      intro i
      have hRIi : (child i).RunningIntersection := fun v => (hRI v).node_inv.1 i
      have hrbFin : ((child i).rootBag).Finite := (hFinChild i).rootBag
      have htfin : (bag ∩ (child i).rootBag).Finite := hFinBag.inter_of_left _
      have hsub : bag ∩ (child i).rootBag ⊆ (child i).rootBag := Set.inter_subset_right
      have hinj_t : Set.InjOn c₀ (bag ∩ (child i).rootBag) := hc₀.mono Set.inter_subset_left
      have hunion : (bag ∩ (child i).rootBag) ∪ ((child i).rootBag \ (bag ∩ (child i).rootBag))
          = (child i).rootBag := Set.union_diff_cancel hsub
      obtain ⟨d_i, hd_inj, hd_eq⟩ := exists_injOn_extend htfin hinj_t hrbFin.diff
        Set.disjoint_sdiff_right (by rw [hunion]; exact (hWChild i).rootBag)
      rw [hunion] at hd_inj
      obtain ⟨c_i, hc_i_bag, hc_i_eq⟩ := ih i hRIi (hFinChild i) (hWChild i) hd_inj
      exact ⟨c_i, hc_i_bag, fun v hv => by rw [hc_i_eq (hsub hv), hd_eq hv]⟩
    choose c_fam hc_bag hc_eq using key
    set c : V -> Fin (ω + 1) := fun v =>
      if hb : v ∈ bag then c₀ v
      else if h : ∃ i, (child i).ContainsVertex v then c_fam h.choose v else c₀ v
      with hc_def
    have hP1 : ∀ v, v ∈ bag -> c v = c₀ v := by
      intro v hv; simp only [hc_def, dif_pos hv]
    have hP2 : ∀ i v, (child i).ContainsVertex v -> c v = c_fam i v := by
      intro i v hcv
      by_cases hv : v ∈ bag
      · rw [hP1 v hv]
        have hvr : v ∈ (child i).rootBag := (hRI v).node_inv.2.1 hv i hcv
        exact (hc_eq i ⟨hv, hvr⟩).symm
      · have hexists : ∃ j, (child j).ContainsVertex v := ⟨i, hcv⟩
        have hchoose : hexists.choose = i :=
          (hRI v).node_inv.2.2 hv hexists.choose i hexists.choose_spec hcv
        simp only [hc_def, dif_neg hv, dif_pos hexists, hchoose]
    refine ⟨c, ?_, fun v hv => hP1 v hv⟩
    simp only [IsBagColoring, allBags_node_iff]
    refine ⟨hc₀.congr (fun v hv => (hP1 v hv).symm), fun i => ?_⟩
    exact isBagColoring_congr (hc_bag i) (fun v hcv => (hP2 i v hcv).symm)

/-- **Existence of a bag-injective coloring.** A width-`ω` tree decomposition with the
running-intersection property admits a coloring with `ω + 1` colors that is injective
on every bag (the lecture-note rainbow coloring). -/
theorem exists_isBagColoring {ω : Nat} {T : DecompositionTree V}
    (hRI : T.RunningIntersection) (hFin : T.BagsFinite) (hW : T.WidthAtMost ω) :
    ∃ c : V -> Fin (ω + 1), T.IsBagColoring c := by
  obtain ⟨c₀, hc₀, -⟩ := exists_injOn_extend (k := ω + 1) (t := (∅ : Set V))
    (c₀ := fun _ => 0) Set.finite_empty (by simp) (AllBags.rootBag hFin) (by simp)
    (by rw [Set.empty_union]; exact AllBags.rootBag hW)
  rw [Set.empty_union] at hc₀
  obtain ⟨c, hc, -⟩ := exists_isBagColoring_extend hRI hFin hW hc₀
  exact ⟨c, hc⟩

end DecompositionTree

/--
`TreeDecomposition G T` means that the inductive tree `T` is a valid tree
decomposition of the graph `G`.
-/
inductive TreeDecomposition {V : Type} (G : SimpleGraph V) : DecompositionTree V -> Prop where
  | mk (T : DecompositionTree V)
      (finite_bags : T.BagsFinite)
      (vertex_mem : forall v : V, T.ContainsVertex v)
      (edge_mem : forall {u v : V}, G.Adj u v -> T.ContainsEdge u v)
      (running_intersection : T.RunningIntersection) :
      TreeDecomposition G T

/-- A nice tree decomposition, indexed by its root bag. -/
inductive NiceTreeDecomposition (V : Type) : Set V -> Type where
  | leaf : NiceTreeDecomposition V (∅ : Set V)
  | introduce (bag : Set V) (v : V) (v_not_mem : v ∉ bag)
      (child : NiceTreeDecomposition V bag) : NiceTreeDecomposition V (insert v bag)
  | forget (bag : Set V) (v : V) (v_not_mem : v ∉ bag)
      (child : NiceTreeDecomposition V (insert v bag)) : NiceTreeDecomposition V bag
  | join (bag : Set V) (left right : NiceTreeDecomposition V bag) :
      NiceTreeDecomposition V bag


namespace TreeDecomposition

variable {V : Type} {G : SimpleGraph V}

/-- The graph `G` admits a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost (G : SimpleGraph V) (k : Nat) : Prop :=
  Exists fun T : DecompositionTree V => TreeDecomposition G T ∧ T.WidthAtMost k

/-- A one-node decomposition tree whose only bag contains all vertices of a finite graph. -/
def singleBag (_G : SimpleGraph V) [Fintype V] : DecompositionTree V :=
  DecompositionTree.leaf Set.univ

/-- The one-bag tree is a valid decomposition of any finite graph. -/
theorem singleBag_decomposition (G : SimpleGraph V) [Fintype V] :
    TreeDecomposition G (singleBag G) := by
  exact TreeDecomposition.mk (singleBag G)
    (DecompositionTree.AllBags.node (bag := Set.univ) (arity := 0)
      (child := fun i => Fin.elim0 i) (by simp) (fun i => Fin.elim0 i))
    (by
      intro v
      exact DecompositionTree.ContainsVertex.root Set.univ 0 (fun i => Fin.elim0 i) v
        (by simp))
    (by
      intro u v _
      exact DecompositionTree.ContainsEdge.root Set.univ 0 (fun i => Fin.elim0 i) u v
        (by simp) (by simp))
    (by
      intro v
      exact DecompositionTree.RunningIntersectionAt.node Set.univ 0 (fun i => Fin.elim0 i) v
        (fun i => Fin.elim0 i)
        (by intro _ i; exact Fin.elim0 i)
        (by intro _ i; exact Fin.elim0 i))

theorem singleBag_widthAtMost_card (G : SimpleGraph V) [Fintype V] :
    (singleBag G).WidthAtMost (Fintype.card V) := by
  exact DecompositionTree.AllBags.node (bag := Set.univ) (arity := 0)
    (child := fun i => Fin.elim0 i) (by simp) (fun i => Fin.elim0 i)

theorem hasTreewidthAtMost_card (G : SimpleGraph V) [Fintype V] :
    HasTreewidthAtMost G (Fintype.card V) :=
  Exists.intro (singleBag G) ⟨singleBag_decomposition G, singleBag_widthAtMost_card G⟩

/-! ### A two-bag path example

The path `0 — 1 — 2` on `Fin 3`, decomposed into the overlapping bags `{0, 1}` and
`{1, 2}`. This width-`1` decomposition exercises the multi-bag running-intersection
machinery beyond the single-bag case. -/

/-- The path graph on three vertices: `0 — 1 — 2`. -/
def pathP3 : SimpleGraph (Fin 3) where
  Adj a b := a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := fun _ _ h => h.symm
  loopless := by intro a h; rcases h with h | h <;> omega

/-- The two-bag decomposition `{0, 1} — {1, 2}` of `pathP3`. -/
def pathP3Decomp : DecompositionTree (Fin 3) :=
  .node {0, 1} 1 (fun _ => DecompositionTree.leaf {1, 2})

theorem pathP3Decomp_decomposition : TreeDecomposition pathP3 pathP3Decomp := by
  refine TreeDecomposition.mk pathP3Decomp ?_ ?_ ?_ ?_
  · unfold DecompositionTree.BagsFinite pathP3Decomp
    refine .node _ _ _ (Set.toFinite _) (fun _ => ?_)
    exact .node _ _ _ (Set.toFinite _) (fun i => Fin.elim0 i)
  · intro v
    simp only [pathP3Decomp, DecompositionTree.containsVertex_unary_iff,
      DecompositionTree.containsVertex_leaf_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro u v h
    simp only [pathP3Decomp, DecompositionTree.containsEdge_unary_iff,
      DecompositionTree.containsEdge_leaf_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    change u.val + 1 = v.val ∨ v.val + 1 = u.val at h
    omega
  · intro v
    simp only [pathP3Decomp]
    refine DecompositionTree.runningIntersectionAt_unary _ _ _
      (DecompositionTree.runningIntersectionAt_leaf _ _) (fun _ hc => ?_)
    rw [DecompositionTree.containsVertex_leaf_iff] at hc
    simpa [DecompositionTree.leaf, DecompositionTree.rootBag] using hc

end TreeDecomposition

namespace NiceTreeDecomposition

variable {V : Type}

/-- Interpret a nice tree decomposition as a bare `DecompositionTree`: `introduce`
and `forget` become unary nodes, `join` a binary node, and `leaf` the empty-bag
leaf. The root-bag index is preserved (`toDecompositionTree_rootBag`). -/
def toDecompositionTree : {bag : Set V} -> NiceTreeDecomposition V bag -> DecompositionTree V
  | _, .leaf => .leaf ∅
  | _, .introduce bag v _ child => .node (insert v bag) 1 (fun _ => child.toDecompositionTree)
  | _, .forget bag _ _ child => .node bag 1 (fun _ => child.toDecompositionTree)
  | _, .join bag left right =>
      .node bag 2 (fun i => if i = 0 then left.toDecompositionTree else right.toDecompositionTree)

@[simp] theorem toDecompositionTree_rootBag {bag : Set V} (d : NiceTreeDecomposition V bag) :
    d.toDecompositionTree.rootBag = bag := by
  cases d <;> rfl

end NiceTreeDecomposition

end GraphMSO

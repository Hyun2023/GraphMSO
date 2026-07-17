import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Dedup

/-!
# Executable tree-decomposition presentation

`DecompTree` is the algorithm-facing input format for tree-decompositions: a
rose tree whose nodes carry raw vertex lists as bags.  The rooted tree shape
is built into the data, so no separate tree axiom, root choice, or child
enumeration is needed, and algorithms can recurse structurally.

Validity for a graph `G` is a separate predicate `IsDecompFor`, split into
vertex coverage, edge coverage, and the local running-intersection property
`RunningIntersection`.  Computable functions consume the raw data; only the
correctness theorems consume the validity predicate.
-/

universe u

/-- A rose-tree presentation of a rooted tree-decomposition.  Each node
stores its bag as a raw vertex list; duplicates are harmless because all
consumers measure bags through `List.toFinset`. -/
inductive DecompTree (V : Type u) : Type u where
  | node (bag : List V) (children : List (DecompTree V))

namespace DecompTree

variable {V : Type u}

/-- The bag stored at the root node. -/
def rootBag : DecompTree V → List V
  | node bag _ => bag

@[simp] theorem rootBag_node (bag : List V) (children : List (DecompTree V)) :
    (node bag children).rootBag = bag :=
  rfl

/-- Rose-tree induction with the child hypotheses gathered by membership. -/
@[elab_as_elim]
theorem induction_on {motive : DecompTree V → Prop} (t : DecompTree V)
    (h : ∀ bag children, (∀ c ∈ children, motive c) → motive (node bag children)) :
    motive t :=
  match t with
  | node bag children => h bag children (fun c _hc => induction_on c h)

/-- The list `target` is the bag of some node of the rose tree. -/
inductive HasBag : DecompTree V → List V → Prop
  | root (bag : List V) (children : List (DecompTree V)) :
      HasBag (node bag children) bag
  | child {c : DecompTree V} {target : List V} (bag : List V)
      {children : List (DecompTree V)} (hc : c ∈ children)
      (h : HasBag c target) : HasBag (node bag children) target

theorem hasBag_node_iff {bag target : List V} {children : List (DecompTree V)} :
    (node bag children).HasBag target ↔
      target = bag ∨ ∃ c ∈ children, c.HasBag target := by
  constructor
  · rintro (_ | ⟨_, hc, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, hc, h⟩
  · rintro (rfl | ⟨c, hc, h⟩)
    · exact HasBag.root _ _
    · exact HasBag.child _ hc h

/-- The root bag occurs as a bag. -/
theorem hasBag_rootBag (t : DecompTree V) : t.HasBag t.rootBag := by
  cases t with
  | node bag children => exact HasBag.root _ _

/-- A vertex occurs in some bag of the rose tree. -/
def Occurs (t : DecompTree V) (v : V) : Prop :=
  ∃ L, t.HasBag L ∧ v ∈ L

/-- Two vertices occur together in some bag of the rose tree. -/
def OccursPair (t : DecompTree V) (u v : V) : Prop :=
  ∃ L, t.HasBag L ∧ u ∈ L ∧ v ∈ L

theorem occurs_node_iff {bag : List V} {children : List (DecompTree V)} {v : V} :
    (node bag children).Occurs v ↔ v ∈ bag ∨ ∃ c ∈ children, c.Occurs v := by
  constructor
  · rintro ⟨L, hL, hv⟩
    rcases hasBag_node_iff.1 hL with rfl | ⟨c, hc, h⟩
    · exact Or.inl hv
    · exact Or.inr ⟨c, hc, L, h, hv⟩
  · rintro (hv | ⟨c, hc, L, hL, hv⟩)
    · exact ⟨bag, HasBag.root _ _, hv⟩
    · exact ⟨L, HasBag.child _ hc hL, hv⟩

theorem occurs_of_mem_rootBag {t : DecompTree V} {v : V}
    (hv : v ∈ t.rootBag) : t.Occurs v :=
  ⟨t.rootBag, t.hasBag_rootBag, hv⟩

theorem occurs_node_nil_iff {bag : List V} {v : V} :
    (node bag ([] : List (DecompTree V))).Occurs v ↔ v ∈ bag := by
  rw [occurs_node_iff]
  simp

section

variable [DecidableEq V]

/-- Every bag of the rose tree has at most `omega + 1` distinct vertices. -/
def HasWidth (t : DecompTree V) (omega : ℕ) : Prop :=
  ∀ L, t.HasBag L → L.toFinset.card ≤ omega + 1

theorem HasWidth.rootBag_card {t : DecompTree V} {omega : ℕ}
    (h : t.HasWidth omega) : t.rootBag.toFinset.card ≤ omega + 1 :=
  h t.rootBag t.hasBag_rootBag

theorem HasWidth.of_mem_children {bag : List V} {children : List (DecompTree V)}
    {omega : ℕ} (h : (node bag children).HasWidth omega)
    {c : DecompTree V} (hc : c ∈ children) : c.HasWidth omega :=
  fun L hL => h L (HasBag.child _ hc hL)

end

/-- Bag-injectivity of a vertex coloring on the rose tree: the coloring is
injective on every bag.  Rose-tree counterpart of
`TreeDecomposition.IsBagColoring`. -/
def IsBagColoring (t : DecompTree V) {k : ℕ} (color : V → Fin k) : Prop :=
  ∀ ⦃L⦄, t.HasBag L → Set.InjOn color {x | x ∈ L}

theorem IsBagColoring.rootBag {t : DecompTree V} {k : ℕ} {color : V → Fin k}
    (h : t.IsBagColoring color) : Set.InjOn color {x | x ∈ t.rootBag} :=
  h t.hasBag_rootBag

theorem IsBagColoring.of_mem_children {bag : List V}
    {children : List (DecompTree V)} {k : ℕ} {color : V → Fin k}
    (h : (node bag children).IsBagColoring color) {c : DecompTree V}
    (hc : c ∈ children) : c.IsBagColoring color :=
  fun _L hL => h (HasBag.child _ hc hL)

/-- The local running-intersection property of the rose tree: a vertex shared
by a node bag and a child subtree lies in the child bag, and a vertex
occurring below two distinct child branches lies in the node bag.  Together
with coverage this is the rooted form of the usual connectivity axiom of
tree-decompositions. -/
inductive RunningIntersection : DecompTree V → Prop
  | node {bag : List V} {children : List (DecompTree V)}
      (hdown : ∀ c ∈ children, ∀ v ∈ bag, c.Occurs v → v ∈ c.rootBag)
      (hpair : children.Pairwise
        (fun c₁ c₂ => ∀ v, c₁.Occurs v → c₂.Occurs v → v ∈ bag))
      (hchildren : ∀ c ∈ children, RunningIntersection c) :
      RunningIntersection (node bag children)

/-- A childless node satisfies the running-intersection property. -/
theorem runningIntersection_node_nil (bag : List V) :
    (node bag ([] : List (DecompTree V))).RunningIntersection :=
  .node (fun c hc => by simp at hc) List.Pairwise.nil (fun c hc => by simp at hc)

/-- Validity of a rose-tree presentation as a tree-decomposition of `G`.
Algorithms run on the raw `DecompTree`; correctness theorems consume this
predicate. -/
structure IsDecompFor (t : DecompTree V) (G : SimpleGraph V) : Prop where
  vertexCoverage : ∀ v, t.Occurs v
  edgeCoverage : ∀ ⦃u v⦄, G.Adj u v → t.OccursPair u v
  runningIntersection : t.RunningIntersection

end DecompTree

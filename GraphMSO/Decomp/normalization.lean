import GraphMSO.Decomp.realization

/-!
# Nice-decomposition normalization

This file formalizes the constructive core of the standard normalization
algorithm from `Courcelle/nice_tree_decomp.tex`.

The first layer is entirely code-facing.  `InductiveNiceTree.changeRoot`
inserts the one-vertex introduce/forget path between two finite bags, and
`RootedTreeDecomposition.normalizeCodeAt` processes the rooted input tree in
postorder, joining all normalized child branches with binary join nodes.
-/

open scoped Classical

universe u

namespace InductiveNiceTree

variable {V : Type u}

/-- A bag occurs at some position of a constructor code. -/
def HasBag {bag : Set V} (tree : InductiveNiceTree V bag) (target : Set V) : Prop :=
  ∃ n : Node tree, nodeBag tree n = target

/-- Every vertex appearing anywhere in a code belongs to `allowed`. -/
def VerticesSubset {bag : Set V} (tree : InductiveNiceTree V bag)
    (allowed : Set V) : Prop :=
  ∀ n : Node tree, nodeBag tree n ⊆ allowed

/-- A vertex occurs in some code bag. -/
def Occurs {bag : Set V} (tree : InductiveNiceTree V bag) (v : V) : Prop :=
  ∃ n : Node tree, v ∈ nodeBag tree n

/-- The positions whose bags contain `v` induce a preconnected subgraph. -/
def OccPreconnected {bag : Set V} (tree : InductiveNiceTree V bag) (v : V) : Prop :=
  (tree.graph.induce {n : Node tree | v ∈ nodeBag tree n}).Preconnected

/-- Number of constructor nodes in a coded nice tree. -/
def size {bag : Set V} : InductiveNiceTree V bag → ℕ
  | .leaf => 1
  | .introduce _ child _ => child.size + 1
  | .forget _ child _ => child.size + 1
  | .join left right => left.size + right.size + 1

/-- The structural size is exactly the cardinality of the code-node type. -/
theorem card_node_eq_size {bag : Set V} (tree : InductiveNiceTree V bag) :
    Fintype.card (Node tree) = tree.size := by
  induction tree with
  | leaf => simp [Node, size]
  | introduce v child fresh ih =>
      simp [Node, size, ih, Fintype.card_option]
  | forget v child present ih =>
      simp [Node, size, ih, Fintype.card_option]
  | join left right ihleft ihrigh =>
      simp [Node, size, ihleft, ihrigh, Fintype.card_option,
        Fintype.card_sum]

theorem toFinset_card_eq_ncard [Fintype V] (s : Set V) :
    s.toFinset.card = s.ncard := by
  calc
    s.toFinset.card = (s.toFinset : Set V).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = s.ncard := congrArg Set.ncard (Set.coe_toFinset s)

theorem VerticesSubset.mono {bag : Set V} {tree : InductiveNiceTree V bag}
    {small large : Set V} (h : tree.VerticesSubset small) (hsub : small ⊆ large) :
    tree.VerticesSubset large :=
  fun n _v hv => hsub (h n hv)

/-- The root-index bag occurs at the code root. -/
theorem hasBag_root {bag : Set V} (tree : InductiveNiceTree V bag) :
    tree.HasBag bag :=
  ⟨root tree, nodeBag_root tree⟩

/-- Transport the root-bag index of a constructor-coded nice tree. -/
def castRoot {A B : Set V} (h : A = B) (tree : InductiveNiceTree V A) :
    InductiveNiceTree V B :=
  h ▸ tree

@[simp] theorem castRoot_rfl {A : Set V} (tree : InductiveNiceTree V A) :
  castRoot rfl tree = tree :=
  rfl

@[simp] theorem size_castRoot {A B : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) :
    (castRoot h tree).size = tree.size := by
  subst B
  rfl

/-- Reindexing a coded tree does not change its width property. -/
theorem hasWidth_castRoot_iff {A B : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) (omega : ℕ) :
    (castRoot h tree).HasWidth omega ↔ tree.HasWidth omega := by
  subst B
  rfl

/-- Root-index transport preserves every occurring bag. -/
theorem hasBag_castRoot_iff {A B target : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) :
    (castRoot h tree).HasBag target ↔ tree.HasBag target := by
  subst B
  rfl

theorem verticesSubset_castRoot_iff {A B allowed : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) :
    (castRoot h tree).VerticesSubset allowed ↔ tree.VerticesSubset allowed := by
  subst B
  rfl

theorem occurs_castRoot_iff {A B : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) (v : V) :
    (castRoot h tree).Occurs v ↔ tree.Occurs v := by
  subst B
  rfl

theorem occPreconnected_castRoot_iff {A B : Set V} (h : A = B)
    (tree : InductiveNiceTree V A) (v : V) :
    (castRoot h tree).OccPreconnected v ↔ tree.OccPreconnected v := by
  subst B
  rfl

theorem introduce_occurs_iff {bag : Set V} (new : V)
    (tree : InductiveNiceTree V bag) (fresh : new ∉ bag) (v : V) :
    (InductiveNiceTree.introduce new tree fresh).Occurs v ↔
      tree.Occurs v ∨ v = new := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | none =>
        have : v ∈ nodeBag tree (root tree) ∪ {new} := by
          simpa [nodeBag] using hn
        rcases this with hchild | hnew
        · exact Or.inl ⟨root tree, hchild⟩
        · exact Or.inr (by simpa using hnew)
    | some n =>
        exact Or.inl ⟨n, by simpa [nodeBag] using hn⟩
  · rintro (⟨n, hn⟩ | hnew)
    · exact ⟨some n, by simpa [nodeBag] using hn⟩
    · exact ⟨root (InductiveNiceTree.introduce new tree fresh), by
        change v ∈ nodeBag tree (root tree) ∪ {new}
        exact Or.inr (by simpa using hnew)⟩

theorem forget_occurs_iff {bag : Set V} (old : V)
    (tree : InductiveNiceTree V bag) (present : old ∈ bag) (v : V) :
    (InductiveNiceTree.forget old tree present).Occurs v ↔ tree.Occurs v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | none =>
        exact ⟨root tree, by
          rw [nodeBag_root]
          exact (by simpa [nodeBag] using hn : v ∈ bag \ {old}).1⟩
    | some n => exact ⟨n, by simpa [nodeBag] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨some n, by simpa [nodeBag] using hn⟩

theorem leaf_verticesSubset (allowed : Set V) :
    (InductiveNiceTree.leaf : InductiveNiceTree V ∅).VerticesSubset allowed := by
  intro n
  cases n
  simp [nodeBag]

theorem leaf_occPreconnected (v : V) :
    (InductiveNiceTree.leaf : InductiveNiceTree V ∅).OccPreconnected v := by
  intro x _y
  rcases x with ⟨x, hx⟩
  cases x
  simp [nodeBag] at hx

theorem introduce_verticesSubset {bag allowed : Set V} (v : V)
    (tree : InductiveNiceTree V bag) (fresh : v ∉ bag)
    (htree : tree.VerticesSubset allowed) (hroot : bag ∪ {v} ⊆ allowed) :
    (InductiveNiceTree.introduce v tree fresh).VerticesSubset allowed := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hroot
  | some n => simpa [nodeBag] using htree n

theorem forget_verticesSubset {bag allowed : Set V} (v : V)
    (tree : InductiveNiceTree V bag) (present : v ∈ bag)
    (htree : tree.VerticesSubset allowed) (hroot : bag \ {v} ⊆ allowed) :
    (InductiveNiceTree.forget v tree present).VerticesSubset allowed := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hroot
  | some n => simpa [nodeBag] using htree n

theorem join_verticesSubset {bag allowed : Set V}
    (left right : InductiveNiceTree V bag)
    (hleft : left.VerticesSubset allowed) (hright : right.VerticesSubset allowed) :
    (InductiveNiceTree.join left right).VerticesSubset allowed := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hleft (root left)
  | some n =>
      cases n with
      | inl n => simpa [nodeBag] using hleft n
      | inr n => simpa [nodeBag] using hright n

/-- Map reachability inside a child occurrence set through an introduce
constructor. -/
theorem introduce_map_occReachable {bag : Set V} (new : V)
    (tree : InductiveNiceTree V bag) (fresh : new ∉ bag) (v : V)
    {x y : Node tree} (hx : v ∈ nodeBag tree x) (hy : v ∈ nodeBag tree y)
    (hreach : (tree.graph.induce {n : Node tree | v ∈ nodeBag tree n}).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩) :
    ((InductiveNiceTree.introduce new tree fresh).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.introduce new tree fresh) n}).Reachable
      ⟨some x, by simpa [nodeBag] using hx⟩
      ⟨some y, by simpa [nodeBag] using hy⟩ := by
  let hom :
      tree.graph.induce {n : Node tree | v ∈ nodeBag tree n} →g
        (InductiveNiceTree.introduce new tree fresh).graph.induce
          {n | v ∈ nodeBag (InductiveNiceTree.introduce new tree fresh) n} := {
    toFun := fun n => ⟨some n.1, by
      change v ∈ nodeBag tree n.1
      exact n.2⟩
    map_rel' := by
      intro x y hxy
      change (InductiveNiceTree.introduce new tree fresh).graph.Adj
        (some x.1) (some y.1)
      rcases (graph_adj tree x.1 y.1).1 hxy with hxy | hyx
      · apply (graph_adj _ _ _).2 (Or.inl _)
        change some y.1 ∈ (tree.children x.1).map some
        exact List.mem_map.mpr ⟨y.1, hxy, rfl⟩
      · apply (graph_adj _ _ _).2 (Or.inr _)
        change some x.1 ∈ (tree.children y.1).map some
        exact List.mem_map.mpr ⟨x.1, hyx, rfl⟩ }
  exact hreach.map hom

/-- Introduce preserves occurrence connectedness when a newly present root
vertex that already occurs below is also present in the child root. -/
theorem introduce_occPreconnected {bag : Set V} (new : V)
    (tree : InductiveNiceTree V bag) (fresh : new ∉ bag) (v : V)
    (hconn : tree.OccPreconnected v)
    (hattach : v ∈ bag ∪ {new} → tree.Occurs v → v ∈ bag) :
    (InductiveNiceTree.introduce new tree fresh).OccPreconnected v := by
  intro x y
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | none =>
      cases y with
      | none => exact SimpleGraph.Reachable.refl _
      | some y =>
          have hvroot : v ∈ bag ∪ {new} := by simpa [nodeBag] using hx
          have hvy : v ∈ nodeBag tree y := by simpa [nodeBag] using hy
          have hvchildRoot : v ∈ nodeBag tree (root tree) := by
            rw [nodeBag_root]
            exact hattach hvroot ⟨y, hvy⟩
          have hedge :
              ((InductiveNiceTree.introduce new tree fresh).graph.induce
                {n | v ∈ nodeBag (InductiveNiceTree.introduce new tree fresh) n}).Adj
                ⟨none, hx⟩ ⟨some (root tree), by
                  simpa [nodeBag] using hvchildRoot⟩ := by
            change (InductiveNiceTree.introduce new tree fresh).graph.Adj
              none (some (root tree))
            apply (graph_adj _ _ _).2 (Or.inl _)
            change some (root tree) ∈ [some (root tree)]
            simp
          exact SimpleGraph.Adj.reachable hedge |>.trans
            (introduce_map_occReachable new tree fresh v hvchildRoot hvy
              (hconn ⟨root tree, hvchildRoot⟩ ⟨y, hvy⟩))
  | some x =>
      have hvx : v ∈ nodeBag tree x := by simpa [nodeBag] using hx
      cases y with
      | some y =>
          have hvy : v ∈ nodeBag tree y := by simpa [nodeBag] using hy
          exact introduce_map_occReachable new tree fresh v hvx hvy
            (hconn ⟨x, hvx⟩ ⟨y, hvy⟩)
      | none =>
          have hvroot : v ∈ bag ∪ {new} := by simpa [nodeBag] using hy
          have hvchildRoot : v ∈ nodeBag tree (root tree) := by
            rw [nodeBag_root]
            exact hattach hvroot ⟨x, hvx⟩
          have hedge :
              ((InductiveNiceTree.introduce new tree fresh).graph.induce
                {n | v ∈ nodeBag (InductiveNiceTree.introduce new tree fresh) n}).Adj
                ⟨none, hy⟩ ⟨some (root tree), by
                  simpa [nodeBag] using hvchildRoot⟩ := by
            change (InductiveNiceTree.introduce new tree fresh).graph.Adj
              none (some (root tree))
            apply (graph_adj _ _ _).2 (Or.inl _)
            change some (root tree) ∈ [some (root tree)]
            simp
          exact (introduce_map_occReachable new tree fresh v hvx hvchildRoot
            (hconn ⟨x, hvx⟩ ⟨root tree, hvchildRoot⟩)).trans
              (SimpleGraph.Adj.reachable hedge).symm

/-- Map reachability inside a child occurrence set through a forget
constructor. -/
theorem forget_map_occReachable {bag : Set V} (old : V)
    (tree : InductiveNiceTree V bag) (present : old ∈ bag) (v : V)
    {x y : Node tree} (hx : v ∈ nodeBag tree x) (hy : v ∈ nodeBag tree y)
    (hreach : (tree.graph.induce {n : Node tree | v ∈ nodeBag tree n}).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩) :
    ((InductiveNiceTree.forget old tree present).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.forget old tree present) n}).Reachable
      ⟨some x, by simpa [nodeBag] using hx⟩
      ⟨some y, by simpa [nodeBag] using hy⟩ := by
  let hom :
      tree.graph.induce {n : Node tree | v ∈ nodeBag tree n} →g
        (InductiveNiceTree.forget old tree present).graph.induce
          {n | v ∈ nodeBag (InductiveNiceTree.forget old tree present) n} := {
    toFun := fun n => ⟨some n.1, by
      change v ∈ nodeBag tree n.1
      exact n.2⟩
    map_rel' := by
      intro x y hxy
      change (InductiveNiceTree.forget old tree present).graph.Adj
        (some x.1) (some y.1)
      rcases (graph_adj tree x.1 y.1).1 hxy with hxy | hyx
      · apply (graph_adj _ _ _).2 (Or.inl _)
        change some y.1 ∈ (tree.children x.1).map some
        exact List.mem_map.mpr ⟨y.1, hxy, rfl⟩
      · apply (graph_adj _ _ _).2 (Or.inr _)
        change some x.1 ∈ (tree.children y.1).map some
        exact List.mem_map.mpr ⟨x.1, hyx, rfl⟩ }
  exact hreach.map hom

/-- Forgetting a vertex preserves connectedness of every remaining
occurrence set. -/
theorem forget_occPreconnected {bag : Set V} (old : V)
    (tree : InductiveNiceTree V bag) (present : old ∈ bag) (v : V)
    (hconn : tree.OccPreconnected v) :
    (InductiveNiceTree.forget old tree present).OccPreconnected v := by
  intro x y
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | none =>
      cases y with
      | none => exact SimpleGraph.Reachable.refl _
      | some y =>
          have hvroot : v ∈ nodeBag tree (root tree) := by
            rw [nodeBag_root]
            exact (by simpa [nodeBag] using hx : v ∈ bag \ {old}).1
          have hvy : v ∈ nodeBag tree y := by simpa [nodeBag] using hy
          have hedge :
              ((InductiveNiceTree.forget old tree present).graph.induce
                {n | v ∈ nodeBag (InductiveNiceTree.forget old tree present) n}).Adj
                ⟨none, hx⟩ ⟨some (root tree), by
                  simpa [nodeBag] using hvroot⟩ := by
            change (InductiveNiceTree.forget old tree present).graph.Adj
              none (some (root tree))
            apply (graph_adj _ _ _).2 (Or.inl _)
            change some (root tree) ∈ [some (root tree)]
            simp
          exact SimpleGraph.Adj.reachable hedge |>.trans
            (forget_map_occReachable old tree present v hvroot hvy
              (hconn ⟨root tree, hvroot⟩ ⟨y, hvy⟩))
  | some x =>
      have hvx : v ∈ nodeBag tree x := by simpa [nodeBag] using hx
      cases y with
      | some y =>
          have hvy : v ∈ nodeBag tree y := by simpa [nodeBag] using hy
          exact forget_map_occReachable old tree present v hvx hvy
            (hconn ⟨x, hvx⟩ ⟨y, hvy⟩)
      | none =>
          have hvroot : v ∈ nodeBag tree (root tree) := by
            rw [nodeBag_root]
            exact (by simpa [nodeBag] using hy : v ∈ bag \ {old}).1
          have hedge :
              ((InductiveNiceTree.forget old tree present).graph.induce
                {n | v ∈ nodeBag (InductiveNiceTree.forget old tree present) n}).Adj
                ⟨none, hy⟩ ⟨some (root tree), by
                  simpa [nodeBag] using hvroot⟩ := by
            change (InductiveNiceTree.forget old tree present).graph.Adj
              none (some (root tree))
            apply (graph_adj _ _ _).2 (Or.inl _)
            change some (root tree) ∈ [some (root tree)]
            simp
          exact (forget_map_occReachable old tree present v hvx hvroot
            (hconn ⟨x, hvx⟩ ⟨root tree, hvroot⟩)).trans
              (SimpleGraph.Adj.reachable hedge).symm

/-- Every child occurrence remains below an introduce node. -/
theorem HasBag.introduce {bag target : Set V} {tree : InductiveNiceTree V bag}
    (h : tree.HasBag target) (v : V) (fresh : v ∉ bag) :
    (InductiveNiceTree.introduce v tree fresh).HasBag target := by
  obtain ⟨n, hn⟩ := h
  exact ⟨some n, by simpa [nodeBag] using hn⟩

/-- Every child occurrence remains below a forget node. -/
theorem HasBag.forget {bag target : Set V} {tree : InductiveNiceTree V bag}
    (h : tree.HasBag target) (v : V) (present : v ∈ bag) :
    (InductiveNiceTree.forget v tree present).HasBag target := by
  obtain ⟨n, hn⟩ := h
  exact ⟨some n, by simpa [nodeBag] using hn⟩

/-- Every left occurrence remains below a join node. -/
theorem HasBag.join_left {bag target : Set V}
    {left right : InductiveNiceTree V bag} (h : left.HasBag target) :
    (InductiveNiceTree.join left right).HasBag target := by
  obtain ⟨n, hn⟩ := h
  exact ⟨some (Sum.inl n), by simpa [nodeBag] using hn⟩

/-- Every right occurrence remains below a join node. -/
theorem HasBag.join_right {bag target : Set V}
    {left right : InductiveNiceTree V bag} (h : right.HasBag target) :
    (InductiveNiceTree.join left right).HasBag target := by
  obtain ⟨n, hn⟩ := h
  exact ⟨some (Sum.inr n), by simpa [nodeBag] using hn⟩

/-- The leaf code has every width bound. -/
theorem leaf_hasWidth (omega : ℕ) :
    (InductiveNiceTree.leaf : InductiveNiceTree V ∅).HasWidth omega := by
  intro n
  cases n
  simp [nodeBag]

/-- Width is preserved by an introduce constructor when its new root bag has
the requested bound. -/
theorem introduce_hasWidth [Finite V] {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (fresh : v ∉ bag) (omega : ℕ)
    (hchild : child.HasWidth omega) (hroot : (bag ∪ {v}).ncard ≤ omega + 1) :
    (InductiveNiceTree.introduce v child fresh).HasWidth omega := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hroot
  | some n => simpa [nodeBag] using hchild n

/-- Width is preserved by a forget constructor when its new root bag has the
requested bound. -/
theorem forget_hasWidth [Finite V] {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (present : v ∈ bag) (omega : ℕ)
    (hchild : child.HasWidth omega) (hroot : (bag \ {v}).ncard ≤ omega + 1) :
    (InductiveNiceTree.forget v child present).HasWidth omega := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hroot
  | some n => simpa [nodeBag] using hchild n

/-- Joining equal-bag width-bounded codes preserves the bound. -/
theorem join_hasWidth [Finite V] {bag : Set V}
    (left right : InductiveNiceTree V bag) (omega : ℕ)
    (hleft : left.HasWidth omega) (hright : right.HasWidth omega) :
    (InductiveNiceTree.join left right).HasWidth omega := by
  intro n
  cases n with
  | none => simpa [nodeBag] using hleft (root left)
  | some n =>
      cases n with
      | inl n => simpa [nodeBag] using hleft n
      | inr n => simpa [nodeBag] using hright n

/-- Forget every vertex of a duplicate-free list, one vertex at a time. -/
noncomputable def forgetList {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup) :
    InductiveNiceTree V (bag \ (xs.toFinset : Set V)) :=
  match xs with
  | [] => castRoot (by simp) tree
  | v :: rest => by
      classical
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      let child := forgetList rest tree hrest hnodup.2
      have hvbag : v ∈ bag := hsub v (by simp)
      have hvchild : v ∈ bag \ (rest.toFinset : Set V) := by
        exact ⟨hvbag, by simpa using hnodup.1⟩
      let result := InductiveNiceTree.forget v child hvchild
      exact castRoot (by ext x; simp [and_assoc, and_comm]) result

/-- Forget paths preserve a width bound when the starting bag has that
bound. -/
theorem forgetList_hasWidth [Finite V] {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup) (omega : ℕ)
    (htree : tree.HasWidth omega) (hbag : bag.ncard ≤ omega + 1) :
    (forgetList xs tree hsub hnodup).HasWidth omega := by
  induction xs with
  | nil =>
      exact (hasWidth_castRoot_iff _ _ _).2 htree
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hchild := ih hrest hnodup.2
      have hvbag : v ∈ bag := hsub v (by simp)
      have hvchild : v ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      have hroot :
          ((bag \ (rest.toFinset : Set V)) \ {v}).ncard ≤ omega + 1 :=
        (Set.ncard_le_ncard (by intro x hx; exact hx.1.1)).trans hbag
      rw [forgetList]
      exact (hasWidth_castRoot_iff _ _ _).2
        (forget_hasWidth v _ hvchild omega hchild hroot)

/-- A forget path preserves all bags occurring in its reused child code. -/
theorem forgetList_hasBag {bag target : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup)
    (hbag : tree.HasBag target) :
    (forgetList xs tree hsub hnodup).HasBag target := by
  induction xs with
  | nil =>
      exact (hasBag_castRoot_iff _ _).2 hbag
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hvbag : v ∈ bag := hsub v (by simp)
      have hvchild : v ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      rw [forgetList]
      apply (hasBag_castRoot_iff _ _).2
      exact (ih hrest hnodup.2).forget v hvchild

theorem forgetList_verticesSubset {bag allowed : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup)
    (htree : tree.VerticesSubset allowed) (hbag : bag ⊆ allowed) :
    (forgetList xs tree hsub hnodup).VerticesSubset allowed := by
  induction xs with
  | nil => exact (verticesSubset_castRoot_iff _ _).2 htree
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hvbag : v ∈ bag := hsub v (by simp)
      have hvchild : v ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      rw [forgetList]
      apply (verticesSubset_castRoot_iff _ _).2
      apply forget_verticesSubset
      · exact ih hrest hnodup.2
      · intro x hx
        exact hbag hx.1.1

theorem forgetList_occurs_iff {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup) (v : V) :
    (forgetList xs tree hsub hnodup).Occurs v ↔ tree.Occurs v := by
  induction xs with
  | nil => exact occurs_castRoot_iff _ tree v
  | cons old rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hvbag : old ∈ bag := hsub old (by simp)
      have hvchild : old ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      rw [forgetList]
      exact (occurs_castRoot_iff _ _ v).trans
        ((forget_occurs_iff old _ hvchild v).trans
          (ih hrest hnodup.2))

theorem forgetList_occPreconnected {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup) (v : V)
    (hconn : tree.OccPreconnected v) :
    (forgetList xs tree hsub hnodup).OccPreconnected v := by
  induction xs with
  | nil => exact (occPreconnected_castRoot_iff _ tree v).2 hconn
  | cons old rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hvbag : old ∈ bag := hsub old (by simp)
      have hvchild : old ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      rw [forgetList]
      apply (occPreconnected_castRoot_iff _ _ v).2
      exact forget_occPreconnected old _ hvchild v
        (ih hrest hnodup.2)

theorem forgetList_size {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hsub : ∀ x ∈ xs, x ∈ bag) (hnodup : xs.Nodup) :
    (forgetList xs tree hsub hnodup).size = tree.size + xs.length := by
  induction xs with
  | nil =>
      rw [forgetList, size_castRoot]
      simp
  | cons old rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∈ bag := by
        intro x hx
        exact hsub x (by simp [hx])
      have hvbag : old ∈ bag := hsub old (by simp)
      have hvchild : old ∈ bag \ (rest.toFinset : Set V) :=
        ⟨hvbag, by simpa using hnodup.1⟩
      rw [forgetList, size_castRoot]
      change (forgetList rest tree hrest hnodup.2).size + 1 = _
      rw [ih hrest hnodup.2]
      simp [Nat.add_assoc]

/-- Introduce every vertex of a duplicate-free list, one vertex at a time. -/
noncomputable def introduceList {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup) :
    InductiveNiceTree V (bag ∪ (xs.toFinset : Set V)) :=
  match xs with
  | [] => castRoot (by simp) tree
  | v :: rest => by
      classical
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      let child := introduceList rest tree hrest hnodup.2
      have hvbag : v ∉ bag := hdisjoint v (by simp)
      have hvfresh : v ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      let result := InductiveNiceTree.introduce v child hvfresh
      exact castRoot (by ext x; simp [or_comm]) result

/-- Introduce paths preserve a width bound when their final bag has that
bound. -/
theorem introduceList_hasWidth [Finite V] {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup) (omega : ℕ)
    (htree : tree.HasWidth omega)
    (hfinal : (bag ∪ (xs.toFinset : Set V)).ncard ≤ omega + 1) :
    (introduceList xs tree hdisjoint hnodup).HasWidth omega := by
  induction xs with
  | nil =>
      exact (hasWidth_castRoot_iff _ _ _).2 htree
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : v ∉ bag := hdisjoint v (by simp)
      have hvfresh : v ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      have hrestFinal :
          (bag ∪ (rest.toFinset : Set V)).ncard ≤ omega + 1 :=
        (Set.ncard_le_ncard (by
          intro x hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · apply Or.inr
            change x ∈ (v :: rest).toFinset
            rw [List.mem_toFinset]
            exact List.mem_cons_of_mem v (by simpa using hx))).trans
          hfinal
      have hroot :
          ((bag ∪ (rest.toFinset : Set V)) ∪ {v}).ncard ≤ omega + 1 := by
        simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hfinal
      rw [introduceList]
      exact (hasWidth_castRoot_iff _ _ _).2
        (introduce_hasWidth v _ hvfresh omega
          (ih hrest hnodup.2 hrestFinal) hroot)

/-- An introduce path preserves all bags occurring in its reused child code. -/
theorem introduceList_hasBag {bag target : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup)
    (hbag : tree.HasBag target) :
    (introduceList xs tree hdisjoint hnodup).HasBag target := by
  induction xs with
  | nil =>
      exact (hasBag_castRoot_iff _ _).2 hbag
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : v ∉ bag := hdisjoint v (by simp)
      have hvfresh : v ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      rw [introduceList]
      apply (hasBag_castRoot_iff _ _).2
      exact (ih hrest hnodup.2).introduce v hvfresh

theorem introduceList_verticesSubset {bag allowed : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup)
    (htree : tree.VerticesSubset allowed)
    (hfinal : bag ∪ (xs.toFinset : Set V) ⊆ allowed) :
    (introduceList xs tree hdisjoint hnodup).VerticesSubset allowed := by
  induction xs with
  | nil => exact (verticesSubset_castRoot_iff _ _).2 htree
  | cons v rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : v ∉ bag := hdisjoint v (by simp)
      have hvfresh : v ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      have hrestFinal : bag ∪ (rest.toFinset : Set V) ⊆ allowed := by
        intro x hx
        apply hfinal
        rcases hx with hx | hx
        · exact Or.inl hx
        · apply Or.inr
          change x ∈ (v :: rest).toFinset
          rw [List.mem_toFinset]
          exact List.mem_cons_of_mem v (by simpa using hx)
      have hroot : (bag ∪ (rest.toFinset : Set V)) ∪ {v} ⊆ allowed := by
        intro x hx
        apply hfinal
        rcases hx with (hx | hx) | rfl
        · exact Or.inl hx
        · exact Or.inr (by simpa using
            (show x ∈ (v :: rest).toFinset by
              rw [List.mem_toFinset]
              exact List.mem_cons_of_mem v (by simpa using hx)))
        · exact Or.inr (by simp)
      rw [introduceList]
      apply (verticesSubset_castRoot_iff _ _).2
      exact introduce_verticesSubset v _ hvfresh
        (ih hrest hnodup.2 hrestFinal) hroot

theorem introduceList_occurs_iff {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup) (v : V) :
    (introduceList xs tree hdisjoint hnodup).Occurs v ↔
      tree.Occurs v ∨ v ∈ xs := by
  induction xs with
  | nil => simpa using (occurs_castRoot_iff (by simp) tree v)
  | cons new rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : new ∉ bag := hdisjoint new (by simp)
      have hvfresh : new ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      rw [introduceList]
      rw [occurs_castRoot_iff, introduce_occurs_iff, ih hrest hnodup.2]
      simp only [List.mem_cons]
      tauto

/-- An introduce path preserves occurrence connectedness provided every
introduced vertex is genuinely new to the reused child code. -/
theorem introduceList_occPreconnected {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup) (v : V)
    (hconn : tree.OccPreconnected v)
    (hnew : ∀ x ∈ xs, ¬ tree.Occurs x) :
    (introduceList xs tree hdisjoint hnodup).OccPreconnected v := by
  induction xs with
  | nil => exact (occPreconnected_castRoot_iff _ tree v).2 hconn
  | cons new rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : new ∉ bag := hdisjoint new (by simp)
      have hvfresh : new ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      have hnewRest : ∀ x ∈ rest, ¬ tree.Occurs x := by
        intro x hx
        exact hnew x (by simp [hx])
      let child := introduceList rest tree hrest hnodup.2
      have hchildConn : child.OccPreconnected v :=
        ih hrest hnodup.2 hnewRest
      have hnewNotBelow : ¬ child.Occurs new := by
        intro hocc
        rcases (introduceList_occurs_iff rest tree hrest hnodup.2 new).1 hocc with
          hocc | hmem
        · exact hnew new (by simp) hocc
        · exact hnodup.1 hmem
      rw [introduceList]
      apply (occPreconnected_castRoot_iff _ _ v).2
      apply introduce_occPreconnected new child hvfresh v hchildConn
      intro hvroot hvbelow
      rcases hvroot with hvroot | hvnew
      · exact hvroot
      · have : v = new := by simpa using hvnew
        subst v
        exact (hnewNotBelow hvbelow).elim

theorem introduceList_size {bag : Set V} (xs : List V)
    (tree : InductiveNiceTree V bag)
    (hdisjoint : ∀ x ∈ xs, x ∉ bag) (hnodup : xs.Nodup) :
    (introduceList xs tree hdisjoint hnodup).size = tree.size + xs.length := by
  induction xs with
  | nil =>
      rw [introduceList, size_castRoot]
      simp
  | cons new rest ih =>
      rw [List.nodup_cons] at hnodup
      have hrest : ∀ x ∈ rest, x ∉ bag := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hvbag : new ∉ bag := hdisjoint new (by simp)
      have hvfresh : new ∉ bag ∪ (rest.toFinset : Set V) := by
        intro hmem
        rcases hmem with hmem | hmem
        · exact hvbag hmem
        · exact hnodup.1 (by simpa using hmem)
      rw [introduceList, size_castRoot]
      change (introduceList rest tree hrest hnodup.2).size + 1 = _
      rw [ih hrest hnodup.2]
      simp [Nat.add_assoc]

/--
Change the root bag from `B` to `A` by first forgetting `B \ A` and then
introducing `A \ B`.  The supplied tree is reused as the bottom of the path.
-/
noncomputable def changeRoot (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) :
    InductiveNiceTree V (A : Set V) := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  let forgotten := forgetList removed.toList tree hremoved removed.nodup_toList
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hxadd').2
    exact hxnotB hxremain.1
  let introduced := introduceList added.toList forgotten hdisjoint added.nodup_toList
  exact castRoot (by
    ext x
    simp [removed, added, Finset.toList_toFinset]
    tauto) introduced

/-- `changeRoot` preserves a width bound provided both endpoint bags satisfy
it. -/
theorem changeRoot_hasWidth [Finite V] (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) (omega : ℕ)
    (htree : tree.HasWidth omega)
    (hA : (A : Set V).ncard ≤ omega + 1)
    (hB : (B : Set V).ncard ≤ omega + 1) :
    (changeRoot A B tree).HasWidth omega := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  have hforgotten :
      (forgetList removed.toList tree hremoved removed.nodup_toList).HasWidth omega :=
    forgetList_hasWidth _ _ _ _ omega htree hB
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    exact (Finset.mem_sdiff.mp hxadd').2 hxremain.1
  have hfinal :
      (((B : Set V) \ (removed.toList.toFinset : Set V)) ∪
        (added.toList.toFinset : Set V)).ncard ≤ omega + 1 := by
    have hsubset :
        ((B : Set V) \ (removed.toList.toFinset : Set V)) ∪
            (added.toList.toFinset : Set V) ⊆ (A : Set V) := by
      intro x hx
      rcases hx with hx | hx
      · have hxnotRemoved : x ∉ removed := by
          simpa [Finset.toList_toFinset] using hx.2
        have hxB : x ∈ B := hx.1
        by_contra hxA
        exact hxnotRemoved (Finset.mem_sdiff.mpr ⟨hxB, hxA⟩)
      · have hxAdded : x ∈ added := by
          simpa [Finset.toList_toFinset] using hx
        exact (Finset.mem_sdiff.mp hxAdded).1
    exact (Set.ncard_le_ncard hsubset).trans hA
  have hintroduced := introduceList_hasWidth added.toList
    (forgetList removed.toList tree hremoved removed.nodup_toList)
    hdisjoint added.nodup_toList omega hforgotten hfinal
  unfold changeRoot
  exact (hasWidth_castRoot_iff _ _ _).2 hintroduced

/-- Changing a root reuses the entire supplied child code. -/
theorem changeRoot_hasBag (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) (target : Set V)
    (hbag : tree.HasBag target) :
    (changeRoot A B tree).HasBag target := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  let forgotten := forgetList removed.toList tree hremoved removed.nodup_toList
  have hforgotten : forgotten.HasBag target :=
    forgetList_hasBag _ _ _ _ hbag
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    exact (Finset.mem_sdiff.mp hxadd').2 hxremain.1
  have hintroduced := introduceList_hasBag added.toList forgotten
    hdisjoint added.nodup_toList hforgotten
  unfold changeRoot
  exact (hasBag_castRoot_iff _ _).2 hintroduced

theorem changeRoot_verticesSubset (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) (allowed : Set V)
    (htree : tree.VerticesSubset allowed)
    (hA : (A : Set V) ⊆ allowed) (hB : (B : Set V) ⊆ allowed) :
    (changeRoot A B tree).VerticesSubset allowed := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  let forgotten := forgetList removed.toList tree hremoved removed.nodup_toList
  have hforgotten : forgotten.VerticesSubset allowed :=
    forgetList_verticesSubset _ _ _ _ htree hB
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    exact (Finset.mem_sdiff.mp hxadd').2 hxremain.1
  have hfinal :
      ((B : Set V) \ (removed.toList.toFinset : Set V)) ∪
          (added.toList.toFinset : Set V) ⊆ allowed := by
    intro x hx
    rcases hx with hx | hx
    · exact hB hx.1
    · have hxAdded : x ∈ A := by
        have : x ∈ added := by simpa [Finset.toList_toFinset] using hx
        exact (Finset.mem_sdiff.mp this).1
      exact hA hxAdded
  have hintroduced := introduceList_verticesSubset added.toList forgotten
    hdisjoint added.nodup_toList hforgotten hfinal
  unfold changeRoot
  exact (verticesSubset_castRoot_iff _ _).2 hintroduced

/-- A root-change path preserves occurrence connectedness when vertices
introduced above the reused child do not already occur in that child. -/
theorem changeRoot_occPreconnected (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) (v : V)
    (hconn : tree.OccPreconnected v)
    (hnew : ∀ x ∈ A \ B, ¬ tree.Occurs x) :
    (changeRoot A B tree).OccPreconnected v := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  let forgotten := forgetList removed.toList tree hremoved removed.nodup_toList
  have hforgotten : forgotten.OccPreconnected v :=
    forgetList_occPreconnected removed.toList tree hremoved
      removed.nodup_toList v hconn
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    exact (Finset.mem_sdiff.mp hxadd').2 hxremain.1
  have hfreshOccurs : ∀ x ∈ added.toList, ¬ forgotten.Occurs x := by
    intro x hxadd hocc
    have hxadd' : x ∈ A \ B := by simpa [added] using hxadd
    apply hnew x hxadd'
    exact (forgetList_occurs_iff removed.toList tree hremoved
      removed.nodup_toList x).1 hocc
  have hintroduced := introduceList_occPreconnected added.toList forgotten
    hdisjoint added.nodup_toList v hforgotten hfreshOccurs
  unfold changeRoot
  exact (occPreconnected_castRoot_iff _ _ v).2 hintroduced

/-- Exact constructor cost of changing one finite root bag into another. -/
theorem changeRoot_size (A B : Finset V)
    (tree : InductiveNiceTree V (B : Set V)) :
    (changeRoot A B tree).size =
      tree.size + (B \ A).card + (A \ B).card := by
  classical
  let removed : Finset V := B \ A
  have hremoved : ∀ x ∈ removed.toList, x ∈ (B : Set V) := by
    intro x hx
    have hx' : x ∈ removed := by simpa using hx
    exact (Finset.mem_sdiff.mp hx').1
  let forgotten := forgetList removed.toList tree hremoved removed.nodup_toList
  let added : Finset V := A \ B
  have hdisjoint : ∀ x ∈ added.toList,
      x ∉ ((B : Set V) \ (removed.toList.toFinset : Set V)) := by
    intro x hxadd hxremain
    have hxadd' : x ∈ added := by simpa using hxadd
    exact (Finset.mem_sdiff.mp hxadd').2 hxremain.1
  simp only [changeRoot, size_castRoot]
  rw [introduceList_size, forgetList_size]
  simp

/-- Attach a path from `A` to an empty leaf. -/
noncomputable def closeToLeaf (A : Finset V) :
    InductiveNiceTree V (A : Set V) :=
  changeRoot A ∅ (castRoot (by simp) InductiveNiceTree.leaf)

theorem closeToLeaf_occPreconnected (A : Finset V) (v : V) :
    (closeToLeaf A).OccPreconnected v := by
  apply changeRoot_occPreconnected A ∅ _ v
  · exact (occPreconnected_castRoot_iff _ _ v).2
      (leaf_occPreconnected v)
  · intro x _hx hocc
    rcases (occurs_castRoot_iff _ _ x).1 hocc with ⟨n, hn⟩
    cases n
    simp [nodeBag] at hn

theorem closeToLeaf_size (A : Finset V) :
    (closeToLeaf A).size = A.card + 1 := by
  rw [closeToLeaf, changeRoot_size]
  simp [size]
  omega

/-- Map occurrence reachability from the left branch through a join. -/
theorem join_left_map_occReachable {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V)
    {x y : Node left} (hx : v ∈ nodeBag left x) (hy : v ∈ nodeBag left y)
    (hreach : (left.graph.induce {n : Node left | v ∈ nodeBag left n}).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩) :
    ((InductiveNiceTree.join left right).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Reachable
      ⟨some (Sum.inl x), by simpa [nodeBag] using hx⟩
      ⟨some (Sum.inl y), by simpa [nodeBag] using hy⟩ := by
  let hom :
      left.graph.induce {n : Node left | v ∈ nodeBag left n} →g
        (InductiveNiceTree.join left right).graph.induce
          {n | v ∈ nodeBag (InductiveNiceTree.join left right) n} := {
    toFun := fun n => ⟨some (Sum.inl n.1), by
      change v ∈ nodeBag left n.1
      exact n.2⟩
    map_rel' := by
      intro x y hxy
      change (InductiveNiceTree.join left right).graph.Adj
        (some (Sum.inl x.1)) (some (Sum.inl y.1))
      rcases (graph_adj left x.1 y.1).1 hxy with hxy | hyx
      · apply (graph_adj _ _ _).2 (Or.inl _)
        change some (Sum.inl y.1) ∈
          (left.children x.1).map (fun n => some (Sum.inl n))
        exact List.mem_map.mpr ⟨y.1, hxy, rfl⟩
      · apply (graph_adj _ _ _).2 (Or.inr _)
        change some (Sum.inl x.1) ∈
          (left.children y.1).map (fun n => some (Sum.inl n))
        exact List.mem_map.mpr ⟨x.1, hyx, rfl⟩ }
  exact hreach.map hom

/-- Map occurrence reachability from the right branch through a join. -/
theorem join_right_map_occReachable {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V)
    {x y : Node right} (hx : v ∈ nodeBag right x) (hy : v ∈ nodeBag right y)
    (hreach : (right.graph.induce {n : Node right | v ∈ nodeBag right n}).Reachable
      ⟨x, hx⟩ ⟨y, hy⟩) :
    ((InductiveNiceTree.join left right).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Reachable
      ⟨some (Sum.inr x), by simpa [nodeBag] using hx⟩
      ⟨some (Sum.inr y), by simpa [nodeBag] using hy⟩ := by
  let hom :
      right.graph.induce {n : Node right | v ∈ nodeBag right n} →g
        (InductiveNiceTree.join left right).graph.induce
          {n | v ∈ nodeBag (InductiveNiceTree.join left right) n} := {
    toFun := fun n => ⟨some (Sum.inr n.1), by
      change v ∈ nodeBag right n.1
      exact n.2⟩
    map_rel' := by
      intro x y hxy
      change (InductiveNiceTree.join left right).graph.Adj
        (some (Sum.inr x.1)) (some (Sum.inr y.1))
      rcases (graph_adj right x.1 y.1).1 hxy with hxy | hyx
      · apply (graph_adj _ _ _).2 (Or.inl _)
        change some (Sum.inr y.1) ∈
          (right.children x.1).map (fun n => some (Sum.inr n))
        exact List.mem_map.mpr ⟨y.1, hxy, rfl⟩
      · apply (graph_adj _ _ _).2 (Or.inr _)
        change some (Sum.inr x.1) ∈
          (right.children y.1).map (fun n => some (Sum.inr n))
        exact List.mem_map.mpr ⟨x.1, hyx, rfl⟩ }
  exact hreach.map hom

theorem join_root_reachable_left {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V) (hvbag : v ∈ bag)
    {x : Node left} (hx : v ∈ nodeBag left x)
    (hconn : left.OccPreconnected v) :
    ((InductiveNiceTree.join left right).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Reachable
      ⟨root (InductiveNiceTree.join left right), by
        change v ∈ nodeBag left (root left)
        simpa using hvbag⟩
      ⟨some (Sum.inl x), by simpa [nodeBag] using hx⟩ := by
  have hvleft : v ∈ nodeBag left (root left) := by
    rw [nodeBag_root]
    exact hvbag
  have hedge :
      ((InductiveNiceTree.join left right).graph.induce
        {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Adj
        ⟨none, by change v ∈ nodeBag left (root left); exact hvleft⟩
        ⟨some (Sum.inl (root left)), by simpa [nodeBag] using hvleft⟩ := by
    change (InductiveNiceTree.join left right).graph.Adj
      none (some (Sum.inl (root left)))
    apply (graph_adj _ _ _).2 (Or.inl _)
    change some (Sum.inl (root left)) ∈
      [some (Sum.inl (root left)), some (Sum.inr (root right))]
    simp
  exact SimpleGraph.Adj.reachable hedge |>.trans
    (join_left_map_occReachable left right v hvleft hx
      (hconn ⟨root left, hvleft⟩ ⟨x, hx⟩))

theorem join_root_reachable_right {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V) (hvbag : v ∈ bag)
    {x : Node right} (hx : v ∈ nodeBag right x)
    (hconn : right.OccPreconnected v) :
    ((InductiveNiceTree.join left right).graph.induce
      {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Reachable
      ⟨root (InductiveNiceTree.join left right), by
        change v ∈ nodeBag left (root left)
        simpa using hvbag⟩
      ⟨some (Sum.inr x), by simpa [nodeBag] using hx⟩ := by
  have hvright : v ∈ nodeBag right (root right) := by
    rw [nodeBag_root]
    exact hvbag
  have hvjoin : v ∈ nodeBag left (root left) := by
    rw [nodeBag_root]
    exact hvbag
  have hedge :
      ((InductiveNiceTree.join left right).graph.induce
        {n | v ∈ nodeBag (InductiveNiceTree.join left right) n}).Adj
        ⟨none, by change v ∈ nodeBag left (root left); exact hvjoin⟩
        ⟨some (Sum.inr (root right)), by simpa [nodeBag] using hvright⟩ := by
    change (InductiveNiceTree.join left right).graph.Adj
      none (some (Sum.inr (root right)))
    apply (graph_adj _ _ _).2 (Or.inl _)
    change some (Sum.inr (root right)) ∈
      [some (Sum.inl (root left)), some (Sum.inr (root right))]
    simp
  exact SimpleGraph.Adj.reachable hedge |>.trans
    (join_right_map_occReachable left right v hvright hx
      (hconn ⟨root right, hvright⟩ ⟨x, hx⟩))

/-- A binary join preserves occurrence connectedness provided a vertex that
occurs in both branches belongs to the common root bag. -/
theorem join_occPreconnected {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V)
    (hleft : left.OccPreconnected v) (hright : right.OccPreconnected v)
    (hcross : left.Occurs v → right.Occurs v → v ∈ bag) :
    (InductiveNiceTree.join left right).OccPreconnected v := by
  intro x y
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | none =>
      have hvbag : v ∈ bag := by
        change v ∈ nodeBag left (root left) at hx
        simpa using hx
      cases y with
      | none => exact SimpleGraph.Reachable.refl _
      | some y =>
          cases y with
          | inl y =>
              have hvy : v ∈ nodeBag left y := by simpa [nodeBag] using hy
              exact join_root_reachable_left left right v hvbag hvy hleft
          | inr y =>
              have hvy : v ∈ nodeBag right y := by simpa [nodeBag] using hy
              exact join_root_reachable_right left right v hvbag hvy hright
  | some x =>
      cases x with
      | inl x =>
          have hvx : v ∈ nodeBag left x := by simpa [nodeBag] using hx
          cases y with
          | none =>
              have hvbag : v ∈ bag := by
                change v ∈ nodeBag left (root left) at hy
                simpa using hy
              exact (join_root_reachable_left left right v hvbag hvx hleft).symm
          | some y =>
              cases y with
              | inl y =>
                  have hvy : v ∈ nodeBag left y := by simpa [nodeBag] using hy
                  exact join_left_map_occReachable left right v hvx hvy
                    (hleft ⟨x, hvx⟩ ⟨y, hvy⟩)
              | inr y =>
                  have hvy : v ∈ nodeBag right y := by simpa [nodeBag] using hy
                  have hvbag := hcross ⟨x, hvx⟩ ⟨y, hvy⟩
                  exact (join_root_reachable_left left right v hvbag hvx hleft).symm
                    |>.trans (join_root_reachable_right left right v hvbag hvy hright)
      | inr x =>
          have hvx : v ∈ nodeBag right x := by simpa [nodeBag] using hx
          cases y with
          | none =>
              have hvbag : v ∈ bag := by
                change v ∈ nodeBag left (root left) at hy
                simpa using hy
              exact (join_root_reachable_right left right v hvbag hvx hright).symm
          | some y =>
              cases y with
              | inr y =>
                  have hvy : v ∈ nodeBag right y := by simpa [nodeBag] using hy
                  exact join_right_map_occReachable left right v hvx hvy
                    (hright ⟨x, hvx⟩ ⟨y, hvy⟩)
              | inl y =>
                  have hvy : v ∈ nodeBag left y := by simpa [nodeBag] using hy
                  have hvbag := hcross ⟨y, hvy⟩ ⟨x, hvx⟩
                  exact (join_root_reachable_right left right v hvbag hvx hright).symm
                    |>.trans (join_root_reachable_left left right v hvbag hvy hleft)

theorem join_occurs_iff {bag : Set V}
    (left right : InductiveNiceTree V bag) (v : V) :
    (InductiveNiceTree.join left right).Occurs v ↔
      left.Occurs v ∨ right.Occurs v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | none =>
        exact Or.inl ⟨root left, by simpa [nodeBag] using hn⟩
    | some n =>
        cases n with
        | inl n => exact Or.inl ⟨n, by simpa [nodeBag] using hn⟩
        | inr n => exact Or.inr ⟨n, by simpa [nodeBag] using hn⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨some (Sum.inl n), by simpa [nodeBag] using hn⟩
    · exact ⟨some (Sum.inr n), by simpa [nodeBag] using hn⟩

/-- Right-associated binary joining of a nonempty list of equal-bag trees. -/
def joinNonempty {bag : Set V} :
    InductiveNiceTree V bag → List (InductiveNiceTree V bag) →
      InductiveNiceTree V bag
  | tree, [] => tree
  | tree, next :: rest => joinNonempty (.join tree next) rest

theorem joinNonempty_size {bag : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag)) :
    (joinNonempty tree rest).size =
      tree.size + (rest.map size).sum + rest.length := by
  induction rest generalizing tree with
  | nil => simp [joinNonempty]
  | cons next rest ih =>
      rw [joinNonempty, ih]
      simp [size]
      omega

/-- Repeated joins preserve occurrence connectedness when every pair of
distinct branch positions that contains the vertex meets in the common bag. -/
theorem joinNonempty_occPreconnected {bag : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag))
    (v : V) (htree : tree.OccPreconnected v)
    (hrest : ∀ next ∈ rest, next.OccPreconnected v)
    (hpair : (tree :: rest).Pairwise
      (fun left right => left.Occurs v → right.Occurs v → v ∈ bag)) :
    (joinNonempty tree rest).OccPreconnected v := by
  induction rest generalizing tree with
  | nil => exact htree
  | cons next rest ih =>
      rw [List.pairwise_cons] at hpair
      have hnext : next.OccPreconnected v := hrest next (by simp)
      have hcross : tree.Occurs v → next.Occurs v → v ∈ bag :=
        hpair.1 next (by simp)
      have hjoined : (InductiveNiceTree.join tree next).OccPreconnected v :=
        join_occPreconnected tree next v htree hnext hcross
      apply ih (InductiveNiceTree.join tree next) hjoined
      · intro other hother
        exact hrest other (by simp [hother])
      · rw [List.pairwise_cons]
        constructor
        · intro other hother hocc hotherOcc
          rcases (join_occurs_iff tree next v).1 hocc with htreeOcc | hnextOcc
          · exact hpair.1 other (by simp [hother]) htreeOcc hotherOcc
          · rw [List.pairwise_cons] at hpair
            exact hpair.2.1 other hother hnextOcc hotherOcc
        · rw [List.pairwise_cons] at hpair
          exact hpair.2.2

/-- Width bounds are preserved by repeated binary joins. -/
theorem joinNonempty_hasWidth [Finite V] {bag : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag))
    (omega : ℕ) (htree : tree.HasWidth omega)
    (hrest : ∀ next ∈ rest, next.HasWidth omega) :
    (joinNonempty tree rest).HasWidth omega := by
  induction rest generalizing tree with
  | nil => exact htree
  | cons next rest ih =>
      apply ih (.join tree next)
      · exact join_hasWidth tree next omega htree (hrest next (by simp))
      · intro other hother
        exact hrest other (by simp [hother])

/-- Repeated joins preserve every bag of the initial branch. -/
theorem joinNonempty_hasBag_head {bag target : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag))
    (hbag : tree.HasBag target) :
    (joinNonempty tree rest).HasBag target := by
  induction rest generalizing tree with
  | nil => exact hbag
  | cons next rest ih =>
      exact ih (.join tree next) hbag.join_left

/-- Repeated joins preserve every bag of every branch in the tail list. -/
theorem joinNonempty_hasBag_of_mem {bag target : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag))
    {branch : InductiveNiceTree V bag} (hmem : branch ∈ rest)
    (hbag : branch.HasBag target) :
    (joinNonempty tree rest).HasBag target := by
  induction rest generalizing tree with
  | nil => simp at hmem
  | cons next rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact joinNonempty_hasBag_head (.join tree branch) rest hbag.join_right
      · exact ih (.join tree next) hmem

theorem joinNonempty_verticesSubset {bag allowed : Set V}
    (tree : InductiveNiceTree V bag) (rest : List (InductiveNiceTree V bag))
    (htree : tree.VerticesSubset allowed)
    (hrest : ∀ next ∈ rest, next.VerticesSubset allowed) :
    (joinNonempty tree rest).VerticesSubset allowed := by
  induction rest generalizing tree with
  | nil => exact htree
  | cons next rest ih =>
      apply ih (.join tree next)
      · exact join_verticesSubset tree next htree (hrest next (by simp))
      · intro other hother
        exact hrest other (by simp [hother])

end InductiveNiceTree

namespace RootedTreeDecomposition

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- A graph vertex occurs somewhere in the original decomposition subtree
rooted at `t`. -/
def HasVertexBelow (T : RootedTreeDecomposition G) (t : T.Node) (v : V) : Prop :=
  ∃ s : T.Node, T.IsAncestor t s ∧ v ∈ T.bag s

/-- If a vertex occurs at a parent bag and somewhere below one of its
children, it occurs in the child bag.  This is the running-intersection axiom
in the exact local form used by normalization paths. -/
theorem mem_child_bag_of_mem_parent_of_hasVertexBelow
    (T : RootedTreeDecomposition G) {parent child : T.Node} {v : V}
    (hchild : T.IsChild parent child) (hparent : v ∈ T.bag parent)
    (hbelow : T.HasVertexBelow child v) :
    v ∈ T.bag child := by
  obtain ⟨s, hchild_s, hs⟩ := hbelow
  have htop_parent : T.IsAncestor (T.topBAGSNode v) parent :=
    T.topBAGSNode_isAncestor v hparent
  have htop_child : T.IsAncestor (T.topBAGSNode v) child :=
    htop_parent.trans (Relation.ReflTransGen.single hchild)
  exact T.mem_BAGS_of_isAncestor_of_isAncestor v htop_child hchild_s hs

/-- If a vertex occurs below two distinct children, it must occur in their
parent bag.  Otherwise the connected occurrence subtree would have to enter
two different child branches below its topmost node. -/
theorem mem_parent_bag_of_hasVertexBelow_two_children
    (T : RootedTreeDecomposition G) {parent left right : T.Node} {v : V}
    (hleft : T.IsChild parent left) (hright : T.IsChild parent right)
    (hne : left ≠ right)
    (hbelowLeft : T.HasVertexBelow left v)
    (hbelowRight : T.HasVertexBelow right v) :
    v ∈ T.bag parent := by
  by_contra hparent
  obtain ⟨sleft, hleft_s, hsleft⟩ := hbelowLeft
  obtain ⟨sright, hright_s, hsright⟩ := hbelowRight
  let top := T.topBAGSNode v
  have htop_leftS : T.IsAncestor top sleft :=
    T.topBAGSNode_isAncestor v hsleft
  have htop_rightS : T.IsAncestor top sright :=
    T.topBAGSNode_isAncestor v hsright
  have hparent_leftS : T.IsAncestor parent sleft :=
    (Relation.ReflTransGen.single hleft).trans hleft_s
  have hparent_rightS : T.IsAncestor parent sright :=
    (Relation.ReflTransGen.single hright).trans hright_s
  have hparent_top : T.IsAncestor parent top := by
    rcases htop_leftS.comparable_of_common_descendant hparent_leftS with
      htop_parent | hparent_top
    · have : v ∈ T.bag parent :=
        T.mem_BAGS_of_isAncestor_of_isAncestor v htop_parent
          hparent_leftS hsleft
      exact (hparent this).elim
    · exact hparent_top
  have htop_ne_parent : top ≠ parent := by
    intro heq
    have htopMem : v ∈ T.bag top := T.topBAGSNode_mem v
    rw [heq] at htopMem
    exact hparent htopMem
  have hparentDepth_lt_top : T.rootDepth parent < T.rootDepth top := by
    have hle := hparent_top.rootDepth_le
    have hneDepth : T.rootDepth parent ≠ T.rootDepth top := by
      intro heq
      exact htop_ne_parent
        (hparent_top.eq_of_rootDepth_le (by omega)).symm
    omega
  have hleft_top : T.IsAncestor left top := by
    rcases hleft_s.comparable_of_common_descendant htop_leftS with
      hleft_top | htop_left
    · exact hleft_top
    · have htopDepth_le_left := htop_left.rootDepth_le
      have hleftDepth := hleft.rootDepth_eq_add_one
      have heq : top = left :=
        htop_left.eq_of_rootDepth_le (by omega)
      rw [heq]
      exact Relation.ReflTransGen.refl
  have hright_top : T.IsAncestor right top := by
    rcases hright_s.comparable_of_common_descendant htop_rightS with
      hright_top | htop_right
    · exact hright_top
    · have htopDepth_le_right := htop_right.rootDepth_le
      have hrightDepth := hright.rootDepth_eq_add_one
      have heq : top = right :=
        htop_right.eq_of_rootDepth_le (by omega)
      rw [heq]
      exact Relation.ReflTransGen.refl
  rcases hleft_top.comparable_of_common_descendant hright_top with
    hleft_right | hright_left
  · have hdepthLeft := hleft.rootDepth_eq_add_one
    have hdepthRight := hright.rootDepth_eq_add_one
    exact hne (hleft_right.eq_of_rootDepth_le (by omega))
  · have hdepthLeft := hleft.rootDepth_eq_add_one
    have hdepthRight := hright.rootDepth_eq_add_one
    exact hne (hright_left.eq_of_rootDepth_le (by omega)).symm

/-- Every root path in a finite decomposition tree is shorter than its node
type. -/
theorem rootDepth_lt_card (T : RootedTreeDecomposition G) (t : T.Node) :
    T.rootDepth t < Fintype.card T.Node := by
  rw [← T.rootPath_length_eq_rootDepth t]
  exact (T.rootPath_isPath t).length_lt

/-- A child has strictly smaller reverse-depth measure than its parent. -/
theorem childMeasure_lt (T : RootedTreeDecomposition G)
    {parent child : T.Node} (hchild : T.IsChild parent child) :
    Fintype.card T.Node - T.rootDepth child <
      Fintype.card T.Node - T.rootDepth parent := by
  have hstep := hchild.rootDepth_eq_add_one
  have hbound := T.rootDepth_lt_card child
  omega

/-- The child relation, read from a parent to its recursive children, is
well-founded on a finite rooted tree. -/
theorem childWellFounded (T : RootedTreeDecomposition G) :
    WellFounded (fun child parent : T.Node => T.IsChild parent child) := by
  exact Subrelation.wf
    (fun {_child _parent} hchild => T.childMeasure_lt hchild)
    (measure (fun t : T.Node =>
      Fintype.card T.Node - T.rootDepth t)).wf

/-- The finite list of children of a rooted decomposition node. -/
noncomputable def childList (T : RootedTreeDecomposition G) (t : T.Node) :
    List {child : T.Node // T.IsChild t child} :=
  Finset.univ.toList

/-- Finite node set of the rooted subtree at `t`. -/
noncomputable def subtreeFinset (T : RootedTreeDecomposition G) (t : T.Node) :
    Finset T.Node :=
  Finset.univ.filter (T.IsAncestor t)

noncomputable def subtreeCard (T : RootedTreeDecomposition G) (t : T.Node) : ℕ :=
  (T.subtreeFinset t).card

@[simp] theorem mem_subtreeFinset (T : RootedTreeDecomposition G)
    (t x : T.Node) :
    x ∈ T.subtreeFinset t ↔ T.IsAncestor t x := by
  simp [subtreeFinset]

/-- The distinguished root is an ancestor of every decomposition node. -/
theorem root_isAncestor (T : RootedTreeDecomposition G) (s : T.Node) :
    T.IsAncestor T.root s := by
  by_cases hs : s = T.root
  · subst s
    exact Relation.ReflTransGen.refl
  · have hnn : ¬(T.rootPath s).Nil :=
      SimpleGraph.Walk.not_nil_of_ne (fun h => hs h.symm)
    obtain ⟨child, hrootChild, p, hpath⟩ :=
      SimpleGraph.Walk.not_nil_iff.mp hnn
    have hdepth : T.rootDepth child = T.rootDepth T.root + 1 := by
      rcases T.rootDepth_eq_add_one_or_eq_add_one hrootChild with hbad | hgood
      · simp at hbad
      · exact hgood
    have hp : (SimpleGraph.Walk.cons hrootChild p).IsPath := by
      rw [← hpath]
      exact T.rootPath_isPath s
    exact T.isAncestor_of_cons_isPath_of_rootDepth_eq_add_one
      hrootChild hdepth p hp

@[simp] theorem subtreeCard_root (T : RootedTreeDecomposition G) :
    T.subtreeCard T.root = Fintype.card T.Node := by
  classical
  have hall : T.subtreeFinset T.root = Finset.univ := by
    ext s
    simp [T.mem_subtreeFinset, T.root_isAncestor s]
  unfold subtreeCard
  rw [hall]
  simp

/-- The proper descendants of `t` are the disjoint union of its children's
rooted subtrees. -/
theorem subtreeFinset_erase_eq_biUnion_children
    (T : RootedTreeDecomposition G) (t : T.Node) :
    (T.subtreeFinset t).erase t =
      (Finset.univ : Finset {child : T.Node // T.IsChild t child}).biUnion
        (fun child => T.subtreeFinset child.1) := by
  classical
  ext x
  rw [Finset.mem_erase, Finset.mem_biUnion]
  simp only [mem_subtreeFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hancestor⟩
    rcases Relation.ReflTransGen.cases_head hancestor with heq |
      ⟨child, hchild, hchild_x⟩
    · exact (hne heq.symm).elim
    · exact ⟨⟨child, hchild⟩, hchild_x⟩
  · rintro ⟨child, hchild_x⟩
    refine ⟨?_, (Relation.ReflTransGen.single child.2).trans hchild_x⟩
    intro heq
    subst x
    have hdepth := child.2.rootDepth_eq_add_one
    have hle := hchild_x.rootDepth_le
    omega

theorem subtreeFinset_children_pairwiseDisjoint
    (T : RootedTreeDecomposition G) (t : T.Node) :
    ((Finset.univ : Finset {child : T.Node // T.IsChild t child}) :
      Set {child : T.Node // T.IsChild t child}).PairwiseDisjoint
        (fun child => T.subtreeFinset child.1) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro left _hleft right _hright hnonempty
  obtain ⟨x, hx⟩ := hnonempty
  have hx' := Finset.mem_inter.mp hx
  have hleft_x : T.IsAncestor left.1 x := by
    exact (T.mem_subtreeFinset left.1 x).1 hx'.1
  have hright_x : T.IsAncestor right.1 x := by
    exact (T.mem_subtreeFinset right.1 x).1 hx'.2
  rcases hleft_x.comparable_of_common_descendant hright_x with
    hleft_right | hright_left
  · apply Subtype.ext
    exact hleft_right.eq_of_rootDepth_le (by
      have hl := left.2.rootDepth_eq_add_one
      have hr := right.2.rootDepth_eq_add_one
      omega)
  · apply Subtype.ext
    exact (hright_left.eq_of_rootDepth_le (by
      have hl := left.2.rootDepth_eq_add_one
      have hr := right.2.rootDepth_eq_add_one
      omega)).symm

/-- Cardinal recurrence for a rooted subtree. -/
theorem subtreeCard_eq_one_add_sum_childList
    (T : RootedTreeDecomposition G) (t : T.Node) :
    T.subtreeCard t = 1 +
      ((T.childList t).map (fun child => T.subtreeCard child.1)).sum := by
  classical
  have ht : t ∈ T.subtreeFinset t :=
    (T.mem_subtreeFinset t t).2 Relation.ReflTransGen.refl
  have herase := T.subtreeFinset_erase_eq_biUnion_children t
  have hdisjoint := T.subtreeFinset_children_pairwiseDisjoint t
  have hcardUnion := Finset.card_biUnion hdisjoint
  have hsum :
      ((T.childList t).map (fun child => T.subtreeCard child.1)).sum =
        ∑ child : {child : T.Node // T.IsChild t child},
          T.subtreeCard child.1 := by
    let f : {child : T.Node // T.IsChild t child} → ℕ :=
      fun child => T.subtreeCard child.1
    have h := List.sum_toFinset f
      (Finset.nodup_toList (Finset.univ :
        Finset {child : T.Node // T.IsChild t child}))
    simpa [childList, f] using h.symm
  unfold subtreeCard
  unfold subtreeCard at hsum
  calc
    (T.subtreeFinset t).card = ((T.subtreeFinset t).erase t).card + 1 :=
      (Finset.card_erase_add_one ht).symm
    _ = ((Finset.univ :
          Finset {child : T.Node // T.IsChild t child}).biUnion
            (fun child => T.subtreeFinset child.1)).card + 1 := by rw [herase]
    _ = (∑ child : {child : T.Node // T.IsChild t child},
          (T.subtreeFinset child.1).card) + 1 := by
      rw [hcardUnion]
    _ = 1 + ((T.childList t).map
          (fun child => (T.subtreeFinset child.1).card)).sum := by
      rw [hsum]
      omega

/-- Normalize the subtree rooted at `t` into constructor-coded nice form.

Each recursive child code is first connected to `bag t` by a one-vertex path;
the resulting equal-bag branches are combined with binary joins.  An original
leaf is closed by a one-vertex path to an empty leaf.
-/
noncomputable def normalizeCodeAt (T : RootedTreeDecomposition G) (t : T.Node) :
    InductiveNiceTree V (T.bag t) :=
  T.childWellFounded.fix (C := fun t => InductiveNiceTree V (T.bag t))
    (fun t recurse =>
      let children := T.childList t
      match children with
      | [] =>
          InductiveNiceTree.castRoot
            (Set.coe_toFinset (T.bag t))
            (InductiveNiceTree.closeToLeaf (T.bag t).toFinset)
      | first :: rest =>
          let branch (child : {child : T.Node // T.IsChild t child}) :
              InductiveNiceTree V (T.bag t) :=
            InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag t))
              (InductiveNiceTree.changeRoot (T.bag t).toFinset
                (T.bag child.1).toFinset
                (InductiveNiceTree.castRoot
                  (Set.coe_toFinset (T.bag child.1)).symm
                  (recurse child.1 child.2)))
          InductiveNiceTree.joinNonempty (branch first) (rest.map branch)) t

/-- Subtree normalization preserves the width bound of the input
decomposition. -/
theorem normalizeCodeAt_hasWidth (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) (t : T.Node) :
    (T.normalizeCodeAt t).HasWidth omega := by
  apply T.childWellFounded.induction t
  intro t ih
  rw [normalizeCodeAt, WellFounded.fix_eq]
  let children := T.childList t
  cases hchildren : children with
  | nil =>
      have hclosed := InductiveNiceTree.changeRoot_hasWidth
        (T.bag t).toFinset ∅
        (InductiveNiceTree.castRoot (by simp)
          (InductiveNiceTree.leaf : InductiveNiceTree V ∅)) omega
        ((InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
          (InductiveNiceTree.leaf_hasWidth omega))
        (by simpa [Set.coe_toFinset] using hwidth t)
        (by simp)
      simpa [children, hchildren] using
        (InductiveNiceTree.hasWidth_castRoot_iff
          (Set.coe_toFinset (T.bag t))
          (InductiveNiceTree.closeToLeaf (T.bag t).toFinset) omega).2 hclosed
  | cons first rest =>
      let branch (child : {child : T.Node // T.IsChild t child}) :
          InductiveNiceTree V (T.bag t) :=
        InductiveNiceTree.castRoot
          (Set.coe_toFinset (T.bag t))
          (InductiveNiceTree.changeRoot (T.bag t).toFinset
            (T.bag child.1).toFinset
            (InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag child.1)).symm
              (T.normalizeCodeAt child.1)))
      have hbranch : ∀ child : {child : T.Node // T.IsChild t child},
          (branch child).HasWidth omega := by
        intro child
        apply (InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
        apply InductiveNiceTree.changeRoot_hasWidth
        · exact (InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
            (ih child.1 child.2)
        · simpa [Set.coe_toFinset] using hwidth t
        · simpa [Set.coe_toFinset] using hwidth child.1
      have hjoined := InductiveNiceTree.joinNonempty_hasWidth
        (branch first) (rest.map branch) omega (hbranch first) (by
          intro next hnext
          obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hnext
          exact hbranch child)
      simpa [children, hchildren, branch] using hjoined

/-- Amortized constructor-size bound for normalization of one rooted
subtree.  The additive term is precisely the budget used by the edge from
this subtree to its parent. -/
theorem normalizeCodeAt_size_add_le (T : RootedTreeDecomposition G)
    (omega : ℕ) (hwidth : T.toTreeDecomposition.HasWidth omega)
    (t : T.Node) :
    (T.normalizeCodeAt t).size + (2 * omega + 3) ≤
      (3 * omega + 5) * T.subtreeCard t := by
  induction t using T.childWellFounded.induction with
  | h t ih =>
      rw [normalizeCodeAt, WellFounded.fix_eq]
      let children := T.childList t
      cases hchildren : children with
      | nil =>
          have hchildList : T.childList t = [] := by
            simpa [children] using hchildren
          have hcard := T.subtreeCard_eq_one_add_sum_childList t
          rw [hchildList] at hcard
          simp at hcard
          have hbag : (T.bag t).toFinset.card ≤ omega + 1 := by
            rw [InductiveNiceTree.toFinset_card_eq_ncard]
            exact hwidth t
          have hresult :
              (InductiveNiceTree.castRoot
                (Set.coe_toFinset (T.bag t))
                (InductiveNiceTree.closeToLeaf
                  (T.bag t).toFinset)).size + (2 * omega + 3) ≤
                (3 * omega + 5) * T.subtreeCard t := by
            rw [InductiveNiceTree.size_castRoot,
              InductiveNiceTree.closeToLeaf_size, hcard]
            omega
          simpa [children, hchildren] using hresult
      | cons first rest =>
          let branch (child : {child : T.Node // T.IsChild t child}) :
              InductiveNiceTree V (T.bag t) :=
            InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag t))
              (InductiveNiceTree.changeRoot (T.bag t).toFinset
                (T.bag child.1).toFinset
                (InductiveNiceTree.castRoot
                  (Set.coe_toFinset (T.bag child.1)).symm
                  (T.normalizeCodeAt child.1)))
          let all := first :: rest
          have hparentCard : (T.bag t).toFinset.card ≤ omega + 1 := by
            rw [InductiveNiceTree.toFinset_card_eq_ncard]
            exact hwidth t
          have hbranchSize :
              ∀ child : {child : T.Node // T.IsChild t child},
                (branch child).size ≤
                  (T.normalizeCodeAt child.1).size + (2 * omega + 2) := by
            intro child
            have hchildCard : (T.bag child.1).toFinset.card ≤ omega + 1 := by
              rw [InductiveNiceTree.toFinset_card_eq_ncard]
              exact hwidth child.1
            have hremove :
                ((T.bag child.1).toFinset \ (T.bag t).toFinset).card ≤
                  (T.bag child.1).toFinset.card :=
              Finset.card_le_card Finset.sdiff_subset
            have hadd :
                ((T.bag t).toFinset \ (T.bag child.1).toFinset).card ≤
                  (T.bag t).toFinset.card :=
              Finset.card_le_card Finset.sdiff_subset
            simp only [branch, InductiveNiceTree.size_castRoot,
              InductiveNiceTree.changeRoot_size]
            omega
          have hjoinSize := InductiveNiceTree.joinNonempty_size
            (branch first) (rest.map branch)
          have hsize :
              (InductiveNiceTree.joinNonempty
                (branch first) (rest.map branch)).size =
                (all.map (fun child => (branch child).size)).sum + rest.length := by
            simpa [all, List.map_map, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hjoinSize
          have hbranchSum :
              (all.map (fun child => (branch child).size)).sum ≤
                (all.map (fun child =>
                  (T.normalizeCodeAt child.1).size)).sum +
                    (all.map (fun _ => 2 * omega + 2)).sum := by
            calc
              (all.map (fun child => (branch child).size)).sum ≤
                  (all.map (fun child =>
                    (T.normalizeCodeAt child.1).size +
                      (2 * omega + 2))).sum :=
                List.sum_le_sum (fun child _hchild => hbranchSize child)
              _ = (all.map (fun child =>
                    (T.normalizeCodeAt child.1).size)).sum +
                    (all.map (fun _ => 2 * omega + 2)).sum := by
                rw [List.sum_map_add]
          have hihSum :
              (all.map (fun child =>
                (T.normalizeCodeAt child.1).size)).sum +
                  (all.map (fun _ => 2 * omega + 3)).sum ≤
                (3 * omega + 5) *
                  (all.map (fun child => T.subtreeCard child.1)).sum := by
            calc
              (all.map (fun child =>
                  (T.normalizeCodeAt child.1).size)).sum +
                    (all.map (fun _ => 2 * omega + 3)).sum =
                  (all.map (fun child =>
                    (T.normalizeCodeAt child.1).size +
                      (2 * omega + 3))).sum := by
                exact (List.sum_map_add (l := all)
                  (f := fun child => (T.normalizeCodeAt child.1).size)
                  (g := fun _ => 2 * omega + 3)).symm
              _ ≤ (all.map (fun child =>
                    (3 * omega + 5) * T.subtreeCard child.1)).sum :=
                List.sum_le_sum (fun child _hchild => ih child.1 child.2)
              _ = (3 * omega + 5) *
                    (all.map (fun child => T.subtreeCard child.1)).sum := by
                exact List.sum_map_mul_left all
                  (fun child => T.subtreeCard child.1) (3 * omega + 5)
          have hpadding :
              (all.map (fun _ => 2 * omega + 2)).sum + rest.length +
                    (2 * omega + 3) ≤
                (all.map (fun _ => 2 * omega + 3)).sum +
                    (3 * omega + 5) := by
            have he : 2 * omega + 3 = (2 * omega + 2) + 1 := by omega
            rw [he]
            simp only [all, List.map_cons, List.sum_cons, List.sum_map_add]
            simp
            omega
          have hchildList : T.childList t = all := by
            simpa [children, all] using hchildren
          have hcard := T.subtreeCard_eq_one_add_sum_childList t
          rw [hchildList] at hcard
          have hresult :
              (InductiveNiceTree.joinNonempty
                  (branch first) (rest.map branch)).size + (2 * omega + 3) ≤
                (3 * omega + 5) * T.subtreeCard t := by
            rw [hsize, hcard, Nat.mul_add]
            simp only [Nat.mul_one]
            omega
          simpa [children, hchildren, branch] using hresult

/-- Normalization introduces no graph vertex outside the original
decomposition subtree being normalized. -/
theorem normalizeCodeAt_verticesSubset (T : RootedTreeDecomposition G)
    (t : T.Node) :
    (T.normalizeCodeAt t).VerticesSubset {v | T.HasVertexBelow t v} := by
  induction t using T.childWellFounded.induction with
  | h t ih =>
      rw [normalizeCodeAt, WellFounded.fix_eq]
      let children := T.childList t
      cases hchildren : children with
      | nil =>
          have hclosed :
              (InductiveNiceTree.castRoot
                (Set.coe_toFinset (T.bag t))
                (InductiveNiceTree.closeToLeaf
                  (T.bag t).toFinset)).VerticesSubset
                    {v | T.HasVertexBelow t v} := by
            apply (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
            apply InductiveNiceTree.changeRoot_verticesSubset
            · exact (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
                (InductiveNiceTree.leaf_verticesSubset _)
            · intro v hv
              exact ⟨t, Relation.ReflTransGen.refl, by
                simpa [Set.coe_toFinset] using hv⟩
            · simp
          simpa [children, hchildren] using hclosed
      | cons first rest =>
          let branch (child : {child : T.Node // T.IsChild t child}) :
              InductiveNiceTree V (T.bag t) :=
            InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag t))
              (InductiveNiceTree.changeRoot (T.bag t).toFinset
                (T.bag child.1).toFinset
                (InductiveNiceTree.castRoot
                  (Set.coe_toFinset (T.bag child.1)).symm
                  (T.normalizeCodeAt child.1)))
          have hbranch : ∀ child : {child : T.Node // T.IsChild t child},
              (branch child).VerticesSubset {v | T.HasVertexBelow t v} := by
            intro child
            apply (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
            apply InductiveNiceTree.changeRoot_verticesSubset
            · apply (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
              exact (ih child.1 child.2).mono (by
                intro v hbelow
                obtain ⟨s, hchild_s, hs⟩ := hbelow
                exact ⟨s,
                  (Relation.ReflTransGen.single child.2).trans hchild_s, hs⟩)
            · intro v hv
              exact ⟨t, Relation.ReflTransGen.refl, by
                simpa [Set.coe_toFinset] using hv⟩
            · intro v hv
              exact ⟨child.1, Relation.ReflTransGen.single child.2, by
                simpa [Set.coe_toFinset] using hv⟩
          have hjoined := InductiveNiceTree.joinNonempty_verticesSubset
            (branch first) (rest.map branch) (hbranch first) (by
              intro next hnext
              obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hnext
              exact hbranch child)
          simpa [children, hchildren, branch] using hjoined

/-- Every original bag in the subtree rooted at `t` survives in the normalized
constructor code for `t`. -/
theorem normalizeCodeAt_hasBag_of_isAncestor
    (T : RootedTreeDecomposition G) {t s : T.Node}
    (hts : T.IsAncestor t s) :
    (T.normalizeCodeAt t).HasBag (T.bag s) := by
  induction t using T.childWellFounded.induction generalizing s with
  | h t ih =>
      rw [normalizeCodeAt, WellFounded.fix_eq]
      let children := T.childList t
      cases hchildren : children with
      | nil =>
          have hst : s = t := by
            rcases Relation.ReflTransGen.cases_head hts with h | ⟨child, hchild, _⟩
            · exact h.symm
            · have hmem :
                  (⟨child, hchild⟩ : {child : T.Node // T.IsChild t child}) ∈
                    children := by
                  simp [children, childList]
              rw [hchildren] at hmem
              simp at hmem
          subst s
          simpa [children, hchildren] using
            (InductiveNiceTree.hasBag_root
              (InductiveNiceTree.castRoot
                (Set.coe_toFinset (T.bag t))
                (InductiveNiceTree.closeToLeaf (T.bag t).toFinset)))
      | cons first rest =>
          let branch (child : {child : T.Node // T.IsChild t child}) :
              InductiveNiceTree V (T.bag t) :=
            InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag t))
              (InductiveNiceTree.changeRoot (T.bag t).toFinset
                (T.bag child.1).toFinset
                (InductiveNiceTree.castRoot
                  (Set.coe_toFinset (T.bag child.1)).symm
                  (T.normalizeCodeAt child.1)))
          rcases Relation.ReflTransGen.cases_head hts with rfl | ⟨child, hchild, hchild_s⟩
          · simpa [children, hchildren, branch] using
              (InductiveNiceTree.hasBag_root
                (InductiveNiceTree.joinNonempty
                  (branch first) (rest.map branch)))
          · let child' : {child : T.Node // T.IsChild t child} := ⟨child, hchild⟩
            have hchildBag : (branch child').HasBag (T.bag s) := by
              apply (InductiveNiceTree.hasBag_castRoot_iff _ _).2
              apply InductiveNiceTree.changeRoot_hasBag
              apply (InductiveNiceTree.hasBag_castRoot_iff _ _).2
              exact ih child hchild hchild_s
            have hmem : child' ∈ children := by
              simp [children, childList, child']
            rw [hchildren] at hmem
            rcases List.mem_cons.mp hmem with hfirst | hrest
            · rw [hfirst] at hchildBag
              simpa [children, hchildren, branch] using
                (InductiveNiceTree.joinNonempty_hasBag_head
                  (branch first) (rest.map branch) hchildBag)
            · have hbranchMem : branch child' ∈ rest.map branch :=
                List.mem_map.mpr ⟨child', hrest, rfl⟩
              simpa [children, hchildren, branch] using
                (InductiveNiceTree.joinNonempty_hasBag_of_mem
                  (branch first) (rest.map branch) hbranchMem hchildBag)

/-- A vertex occurs in a normalized subtree code exactly when it occurs in an
original bag below that subtree root. -/
theorem normalizeCodeAt_occurs_iff (T : RootedTreeDecomposition G)
    (t : T.Node) (v : V) :
    (T.normalizeCodeAt t).Occurs v ↔ T.HasVertexBelow t v := by
  constructor
  · rintro ⟨n, hn⟩
    exact T.normalizeCodeAt_verticesSubset t n hn
  · rintro ⟨s, hts, hs⟩
    obtain ⟨n, hn⟩ := T.normalizeCodeAt_hasBag_of_isAncestor hts
    exact ⟨n, by rw [hn]; exact hs⟩

/-- Normalization preserves the running-intersection property: the code
positions containing a fixed graph vertex form a connected subtree. -/
theorem normalizeCodeAt_occPreconnected (T : RootedTreeDecomposition G)
    (t : T.Node) (v : V) :
    (T.normalizeCodeAt t).OccPreconnected v := by
  induction t using T.childWellFounded.induction with
  | h t ih =>
      rw [normalizeCodeAt, WellFounded.fix_eq]
      let children := T.childList t
      cases hchildren : children with
      | nil =>
          have hclosed :
              (InductiveNiceTree.castRoot
                (Set.coe_toFinset (T.bag t))
                (InductiveNiceTree.closeToLeaf
                  (T.bag t).toFinset)).OccPreconnected v :=
            (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
              (InductiveNiceTree.closeToLeaf_occPreconnected _ v)
          simpa [children, hchildren] using hclosed
      | cons first rest =>
          let branch (child : {child : T.Node // T.IsChild t child}) :
              InductiveNiceTree V (T.bag t) :=
            InductiveNiceTree.castRoot
              (Set.coe_toFinset (T.bag t))
              (InductiveNiceTree.changeRoot (T.bag t).toFinset
                (T.bag child.1).toFinset
                (InductiveNiceTree.castRoot
                  (Set.coe_toFinset (T.bag child.1)).symm
                  (T.normalizeCodeAt child.1)))
          have hbranchConn : ∀ child : {child : T.Node // T.IsChild t child},
              (branch child).OccPreconnected v := by
            intro child
            apply (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
            apply InductiveNiceTree.changeRoot_occPreconnected
            · exact (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
                (ih child.1 child.2)
            · intro x hx hocc
              have hbelow : T.HasVertexBelow child.1 x :=
                (T.normalizeCodeAt_occurs_iff child.1 x).1
                  ((InductiveNiceTree.occurs_castRoot_iff _ _ x).1 hocc)
              have hxparent : x ∈ T.bag t := by
                simpa using (Finset.mem_sdiff.mp hx).1
              have hxchild := T.mem_child_bag_of_mem_parent_of_hasVertexBelow
                child.2 hxparent hbelow
              exact (Finset.mem_sdiff.mp hx).2 (by simpa using hxchild)
          have hbranchSubset :
              ∀ child : {child : T.Node // T.IsChild t child},
                (branch child).VerticesSubset
                  {x | T.HasVertexBelow child.1 x ∨ x ∈ T.bag t} := by
            intro child
            apply (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
            apply InductiveNiceTree.changeRoot_verticesSubset
            · apply (InductiveNiceTree.verticesSubset_castRoot_iff _ _).2
              exact (T.normalizeCodeAt_verticesSubset child.1).mono
                (fun _ hx => Or.inl hx)
            · intro x hx
              exact Or.inr (by simpa using hx)
            · intro x hx
              exact Or.inl ⟨child.1, Relation.ReflTransGen.refl,
                by simpa using hx⟩
          have hchildrenNodup : (first :: rest).Nodup := by
            have h := Finset.nodup_toList (Finset.univ :
              Finset {child : T.Node // T.IsChild t child})
            change children.Nodup at h
            simpa [hchildren] using h
          have hnePair : (first :: rest).Pairwise (fun left right => left ≠ right) :=
            List.nodup_iff_pairwise_ne.mp hchildrenNodup
          have hbranchPair :
              (branch first :: rest.map branch).Pairwise
                (fun left right =>
                  left.Occurs v → right.Occurs v → v ∈ T.bag t) := by
            have hmapped : ((first :: rest).map branch).Pairwise
                (fun left right =>
                  left.Occurs v → right.Occurs v → v ∈ T.bag t) :=
              hnePair.map branch (by
              intro left right hne hleftOcc hrightOcc
              by_cases hparent : v ∈ T.bag t
              · exact hparent
              · have hleftBelow : T.HasVertexBelow left.1 v := by
                  rcases hleftOcc with ⟨n, hn⟩
                  exact (hbranchSubset left n hn).resolve_right hparent
                have hrightBelow : T.HasVertexBelow right.1 v := by
                  rcases hrightOcc with ⟨n, hn⟩
                  exact (hbranchSubset right n hn).resolve_right hparent
                apply T.mem_parent_bag_of_hasVertexBelow_two_children
                  left.2 right.2
                · intro heq
                  apply hne
                  exact Subtype.ext heq
                · exact hleftBelow
                · exact hrightBelow)
            simpa using hmapped
          have hjoined := InductiveNiceTree.joinNonempty_occPreconnected
            (branch first) (rest.map branch) v (hbranchConn first) (by
              intro next hnext
              obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hnext
              exact hbranchConn child) hbranchPair
          simpa [children, hchildren, branch] using hjoined

/-- The complete normalized code, with an empty path attached above the
chosen root. -/
noncomputable def normalizeCode (T : RootedTreeDecomposition G) :
    InductiveNiceTree V ∅ :=
  InductiveNiceTree.castRoot (by simp)
    (InductiveNiceTree.changeRoot ∅ (T.bag T.root).toFinset
      (InductiveNiceTree.castRoot (Set.coe_toFinset (T.bag T.root)).symm
        (T.normalizeCodeAt T.root)))

/-- Complete normalization, including the empty-root path, preserves width. -/
theorem normalizeCode_hasWidth (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    T.normalizeCode.HasWidth omega := by
  unfold normalizeCode
  apply (InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
  apply InductiveNiceTree.changeRoot_hasWidth
  · exact (InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
      (T.normalizeCodeAt_hasWidth omega hwidth T.root)
  · simp
  · simpa [Set.coe_toFinset] using hwidth T.root

/-- Every bag of the original decomposition occurs in the complete normalized
code. -/
theorem normalizeCode_hasBag (T : RootedTreeDecomposition G) (s : T.Node) :
    T.normalizeCode.HasBag (T.bag s) := by
  unfold normalizeCode
  apply (InductiveNiceTree.hasBag_castRoot_iff _ _).2
  apply InductiveNiceTree.changeRoot_hasBag
  apply (InductiveNiceTree.hasBag_castRoot_iff _ _).2
  exact T.normalizeCodeAt_hasBag_of_isAncestor (T.root_isAncestor s)

theorem normalizeCode_occPreconnected (T : RootedTreeDecomposition G) (v : V) :
    T.normalizeCode.OccPreconnected v := by
  unfold normalizeCode
  apply (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
  apply InductiveNiceTree.changeRoot_occPreconnected
  · exact (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
      (T.normalizeCodeAt_occPreconnected T.root v)
  · simp

/-- Construct the certified inductive nice decomposition obtained by
normalizing a rooted tree-decomposition. -/
noncomputable def normalize (T : RootedTreeDecomposition G) :
    InductiveNiceTreeDecomposition (G := G) := by
  apply T.normalizeCode.toInductiveNiceTreeDecomposition
  · intro v
    obtain ⟨s, hs⟩ := T.VertexCoverage v
    obtain ⟨n, hn⟩ := T.normalizeCode_hasBag s
    refine ⟨n, ?_⟩
    rw [hn]
    simpa [RootedTreeDecomposition.bag, TreeDecomposition.bag] using hs
  · intro u v huv
    obtain ⟨s, hus, hvs⟩ := T.EdgeCoverage huv
    obtain ⟨n, hn⟩ := T.normalizeCode_hasBag s
    refine ⟨n, ?_, ?_⟩
    · rw [hn]
      simpa [RootedTreeDecomposition.bag, TreeDecomposition.bag] using hus
    · rw [hn]
      simpa [RootedTreeDecomposition.bag, TreeDecomposition.bag] using hvs
  · exact T.normalizeCode_occPreconnected

@[simp] theorem normalize_tree (T : RootedTreeDecomposition G) :
    T.normalize.tree = T.normalizeCode :=
  rfl

/-- The normalization preserves any width bound of the input decomposition. -/
theorem normalize_hasWidth (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    T.normalize.toTreeDecomposition.HasWidth omega := by
  rw [T.normalize.hasWidth_iff]
  simpa using T.normalizeCode_hasWidth omega hwidth

/-- Complete normalization satisfies the TeX node bound. -/
theorem normalizeCode_size_le (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    T.normalizeCode.size ≤
      (3 * omega + 5) * Fintype.card T.Node := by
  have hrootBag : (T.bag T.root).toFinset.card ≤ omega + 1 := by
    rw [InductiveNiceTree.toFinset_card_eq_ncard]
    exact hwidth T.root
  have hsubtree := T.normalizeCodeAt_size_add_le omega hwidth T.root
  rw [T.subtreeCard_root] at hsubtree
  have hsize : T.normalizeCode.size =
      (T.normalizeCodeAt T.root).size + (T.bag T.root).toFinset.card := by
    unfold normalizeCode
    simp only [InductiveNiceTree.size_castRoot,
      InductiveNiceTree.changeRoot_size]
    simp
  rw [hsize]
  omega

theorem normalize_node_bound (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    Fintype.card T.normalize.Node ≤
      (3 * omega + 5) * Fintype.card T.Node := by
  change Fintype.card (InductiveNiceTree.Node T.normalizeCode) ≤ _
  rw [InductiveNiceTree.card_node_eq_size]
  exact T.normalizeCode_size_le omega hwidth

end RootedTreeDecomposition

namespace TreeDecomposition

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Choose an arbitrary root of a finite tree-decomposition. -/
noncomputable def rooted (D : TreeDecomposition G) : RootedTreeDecomposition G where
  toTreeDecomposition := D
  root := Classical.choice D.T_istree.isConnected.nonempty

@[simp] theorem rooted_toTreeDecomposition (D : TreeDecomposition G) :
    D.rooted.toTreeDecomposition = D :=
  rfl

/-- Nice-normalize an ordinary tree-decomposition after choosing a root. -/
noncomputable def normalize (D : TreeDecomposition G) :
    InductiveNiceTreeDecomposition (G := G) :=
  D.rooted.normalize

theorem normalize_hasWidth (D : TreeDecomposition G) (omega : ℕ)
    (hwidth : D.HasWidth omega) :
    D.normalize.toTreeDecomposition.HasWidth omega :=
  D.rooted.normalize_hasWidth omega hwidth

theorem normalize_node_bound (D : TreeDecomposition G) (omega : ℕ)
    (hwidth : D.HasWidth omega) :
    Fintype.card D.normalize.Node ≤
      (3 * omega + 5) * Fintype.card D.Node :=
  D.rooted.normalize_node_bound omega hwidth

end TreeDecomposition

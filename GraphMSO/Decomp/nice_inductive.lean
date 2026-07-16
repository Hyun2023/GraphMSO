import GraphMSO.Decomp.nice

/-!
# Inductive nice tree-decompositions

`GraphMSO.Decomp.nice` defines a nice tree-decomposition as a rooted
tree-decomposition plus a global predicate `IsNice`.

This file is deliberately different: it introduces a programming-facing tree
code, defined by ordinary inductive constructors, and then relates that code to
a mathematical `NiceTreeDecomposition` by a separate realization proof.

The intended use is that algorithms recurse over `InductiveNiceTree`; the
realization fields say that this recursive tree is exactly the nice
tree-decomposition already present in the mathematical development.
-/

open scoped Classical

universe u

/--
A constructor-coded nice tree whose type is indexed by its root bag.

The local bag discipline is carried by the constructors themselves:

* a leaf has empty bag,
* an introduce node adds one fresh vertex to its child bag,
* a forget node removes one present vertex from its child bag,
* a join node has two children with the same root bag.

This is the algorithm-facing object: definitions can recurse directly over
`leaf`, `introduce`, `forget`, and `join`.
-/
inductive InductiveNiceTree (V : Type u) : Set V -> Type (u + 1) where
  | leaf : InductiveNiceTree V ∅
  | introduce {bag : Set V} (v : V) (child : InductiveNiceTree V bag)
      (fresh : v ∉ bag) : InductiveNiceTree V (bag ∪ {v})
  | forget {bag : Set V} (v : V) (child : InductiveNiceTree V bag)
      (present : v ∈ bag) : InductiveNiceTree V (bag \ {v})
  | join {bag : Set V} (left right : InductiveNiceTree V bag) :
      InductiveNiceTree V bag


-- 계산구조 <-> 진짜수학구조
--   체킹  <->   성질만족

namespace InductiveNiceTree

variable {V : Type u}

/--
The finite type of positions/nodes inside a coded nice tree.

The root is represented by `PUnit.unit` for a leaf and by `none` for every
non-leaf constructor.  Child positions are embedded recursively.
-/
def Node {bag : Set V} (tree : InductiveNiceTree V bag) : Type (u + 1) :=
  match tree with
  | leaf => PUnit
  | introduce _ child _ => Option (Node child)
  | forget _ child _ => Option (Node child)
  | join left right => Option (Sum (Node left) (Node right))

/-- The root position of a coded nice tree. -/
def root {bag : Set V} (tree : InductiveNiceTree V bag) : Node tree :=
  match tree with
  | leaf => PUnit.unit
  | introduce _ _ _ => none
  | forget _ _ _ => none
  | join _ _ => none

/-- The bag at a coded tree position. -/
def nodeBag {bag : Set V} (tree : InductiveNiceTree V bag) :
    Node tree -> Set V :=
  match tree with
  | leaf => fun _ => ∅
  | introduce v child _ => fun
      | none => nodeBag child (root child) ∪ {v}
      | some n => nodeBag child n
  | forget v child _ => fun
      | none => nodeBag child (root child) \ {v}
      | some n => nodeBag child n
  | join left _right => fun
      | none => nodeBag left (root left)
      | some (Sum.inl n) => nodeBag left n
      | some (Sum.inr n) => nodeBag _right n

/-- The immediate children of a coded tree position, as explicit data. -/
def children {bag : Set V} (tree : InductiveNiceTree V bag) :
    Node tree -> List (Node tree) :=
  match tree with
  | leaf => fun _ => []
  | introduce _ child _ => fun
      | none => [some (root child)]
      | some n => (children child n).map some
  | forget _ child _ => fun
      | none => [some (root child)]
      | some n => (children child n).map some
  | join left right => fun
      | none => [some (Sum.inl (root left)), some (Sum.inr (root right))]
      | some (Sum.inl n) => (children left n).map (fun child => some (Sum.inl child))
      | some (Sum.inr n) => (children right n).map (fun child => some (Sum.inr child))

/-- The parent/child relation induced by the explicit `children` list. -/
def IsChild {bag : Set V} (tree : InductiveNiceTree V bag)
    (parent child : Node tree) : Prop :=
  child ∈ children tree parent

/-- Depth of a constructor-code position from the root. -/
def depth {bag : Set V} (tree : InductiveNiceTree V bag) : Node tree → ℕ :=
  match tree with
  | leaf => fun _ => 0
  | introduce _ child _ => fun
      | none => 0
      | some n => depth child n + 1
  | forget _ child _ => fun
      | none => 0
      | some n => depth child n + 1
  | join left right => fun
      | none => 0
      | some (.inl n) => depth left n + 1
      | some (.inr n) => depth right n + 1

@[simp] theorem depth_root {bag : Set V} (tree : InductiveNiceTree V bag) :
    depth tree (root tree) = 0 := by
  cases tree <;> rfl

/-- Every constructor-code child edge increases depth by exactly one. -/
theorem depth_eq_add_one_of_isChild {bag : Set V}
    (tree : InductiveNiceTree V bag) {parent child : Node tree}
    (h : tree.IsChild parent child) :
    depth tree child = depth tree parent + 1 := by
  induction tree with
  | leaf =>
      cases parent
      cases child
      simp [IsChild, children] at h
  | introduce v childTree fresh ih =>
      cases parent with
      | none =>
          cases child with
          | none => simp [IsChild, children] at h
          | some child =>
              have hroot : child = root childTree := by
                change some child ∈ [some (root childTree)] at h
                exact Option.some.inj (List.mem_singleton.mp h)
              change depth childTree child + 1 = 0 + 1
              rw [hroot, depth_root]
      | some parent =>
          cases child with
          | none => simp [IsChild, children] at h
          | some child =>
              have hchild : childTree.IsChild parent child := by
                change some child ∈ (childTree.children parent).map some at h
                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
                have hxc : x = child := Option.some.inj heq
                simpa [hxc] using hx
              simpa [depth] using ih hchild
  | forget v childTree present ih =>
      cases parent with
      | none =>
          cases child with
          | none => simp [IsChild, children] at h
          | some child =>
              have hroot : child = root childTree := by
                change some child ∈ [some (root childTree)] at h
                exact Option.some.inj (List.mem_singleton.mp h)
              change depth childTree child + 1 = 0 + 1
              rw [hroot, depth_root]
      | some parent =>
          cases child with
          | none => simp [IsChild, children] at h
          | some child =>
              have hchild : childTree.IsChild parent child := by
                change some child ∈ (childTree.children parent).map some at h
                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
                have hxc : x = child := Option.some.inj heq
                simpa [hxc] using hx
              simpa [depth] using ih hchild
  | join left right ihleft ihrigh =>
      cases parent with
      | none =>
          cases child with
          | none => simp [IsChild, children] at h
          | some child =>
              cases child with
              | inl child =>
                  have hroot : child = root left := by
                    change some (Sum.inl child : Node left ⊕ Node right) ∈
                      [some (Sum.inl (root left)), some (Sum.inr (root right))] at h
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                    rcases h with h | h
                    · exact Sum.inl.inj (Option.some.inj h)
                    · have hfalse : False := by
                        simpa using Option.some.inj h
                      exact hfalse.elim
                  change depth left child + 1 = 0 + 1
                  rw [hroot, depth_root]
              | inr child =>
                  have hroot : child = root right := by
                    change some (Sum.inr child : Node left ⊕ Node right) ∈
                      [some (Sum.inl (root left)), some (Sum.inr (root right))] at h
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                    rcases h with h | h
                    · have hfalse : False := by
                        simpa using Option.some.inj h
                      exact hfalse.elim
                    · exact Sum.inr.inj (Option.some.inj h)
                  change depth right child + 1 = 0 + 1
                  rw [hroot, depth_root]
      | some parent =>
          cases parent with
          | inl parent =>
              cases child with
              | none => simp [IsChild, children] at h
              | some child =>
                  cases child with
                  | inl child =>
                      have hchild : left.IsChild parent child := by
                        change some (Sum.inl child : Node left ⊕ Node right) ∈
                          (left.children parent).map
                            (fun n => some (Sum.inl n)) at h
                        obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
                        have : x = child := Sum.inl.inj (Option.some.inj heq)
                        simpa [this] using hx
                      simpa [depth] using ihleft hchild
                  | inr child =>
                      change some (Sum.inr child : Node left ⊕ Node right) ∈
                        (left.children parent).map
                          (fun n => some (Sum.inl n)) at h
                      obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h
                      have hfalse : False := by
                        simpa using Option.some.inj heq
                      exact hfalse.elim
          | inr parent =>
              cases child with
              | none => simp [IsChild, children] at h
              | some child =>
                  cases child with
                  | inl child =>
                      change some (Sum.inl child : Node left ⊕ Node right) ∈
                        (right.children parent).map
                          (fun n => some (Sum.inr n)) at h
                      obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h
                      have hfalse : False := by
                        simpa using Option.some.inj heq
                      exact hfalse.elim
                  | inr child =>
                      have hchild : right.IsChild parent child := by
                        change some (Sum.inr child : Node left ⊕ Node right) ∈
                          (right.children parent).map
                            (fun n => some (Sum.inr n)) at h
                        obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
                        have : x = child := Sum.inr.inj (Option.some.inj heq)
                        simpa [this] using hx
                      simpa [depth] using ihrigh hchild

/-- A constructor-code node has at most one parent. -/
theorem parent_unique {bag : Set V} (tree : InductiveNiceTree V bag)
    {parent₁ parent₂ child : Node tree}
    (h₁ : tree.IsChild parent₁ child) (h₂ : tree.IsChild parent₂ child) :
    parent₁ = parent₂ := by
  induction tree with
  | leaf =>
      cases parent₁
      cases parent₂
      cases child
      simp [IsChild, children] at h₁
  | introduce v childTree fresh ih =>
      cases child with
      | none =>
          cases parent₁ <;> simp [IsChild, children] at h₁
      | some child =>
          cases parent₁ with
          | none =>
              cases parent₂ with
              | none => rfl
              | some parent₂ =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  simp [depth] at hd₁ hd₂
                  omega
          | some parent₁ =>
              cases parent₂ with
              | none =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  simp [depth] at hd₁ hd₂
                  omega
              | some parent₂ =>
                  have hc₁ : childTree.IsChild parent₁ child := by
                    change some child ∈ (childTree.children parent₁).map some at h₁
                    obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₁
                    have : x = child := Option.some.inj heq
                    simpa [this] using hx
                  have hc₂ : childTree.IsChild parent₂ child := by
                    change some child ∈ (childTree.children parent₂).map some at h₂
                    obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₂
                    have : x = child := Option.some.inj heq
                    simpa [this] using hx
                  exact congrArg some (ih hc₁ hc₂)
  | forget v childTree present ih =>
      cases child with
      | none =>
          cases parent₁ <;> simp [IsChild, children] at h₁
      | some child =>
          cases parent₁ with
          | none =>
              cases parent₂ with
              | none => rfl
              | some parent₂ =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  simp [depth] at hd₁ hd₂
                  omega
          | some parent₁ =>
              cases parent₂ with
              | none =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  simp [depth] at hd₁ hd₂
                  omega
              | some parent₂ =>
                  have hc₁ : childTree.IsChild parent₁ child := by
                    change some child ∈ (childTree.children parent₁).map some at h₁
                    obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₁
                    have : x = child := Option.some.inj heq
                    simpa [this] using hx
                  have hc₂ : childTree.IsChild parent₂ child := by
                    change some child ∈ (childTree.children parent₂).map some at h₂
                    obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₂
                    have : x = child := Option.some.inj heq
                    simpa [this] using hx
                  exact congrArg some (ih hc₁ hc₂)
  | join left right ihleft ihrigh =>
      cases child with
      | none =>
          cases parent₁ with
          | none => simp [IsChild, children] at h₁
          | some parent₁ =>
              cases parent₁ <;> simp [IsChild, children] at h₁
      | some child =>
          cases parent₁ with
          | none =>
              cases parent₂ with
              | none => rfl
              | some parent₂ =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  cases child <;> cases parent₂ <;>
                    simp [depth] at hd₁ hd₂ <;> omega
          | some parent₁ =>
              cases parent₂ with
              | none =>
                  have hd₁ := depth_eq_add_one_of_isChild _ h₁
                  have hd₂ := depth_eq_add_one_of_isChild _ h₂
                  cases child <;> cases parent₁ <;>
                    simp [depth] at hd₁ hd₂ <;> omega
              | some parent₂ =>
                  cases child with
                  | inl child =>
                      cases parent₁ with
                      | inl parent₁ =>
                          cases parent₂ with
                          | inl parent₂ =>
                              have hc₁ : left.IsChild parent₁ child := by
                                change some (Sum.inl child : Node left ⊕ Node right) ∈
                                  (left.children parent₁).map
                                    (fun n => some (Sum.inl n)) at h₁
                                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₁
                                have : x = child := Sum.inl.inj (Option.some.inj heq)
                                simpa [this] using hx
                              have hc₂ : left.IsChild parent₂ child := by
                                change some (Sum.inl child : Node left ⊕ Node right) ∈
                                  (left.children parent₂).map
                                    (fun n => some (Sum.inl n)) at h₂
                                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₂
                                have : x = child := Sum.inl.inj (Option.some.inj heq)
                                simpa [this] using hx
                              exact congrArg (fun n => some (Sum.inl n))
                                (ihleft hc₁ hc₂)
                          | inr parent₂ =>
                              change some (Sum.inl child : Node left ⊕ Node right) ∈
                                (right.children parent₂).map
                                  (fun n => some (Sum.inr n)) at h₂
                              obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h₂
                              have hfalse : False := by
                                simpa using Option.some.inj heq
                              exact hfalse.elim
                      | inr parent₁ =>
                          change some (Sum.inl child : Node left ⊕ Node right) ∈
                            (right.children parent₁).map
                              (fun n => some (Sum.inr n)) at h₁
                          obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h₁
                          have hfalse : False := by
                            simpa using Option.some.inj heq
                          exact hfalse.elim
                  | inr child =>
                      cases parent₁ with
                      | inl parent₁ =>
                          change some (Sum.inr child : Node left ⊕ Node right) ∈
                            (left.children parent₁).map
                              (fun n => some (Sum.inl n)) at h₁
                          obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h₁
                          have hfalse : False := by
                            simpa using Option.some.inj heq
                          exact hfalse.elim
                      | inr parent₁ =>
                          cases parent₂ with
                          | inl parent₂ =>
                              change some (Sum.inr child : Node left ⊕ Node right) ∈
                                (left.children parent₂).map
                                  (fun n => some (Sum.inl n)) at h₂
                              obtain ⟨x, _hx, heq⟩ := List.mem_map.mp h₂
                              have hfalse : False := by
                                simpa using Option.some.inj heq
                              exact hfalse.elim
                          | inr parent₂ =>
                              have hc₁ : right.IsChild parent₁ child := by
                                change some (Sum.inr child : Node left ⊕ Node right) ∈
                                  (right.children parent₁).map
                                    (fun n => some (Sum.inr n)) at h₁
                                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₁
                                have : x = child := Sum.inr.inj (Option.some.inj heq)
                                simpa [this] using hx
                              have hc₂ : right.IsChild parent₂ child := by
                                change some (Sum.inr child : Node left ⊕ Node right) ∈
                                  (right.children parent₂).map
                                    (fun n => some (Sum.inr n)) at h₂
                                obtain ⟨x, hx, heq⟩ := List.mem_map.mp h₂
                                have : x = child := Sum.inr.inj (Option.some.inj heq)
                                simpa [this] using hx
                              exact congrArg (fun n => some (Sum.inr n))
                                (ihrigh hc₁ hc₂)

/-- No constructor-code edge enters the root. -/
theorem not_isChild_root {bag : Set V} (tree : InductiveNiceTree V bag)
    (parent : Node tree) : ¬ tree.IsChild parent (root tree) := by
  intro h
  have hdepth := depth_eq_add_one_of_isChild tree h
  simp at hdepth

/-- Every constructor-code position is a descendant of the root. -/
theorem root_reflTransGen_isChild {bag : Set V}
    (tree : InductiveNiceTree V bag) (n : Node tree) :
    Relation.ReflTransGen tree.IsChild (root tree) n := by
  induction tree with
  | leaf =>
      cases n
      exact Relation.ReflTransGen.refl
  | introduce v child fresh ih =>
      cases n with
      | none => exact Relation.ReflTransGen.refl
      | some n =>
          have hlift : Relation.ReflTransGen
              (introduce v child fresh).IsChild
              (some (root child)) (some n) :=
            (ih n).lift some (by
              intro parent childNode hchild
              change some childNode ∈ (child.children parent).map some
              exact List.mem_map.mpr ⟨childNode, hchild, rfl⟩)
          exact (Relation.ReflTransGen.single (by
            change some (root child) ∈ [some (root child)]
            simp)).trans hlift
  | forget v child present ih =>
      cases n with
      | none => exact Relation.ReflTransGen.refl
      | some n =>
          have hlift : Relation.ReflTransGen
              (forget v child present).IsChild
              (some (root child)) (some n) :=
            (ih n).lift some (by
              intro parent childNode hchild
              change some childNode ∈ (child.children parent).map some
              exact List.mem_map.mpr ⟨childNode, hchild, rfl⟩)
          exact (Relation.ReflTransGen.single (by
            change some (root child) ∈ [some (root child)]
            simp)).trans hlift
  | join left right ihleft ihrigh =>
      cases n with
      | none => exact Relation.ReflTransGen.refl
      | some n =>
          cases n with
          | inl n =>
              have hlift : Relation.ReflTransGen (left.join right).IsChild
                  (some (Sum.inl (root left))) (some (Sum.inl n)) :=
                (ihleft n).lift (fun x => some (Sum.inl x)) (by
                  intro parent childNode hchild
                  change some (Sum.inl childNode : Node left ⊕ Node right) ∈
                    (left.children parent).map (fun x => some (Sum.inl x))
                  exact List.mem_map.mpr ⟨childNode, hchild, rfl⟩)
              exact (Relation.ReflTransGen.single (by
                change some (Sum.inl (root left) : Node left ⊕ Node right) ∈
                  [some (Sum.inl (root left)), some (Sum.inr (root right))]
                simp)).trans hlift
          | inr n =>
              have hlift : Relation.ReflTransGen (left.join right).IsChild
                  (some (Sum.inr (root right))) (some (Sum.inr n)) :=
                (ihrigh n).lift (fun x => some (Sum.inr x)) (by
                  intro parent childNode hchild
                  change some (Sum.inr childNode : Node left ⊕ Node right) ∈
                    (right.children parent).map (fun x => some (Sum.inr x))
                  exact List.mem_map.mpr ⟨childNode, hchild, rfl⟩)
              exact (Relation.ReflTransGen.single (by
                change some (Sum.inr (root right) : Node left ⊕ Node right) ∈
                  [some (Sum.inl (root left)), some (Sum.inr (root right))]
                simp)).trans hlift

/-- The undirected simple graph underlying a constructor-coded nice tree. -/
def graph {bag : Set V} (tree : InductiveNiceTree V bag) :
    SimpleGraph (Node tree) :=
  SimpleGraph.fromRel tree.IsChild

/-- A code child edge has distinct endpoints. -/
theorem ne_of_isChild {bag : Set V} {tree : InductiveNiceTree V bag}
    {parent child : Node tree} (h : tree.IsChild parent child) :
    parent ≠ child := by
  intro heq
  subst child
  have hdepth := depth_eq_add_one_of_isChild tree h
  omega

@[simp] theorem graph_adj {bag : Set V} (tree : InductiveNiceTree V bag)
    (x y : Node tree) :
    tree.graph.Adj x y ↔ tree.IsChild x y ∨ tree.IsChild y x := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h
    · exact ne_of_isChild h
    · exact (ne_of_isChild h).symm

/-- The code graph is connected. -/
theorem graph_connected {bag : Set V} (tree : InductiveNiceTree V bag) :
    tree.graph.Connected := by
  have hroot : ∀ n : Node tree, tree.graph.Reachable (root tree) n := by
    intro n
    induction tree.root_reflTransGen_isChild n with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail hprev hchild ih =>
        exact ih.trans (SimpleGraph.Adj.reachable ((graph_adj tree _ _).2 (Or.inl hchild)))
  exact {
    preconnected := by
      intro x y
      exact (hroot x).symm.trans (hroot y)
    nonempty := ⟨root tree⟩ }

/-- The code graph is acyclic.  At a maximum-depth vertex of a hypothetical
cycle, both cycle neighbours would be parents, contradicting parent
uniqueness. -/
theorem graph_isAcyclic {bag : Set V} (tree : InductiveNiceTree V bag) :
    tree.graph.IsAcyclic := by
  classical
  intro x c hc
  let depths : Finset ℕ := c.support.toFinset.image (depth tree)
  have hdepths : depths.Nonempty := by
    refine ⟨depth tree x, ?_⟩
    exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
  let maxDepth : ℕ := depths.max' hdepths
  have hmaxMem : maxDepth ∈ depths := depths.max'_mem hdepths
  obtain ⟨w, hwfin, hwdepth⟩ := Finset.mem_image.mp hmaxMem
  have hw : w ∈ c.support := by simpa using hwfin
  have hmax : ∀ z ∈ c.support, depth tree z ≤ depth tree w := by
    intro z hz
    have hzmem : depth tree z ∈ depths :=
      Finset.mem_image.mpr ⟨z, by simpa using hz, rfl⟩
    have hle : depth tree z ≤ maxDepth := depths.le_max' _ hzmem
    rw [← hwdepth] at hle
    exact hle
  have hc' : (c.rotate hw).IsCycle := hc.rotate hw
  have hnn : ¬(c.rotate hw).Nil := by
    intro hnil
    exact hc'.ne_nil (SimpleGraph.Walk.nil_iff_eq_nil.mp hnil)
  obtain ⟨y, hadj, p, heq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnn
  rw [heq] at hc'
  have hyw : y ≠ w := by
    intro hyw
    subst y
    exact tree.graph.loopless w hadj
  have hpn : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hyw
  have hyrot : y ∈ (c.rotate hw).support := by
    rw [heq]
    simp
  have hy : y ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c hw).1 hyrot
  have hpenp : p.penultimate ∈ p.support :=
    List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hpn)
  have hpenrot : p.penultimate ∈ (c.rotate hw).support := by
    rw [heq]
    simp [hpenp]
  have hpen : p.penultimate ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c hw).1 hpenrot
  have hyParent : tree.IsChild y w := by
    rcases (graph_adj tree w y).1 hadj with hwy | hyw
    · have hstep := depth_eq_add_one_of_isChild tree hwy
      have hle := hmax y hy
      omega
    · exact hyw
  have hpenParent : tree.IsChild p.penultimate w := by
    have hpenAdj : tree.graph.Adj w p.penultimate :=
      (p.adj_penultimate hpn).symm
    rcases (graph_adj tree w p.penultimate).1 hpenAdj with hwp | hpw
    · have hstep := depth_eq_add_one_of_isChild tree hwp
      have hle := hmax p.penultimate hpen
      omega
    · exact hpw
  have hparents : p.penultimate = y :=
    parent_unique tree hpenParent hyParent
  have hlast : s(p.penultimate, w) ∈ p.edges :=
    SimpleGraph.Walk.mk_penultimate_end_mem_edges hpn
  have hnotmem : s(w, y) ∉ p.edges :=
    ((SimpleGraph.Walk.cons_isCycle_iff p hadj).mp hc').2
  rw [hparents, Sym2.eq_swap] at hlast
  exact hnotmem hlast

/-- Every constructor-coded nice tree has a genuine finite tree as its
underlying undirected graph. -/
theorem graph_isTree {bag : Set V} (tree : InductiveNiceTree V bag) :
    tree.graph.IsTree where
  isConnected := graph_connected tree
  IsAcyclic := graph_isAcyclic tree

/-- A code-descendant witness from the root gives a graph walk whose length is
exactly the endpoint code depth. -/
theorem exists_root_walk_length_eq_depth {bag : Set V}
    {tree : InductiveNiceTree V bag} {n : Node tree}
    (h : Relation.ReflTransGen tree.IsChild (root tree) n) :
    ∃ p : tree.graph.Walk (root tree) n, p.length = depth tree n := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | tail hprev hchild ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.concat ((graph_adj tree _ _).2 (Or.inl hchild)), ?_⟩
      rw [SimpleGraph.Walk.length_concat, hp,
        depth_eq_add_one_of_isChild tree hchild]

/-- Along any code-graph walk, the endpoint depth is at most the start depth
plus the walk length. -/
theorem depth_le_add_walk_length {bag : Set V}
    (tree : InductiveNiceTree V bag) {x y : Node tree}
    (p : tree.graph.Walk x y) :
    depth tree y ≤ depth tree x + p.length := by
  induction p with
  | nil => simp
  | @cons x z y hadj p ih =>
      have hstep : depth tree z ≤ depth tree x + 1 := by
        rcases (graph_adj tree x z).1 hadj with hxz | hzx
        · rw [depth_eq_add_one_of_isChild tree hxz]
        · have hback := depth_eq_add_one_of_isChild tree hzx
          omega
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Graph distance from the constructor root is exactly code depth. -/
theorem graph_dist_root_eq_depth {bag : Set V}
    (tree : InductiveNiceTree V bag) (n : Node tree) :
    tree.graph.dist (root tree) n = depth tree n := by
  have hdesc := root_reflTransGen_isChild tree n
  obtain ⟨codeWalk, hcodeWalk⟩ := exists_root_walk_length_eq_depth hdesc
  have hupper : tree.graph.dist (root tree) n ≤ depth tree n := by
    simpa [hcodeWalk] using tree.graph.dist_le codeWalk
  obtain ⟨p, _hp, hplen⟩ :=
    (graph_connected tree).exists_path_of_dist (root tree) n
  have hlower : depth tree n ≤ tree.graph.dist (root tree) n := by
    rw [← hplen]
    simpa using depth_le_add_walk_length tree p
  omega

/-- The root bag index is exactly the bag of the root position. -/
@[simp] theorem nodeBag_root {bag : Set V} (tree : InductiveNiceTree V bag) :
    nodeBag tree (root tree) = bag := by
  induction tree with
  | leaf =>
      rfl
  | introduce v child _ ih =>
      simpa [nodeBag, root] using congrArg (fun s : Set V => s ∪ {v}) ih
  | forget v child _ ih =>
      simpa [nodeBag, root] using congrArg (fun s : Set V => s \ {v}) ih
  | join left _right ih_left _ih_right =>
      simpa [nodeBag, root] using ih_left

/-- The root children of an introduce node consist of the unique child root. -/
@[simp] theorem children_root_introduce {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (fresh : v ∉ bag) :
    children (introduce v child fresh) (root (introduce v child fresh)) =
      [some (root child)] :=
  rfl

/-- The root children of a forget node consist of the unique child root. -/
@[simp] theorem children_root_forget {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (present : v ∈ bag) :
    children (forget v child present) (root (forget v child present)) =
      [some (root child)] :=
  rfl

/-- The root children of a join node are the two child roots. -/
@[simp] theorem children_root_join {bag : Set V}
    (left right : InductiveNiceTree V bag) :
    children (join left right) (root (join left right)) =
      [some (Sum.inl (root left)), some (Sum.inr (root right))] :=
  rfl

/-- A coded nice tree has finitely many positions. -/
def nodeFintype {bag : Set V} (tree : InductiveNiceTree V bag) :
    Fintype (Node tree) :=
  match tree with
  | leaf => by
      change Fintype PUnit
      infer_instance
  | introduce _ child _ => by
      letI := nodeFintype child
      change Fintype (Option (Node child))
      infer_instance
  | forget _ child _ => by
      letI := nodeFintype child
      change Fintype (Option (Node child))
      infer_instance
  | join left right => by
      letI := nodeFintype left
      letI := nodeFintype right
      change Fintype (Option (Sum (Node left) (Node right)))
      infer_instance

instance instFintypeNode {bag : Set V} (tree : InductiveNiceTree V bag) :
    Fintype (Node tree) :=
  nodeFintype tree

/-! ## Mathematical realization of a constructor code

The constructor shape always supplies the decomposition tree.  To turn it
into a decomposition of a particular graph, callers only have to establish
the three bag axioms.
-/

variable [Fintype V] {G : SimpleGraph V}

/-- Build the mathematical rooted decomposition carried by a constructor
code, assuming its bags cover the graph and have connected occurrences. -/
noncomputable def toRootedTreeDecomposition {bag : Set V}
    (tree : InductiveNiceTree V bag)
    (vertexCoverage : ∀ v : V, ∃ n : Node tree, v ∈ nodeBag tree n)
    (edgeCoverage : ∀ {u v : V}, G.Adj u v →
      ∃ n : Node tree, u ∈ nodeBag tree n ∧ v ∈ nodeBag tree n)
    (connectivity : ∀ v : V,
      (tree.graph.induce {n : Node tree | v ∈ nodeBag tree n}).Preconnected) :
    RootedTreeDecomposition G where
  Node := Node tree
  nodeFintype := nodeFintype tree
  T := tree.graph
  T_istree := graph_isTree tree
  node2bag := nodeBag tree
  VertexCoverage := vertexCoverage
  EdgeCoverage := edgeCoverage
  Connectivity := connectivity
  root := root tree

@[simp] theorem toRootedTreeDecomposition_bag {bag : Set V}
    (tree : InductiveNiceTree V bag)
    (vertexCoverage edgeCoverage connectivity)
    (n : Node tree) :
    (toRootedTreeDecomposition (G := G) tree vertexCoverage edgeCoverage
      connectivity).bag n = nodeBag tree n :=
  rfl

/-- The rooted mathematical depth induced by the code graph is the explicit
code depth. -/
theorem toRootedTreeDecomposition_rootDepth {bag : Set V}
    (tree : InductiveNiceTree V bag)
    (vertexCoverage edgeCoverage connectivity)
    (n : Node tree) :
    (toRootedTreeDecomposition (G := G) tree vertexCoverage edgeCoverage
      connectivity).rootDepth n = depth tree n := by
  exact graph_dist_root_eq_depth tree n

/-- The mathematical child relation derived from the rooted code graph is
exactly the constructor-code child relation. -/
theorem toRootedTreeDecomposition_isChild_iff {bag : Set V}
    (tree : InductiveNiceTree V bag)
    (vertexCoverage edgeCoverage connectivity)
    (parent child : Node tree) :
    (toRootedTreeDecomposition (G := G) tree vertexCoverage edgeCoverage
      connectivity).IsChild parent child ↔ tree.IsChild parent child := by
  let T := toRootedTreeDecomposition (G := G) tree vertexCoverage edgeCoverage
    connectivity
  constructor
  · intro hchild
    have hadj : tree.graph.Adj parent child := hchild.adj
    rcases (graph_adj tree parent child).1 hadj with h | h
    · exact h
    · have hmath := hchild.rootDepth_eq_add_one
      have hcode := depth_eq_add_one_of_isChild tree h
      rw [toRootedTreeDecomposition_rootDepth,
        toRootedTreeDecomposition_rootDepth] at hmath
      omega
  · intro hchild
    apply RootedTreeDecomposition.isChild_of_adj_of_rootDepth_eq_add_one
    · exact (graph_adj tree parent child).2 (Or.inl hchild)
    · rw [toRootedTreeDecomposition_rootDepth,
        toRootedTreeDecomposition_rootDepth,
        depth_eq_add_one_of_isChild tree hchild]

namespace Realization

variable [Fintype V] {G : SimpleGraph V} {bag : Set V}

/--
Compatibility between a coded nice tree and a rooted tree-decomposition.

`realize` sends algorithmic positions to mathematical decomposition nodes.  The
remaining fields say that this map is bijective, preserves the root and bags,
and identifies the explicit child relation of the coded tree with the rooted
child relation of the decomposition.
-/
structure Realizes (tree : InductiveNiceTree V bag)
    (T : RootedTreeDecomposition G) where
  realize : Node tree -> T.Node
  realize_bijective : Function.Bijective realize
  root_eq : realize (root tree) = T.root
  bag_eq : ∀ n : Node tree, T.bag (realize n) = nodeBag tree n
  child_iff : ∀ parent child : Node tree,
    T.IsChild (realize parent) (realize child) ↔ tree.IsChild parent child

end Realization

export Realization (Realizes)

namespace Realizes

variable [Fintype V] {G : SimpleGraph V} {bag : Set V}
variable {tree : InductiveNiceTree V bag} {T : RootedTreeDecomposition G}

set_option linter.unusedSectionVars false in
theorem root_bag_eq (R : Realizes tree T) :
    T.bag T.root = bag := by
  rw [← R.root_eq, R.bag_eq, nodeBag_root]

set_option linter.unusedSectionVars false in
theorem child_iff_realize (R : Realizes tree T)
    (parent child : Node tree) :
    T.IsChild (R.realize parent) (R.realize child) ↔
      tree.IsChild parent child :=
  R.child_iff parent child

end Realizes

end InductiveNiceTree

/--
An inductive nice tree-decomposition of `G`.

The constructor code itself enforces all local nice-node conditions, so the
mathematical component only needs to be a rooted tree-decomposition.  The
realization identifies its root, bags, and child relation with the code; the
predicate-style `IsNice` theorem is consequently derived rather than stored
as redundant structure data.
-/
structure InductiveNiceTreeDecomposition {V : Type u} [Fintype V]
    {G : SimpleGraph V} extends RootedTreeDecomposition G where
  tree : InductiveNiceTree V ∅
  realization :
    InductiveNiceTree.Realizes tree toRootedTreeDecomposition

namespace InductiveNiceTree

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Package a constructor code with verified bag axioms as an inductive nice
tree-decomposition.  The realization is the identity on code nodes. -/
noncomputable def toInductiveNiceTreeDecomposition
    (tree : InductiveNiceTree V ∅)
    (vertexCoverage : ∀ v : V, ∃ n : Node tree, v ∈ nodeBag tree n)
    (edgeCoverage : ∀ {u v : V}, G.Adj u v →
      ∃ n : Node tree, u ∈ nodeBag tree n ∧ v ∈ nodeBag tree n)
    (connectivity : ∀ v : V,
      (tree.graph.induce {n : Node tree | v ∈ nodeBag tree n}).Preconnected) :
    InductiveNiceTreeDecomposition (G := G) := by
  let T := tree.toRootedTreeDecomposition (G := G)
    vertexCoverage edgeCoverage connectivity
  exact {
    toRootedTreeDecomposition := T
    tree := tree
    realization := {
      realize := id
      realize_bijective := Function.bijective_id
      root_eq := rfl
      bag_eq := fun _ => rfl
      child_iff := fun parent child =>
        toRootedTreeDecomposition_isChild_iff tree vertexCoverage
          edgeCoverage connectivity parent child } }

end InductiveNiceTree


namespace InductiveNiceTreeDecomposition

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The algorithm-facing node type of an inductive nice tree-decomposition. -/
abbrev CodeNode (T : InductiveNiceTreeDecomposition (G := G)) : Type (u + 1) :=
  InductiveNiceTree.Node T.tree

/-- The root of the algorithm-facing tree. -/
def codeRoot (T : InductiveNiceTreeDecomposition (G := G)) : T.CodeNode :=
  InductiveNiceTree.root T.tree

/-- The bag computed from the algorithm-facing tree at a code node. -/
def codeBag (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : Set V :=
  InductiveNiceTree.nodeBag T.tree n

/-- The immediate children available to algorithms by structural recursion. -/
def codeChildren (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : List T.CodeNode :=
  InductiveNiceTree.children T.tree n

/-- Interpret an algorithm-facing node as a node of the rooted decomposition. -/
def realize (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : T.Node :=
  T.realization.realize n

@[simp] theorem realize_codeRoot
    (T : InductiveNiceTreeDecomposition (G := G)) :
    T.realize T.codeRoot = T.root :=
  T.realization.root_eq

@[simp] theorem bag_realize
    (T : InductiveNiceTreeDecomposition (G := G)) (n : T.CodeNode) :
    T.toRootedTreeDecomposition.bag (T.realize n) = T.codeBag n :=
  T.realization.bag_eq n

/-- The mathematical root bag is empty because the coded tree is indexed by `∅`. -/
theorem root_empty (T : InductiveNiceTreeDecomposition (G := G)) :
    T.toRootedTreeDecomposition.bag T.root = ∅ :=
  InductiveNiceTree.Realizes.root_bag_eq T.realization

/-- Childhood agrees between the coded tree and the rooted decomposition. -/
theorem child_iff (T : InductiveNiceTreeDecomposition (G := G))
    (parent child : T.CodeNode) :
    T.toRootedTreeDecomposition.IsChild (T.realize parent) (T.realize child) ↔
      T.tree.IsChild parent child :=
  T.realization.child_iff parent child

end InductiveNiceTreeDecomposition

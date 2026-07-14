import GraphMSO.Executable.encoding

/-!
# Correctness of the executable decomposition encoding
-/

namespace GraphMSO.Executable

universe u v w

variable {P : Type} {V : Type v} {omega : ℕ}

@[simp] theorem encodeAny_eq_true_iff [DecidableEq V]
    (s : Finset V) (p : V → Bool) :
    encodeAny s p = true ↔ ∃ x ∈ s, p x = true := by
  induction s using Finset.induction_on with
  | empty => simp [encodeAny]
  | @insert a s ha ih =>
      rw [encodeAny, Finset.fold_insert ha, Bool.or_eq_true]
      change (p a = true ∨ encodeAny s p = true) ↔ _
      rw [ih]
      simp

/-! ## Extensionality for proof-facing sigma letters -/

/-- The four observable sigma-letter predicates determine the whole letter. -/
theorem sigmaLetter_ext_of_observations (A B : SigmaLetter P omega)
    (hverts : ∀ i, A.HasVertex i ↔ B.HasVertex i)
    (hroot : ∀ i, A.RootContains i ↔ B.RootContains i)
    (hadj : ∀ i j, A.AdjOnColors i j ↔ B.AdjOnColors i j)
    (htag : ∀ p i, A.TagOnColor p i ↔ B.TagOnColor p i) :
    A = B := by
  rcases A with ⟨aVerts, aG, aR, aTag⟩
  rcases B with ⟨bVerts, bG, bR, bTag⟩
  have hv : aVerts = bVerts := by
    ext i
    exact hverts i
  subst bVerts
  have hG : aG = bG := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    constructor
    · intro hxy
      have hobs := (hadj x.1 y.1).mp
        ⟨x.2, y.2, hxy⟩
      rcases hobs with ⟨hx, hy, hxy⟩
      have hx' : (⟨x.1, hx⟩ : aVerts) = x := Subtype.ext (by rfl)
      have hy' : (⟨y.1, hy⟩ : aVerts) = y := Subtype.ext (by rfl)
      simpa [hx', hy'] using hxy
    · intro hxy
      have hobs := (hadj x.1 y.1).mpr
        ⟨x.2, y.2, hxy⟩
      rcases hobs with ⟨hx, hy, hxy⟩
      have hx' : (⟨x.1, hx⟩ : aVerts) = x := Subtype.ext (by rfl)
      have hy' : (⟨y.1, hy⟩ : aVerts) = y := Subtype.ext (by rfl)
      simpa [hx', hy'] using hxy
  subst bG
  have hR : aR = bR := by
    ext x
    constructor
    · intro hx
      have hobs := (hroot x.1).mp ⟨x.2, hx⟩
      rcases hobs with ⟨hi, hx⟩
      have hi' : (⟨x.1, hi⟩ : aVerts) = x := Subtype.ext (by rfl)
      simpa [hi'] using hx
    · intro hx
      have hobs := (hroot x.1).mpr ⟨x.2, hx⟩
      rcases hobs with ⟨hi, hx⟩
      have hi' : (⟨x.1, hi⟩ : aVerts) = x := Subtype.ext (by rfl)
      simpa [hi'] using hx
  subst bR
  have hTag : aTag = bTag := by
    funext p x
    apply propext
    constructor
    · intro hx
      have hobs := (htag p x.1).mp ⟨x.2, hx⟩
      rcases hobs with ⟨hi, hx⟩
      have hi' : (⟨x.1, hi⟩ : aVerts) = x := Subtype.ext (by rfl)
      simpa [hi'] using hx
    · intro hx
      have hobs := (htag p x.1).mpr ⟨x.2, hx⟩
      rcases hobs with ⟨hi, hx⟩
      have hi' : (⟨x.1, hi⟩ : aVerts) = x := Subtype.ext (by rfl)
      simpa [hi'] using hx
  subst bTag
  rfl

/-! ## Correctness of one executable letter -/

/-- Decoding the Boolean table built from finite bag data gives the existing
proof-facing decomposition letter. -/
theorem decode_encodeLetter_eq [Fintype V] [DecidableEq V]
    (X : TauPGraph P V) (D : @RootedTreeDecomposition V _ X.toMath.G)
    (color : V → Fin (omega + 1)) (hcolor : D.IsBagColoring color)
    (t : D.Node) (bag adhesion : Finset V)
    (hbag : (bag : Set V) = D.bag t)
    (hadhesion : (adhesion : Set V) = D.adhesion t) :
    (encodeLetter X color bag adhesion).decode =
      D.encodeLetter X.toMath.pred color hcolor t := by
  have hbag_mem (x : V) : x ∈ bag ↔ x ∈ D.bag t := by
    change x ∈ (bag : Set V) ↔ _
    rw [hbag]
  have hadhesion_mem (x : V) : x ∈ adhesion ↔ x ∈ D.adhesion t := by
    change x ∈ (adhesion : Set V) ↔ _
    rw [hadhesion]
  apply sigmaLetter_ext_of_observations
  · intro i
    rw [← ExecSigmaLetter.hasVertex_eq_true_iff,
      D.encodeLetter_hasVertex_iff]
    change encodeAny bag (fun x => decide (color x = i)) = true ↔
      ∃ x ∈ D.bag t, color x = i
    rw [encodeAny_eq_true_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hxi⟩
      exact ⟨x, (hbag_mem x).1 hx, hxi⟩
    · rintro ⟨x, hx, hxi⟩
      exact ⟨x, (hbag_mem x).2 hx, hxi⟩
  · intro i
    rw [← ExecSigmaLetter.rootContains_eq_true_iff,
      D.encodeLetter_rootContains_iff]
    simp only [ExecSigmaLetter.rootContains, Bool.and_eq_true,
      encodeLetter_present, encodeLetter_root, encodeAny_eq_true_iff,
      decide_eq_true_eq]
    constructor
    · rintro ⟨-, x, hx, hxi⟩
      exact ⟨x, (hadhesion_mem x).1 hx, hxi⟩
    · rintro ⟨x, hx, hxi⟩
      have hxbag : x ∈ D.bag t := D.adhesion_subset_bag t hx
      exact ⟨⟨x, (hbag_mem x).2 hxbag, hxi⟩,
        x, (hadhesion_mem x).2 hx, hxi⟩
  · intro i j
    rw [← ExecSigmaLetter.adjOnColors_eq_true_iff,
      D.encodeLetter_adjOnColors_iff]
    simp only [ExecSigmaLetter.adjOnColors, Bool.and_eq_true,
      Bool.or_eq_true, encodeLetter_present, encodeLetter_adj,
      encodeAny_eq_true_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨⟨xi, hxi, hcxi⟩, ⟨xj, hxj, hcxj⟩⟩, -⟩,
        hforward | hreverse⟩
      · rcases hforward with ⟨x, hx, y, hy, ⟨hcx, hcy⟩, hxy⟩
        exact ⟨x, y, (hbag_mem x).1 hx, (hbag_mem y).1 hy, hcx, hcy, hxy⟩
      · rcases hreverse with ⟨x, hx, y, hy, ⟨hcx, hcy⟩, hxy⟩
        exact ⟨y, x, (hbag_mem y).1 hy, (hbag_mem x).1 hx, hcy, hcx,
          X.toMath.G.symm hxy⟩
    · rintro ⟨x, y, hx, hy, hcx, hcy, hxy⟩
      have hne : i ≠ j := by
        intro hij
        have hsame : color x = color y := hcx.trans (hij.trans hcy.symm)
        have hxy' : x = y := hcolor t hx hy hsame
        subst y
        exact X.toMath.G.loopless x hxy
      refine ⟨⟨⟨⟨x, (hbag_mem x).2 hx, hcx⟩,
        ⟨y, (hbag_mem y).2 hy, hcy⟩⟩, hne⟩, Or.inl ?_⟩
      exact ⟨x, (hbag_mem x).2 hx, y, (hbag_mem y).2 hy,
        ⟨hcx, hcy⟩, hxy⟩
  · intro p i
    rw [← ExecSigmaLetter.tagOnColor_eq_true_iff,
      D.encodeLetter_tagOnColor_iff]
    simp only [ExecSigmaLetter.tagOnColor, Bool.and_eq_true,
      encodeLetter_present, encodeLetter_tag, encodeAny_eq_true_iff,
      decide_eq_true_eq]
    constructor
    · rintro ⟨-, x, hx, hxi, hpx⟩
      exact ⟨x, (hbag_mem x).1 hx, hxi, hpx⟩
    · rintro ⟨x, hx, hxi, hpx⟩
      exact ⟨⟨x, (hbag_mem x).2 hx, hxi⟩,
        x, (hbag_mem x).2 hx, hxi, hpx⟩

/-! ## The recursively carried label function -/

/-- The label attached to every code node by the executable traversal. -/
def encodeLabelAux [Fintype V] [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1)) :
    {rootBag : Set V} → (tree : InductiveNiceTree V rootBag) →
      Finset V → Finset V →
        InductiveNiceTree.Node tree → ExecSigmaLetter P omega
  | _, .leaf, bag, adhesion => fun _ =>
      encodeLetter X color bag adhesion
  | _, .introduce v child _, bag, adhesion => fun
      | none => encodeLetter X color bag adhesion
      | some n => encodeLabelAux X color child (bag.erase v) (bag.erase v) n
  | _, .forget v child _, bag, adhesion => fun
      | none => encodeLetter X color bag adhesion
      | some n => encodeLabelAux X color child (insert v bag) bag n
  | _, .join left right, bag, adhesion => fun
      | none => encodeLetter X color bag adhesion
      | some (.inl n) => encodeLabelAux X color left bag bag n
      | some (.inr n) => encodeLabelAux X color right bag bag n

/-- `encodeAux` has exactly the shape and labels described by
`InductiveNiceTree.toBinTree`. -/
theorem encodeAux_eq_toBinTree [Fintype V] [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {rootBag : Set V} (tree : InductiveNiceTree V rootBag)
    (bag adhesion : Finset V) :
    encodeAux X color tree bag adhesion =
      tree.toBinTree (encodeLabelAux X color tree bag adhesion) := by
  induction tree generalizing bag adhesion with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [encodeAux, encodeLabelAux, InductiveNiceTree.toBinTree, ih]
  | forget v child present ih =>
      simp [encodeAux, encodeLabelAux, InductiveNiceTree.toBinTree, ih]
  | join left right ihl ihr =>
      simp [encodeAux, encodeLabelAux, InductiveNiceTree.toBinTree, ihl, ihr]

/-- Mapping a function over an ordered code-tree encoding maps its code-node
label function pointwise. -/
theorem map_toBinTree {A : Type u} {B : Type w} {rootBag : Set V}
    (tree : InductiveNiceTree V rootBag)
    (label : InductiveNiceTree.Node tree → A) (f : A → B) :
    (tree.toBinTree label).map f = tree.toBinTree (fun n => f (label n)) := by
  induction tree with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [InductiveNiceTree.toBinTree, ih]
  | forget v child present ih =>
      simp [InductiveNiceTree.toBinTree, ih]
  | join left right ihl ihr =>
      simp [InductiveNiceTree.toBinTree, ihl, ihr]

/-! ## Finite bags carried through constructors -/

theorem coe_erase_eq_of_coe_eq_union_singleton [DecidableEq V]
    (bag : Finset V) (s : Set V) (v : V)
    (hbag : (bag : Set V) = s ∪ {v}) (hv : v ∉ s) :
    ((bag.erase v : Finset V) : Set V) = s := by
  ext x
  have hmem : x ∈ bag ↔ x ∈ s ∨ x = v := by
    change x ∈ (bag : Set V) ↔ _
    rw [hbag]
    simp [or_comm]
  rw [Finset.mem_coe, Finset.mem_erase, hmem]
  constructor
  · rintro ⟨hxv, hxs | rfl⟩
    · exact hxs
    · exact (hxv rfl).elim
  · intro hxs
    exact ⟨fun hxv => hv (hxv ▸ hxs), Or.inl hxs⟩

theorem coe_insert_eq_of_coe_eq_diff_singleton [DecidableEq V]
    (bag : Finset V) (s : Set V) (v : V)
    (hbag : (bag : Set V) = s \ {v}) (hv : v ∈ s) :
    (((insert v bag : Finset V) : Finset V) : Set V) = s := by
  ext x
  have hmem : x ∈ bag ↔ x ∈ s ∧ x ≠ v := by
    change x ∈ (bag : Set V) ↔ _
    rw [hbag]
    simp
  rw [Finset.mem_coe, Finset.mem_insert, hmem]
  constructor
  · rintro (rfl | ⟨hxs, -⟩)
    · exact hv
    · exact hxs
  · intro hxs
    by_cases hxv : x = v
    · exact Or.inl hxv
    · exact Or.inr ⟨hxs, hxv⟩

/-! ## Pointwise correctness along a realized code tree -/

/-- The recursively computed label at every code node agrees with the
proof-facing letter at the corresponding mathematical decomposition node. -/
theorem encodeLabelAux_decode_eq [Fintype V] [DecidableEq V]
    (X : TauPGraph P V) (D : @RootedTreeDecomposition V _ X.toMath.G)
    (color : V → Fin (omega + 1)) (hcolor : D.IsBagColoring color)
    {rootBag : Set V} (tree : InductiveNiceTree V rootBag)
    (target : InductiveNiceTree.Node tree → D.Node)
    (hbags : ∀ n, D.bag (target n) = InductiveNiceTree.nodeBag tree n)
    (hchildren : ∀ parent child,
      D.IsChild (target parent) (target child) ↔ tree.IsChild parent child)
    (bag adhesion : Finset V) (hbag : (bag : Set V) = rootBag)
    (hadhesion : (adhesion : Set V) =
      D.adhesion (target (InductiveNiceTree.root tree)))
    (n : InductiveNiceTree.Node tree) :
    (encodeLabelAux X color tree bag adhesion n).decode =
      D.encodeLetter X.toMath.pred color hcolor (target n) := by
  induction tree generalizing bag adhesion with
  | leaf =>
      cases n
      apply decode_encodeLetter_eq
      · exact hbag.trans (hbags PUnit.unit).symm
      · exact hadhesion
  | @introduce childBag v child fresh ih =>
      cases n with
      | none =>
          apply decode_encodeLetter_eq
          · exact hbag.trans ((hbags none).trans
              (InductiveNiceTree.nodeBag_root (.introduce v child fresh))).symm
          · exact hadhesion
      | some n =>
          have hchildBag : (((bag.erase v : Finset V) : Finset V) : Set V) = childBag :=
            coe_erase_eq_of_coe_eq_union_singleton bag childBag v hbag fresh
          have hcodeChild :
              (InductiveNiceTree.introduce v child fresh).IsChild none
                (some (InductiveNiceTree.root child)) := by
            simp [InductiveNiceTree.IsChild, InductiveNiceTree.children,
              InductiveNiceTree.root]
          have hmathChild :
              D.IsChild (target none) (target (some (InductiveNiceTree.root child))) :=
            (hchildren _ _).2 hcodeChild
          have hadhesionChild :
              (((bag.erase v : Finset V) : Finset V) : Set V) =
                D.adhesion (target (some (InductiveNiceTree.root child))) := by
            rw [D.adhesion_eq_inter_of_isChild hmathChild,
              hbags (some (InductiveNiceTree.root child)), hbags none]
            simp only [InductiveNiceTree.nodeBag]
            rw [InductiveNiceTree.nodeBag_root,
              Set.inter_eq_left.2 Set.subset_union_left]
            exact hchildBag
          apply ih (target := fun m => target (some m))
              (bag := bag.erase v) (adhesion := bag.erase v)
          · intro m
            simpa [InductiveNiceTree.nodeBag] using hbags (some m)
          · intro parent childNode
            rw [hchildren (some parent) (some childNode)]
            simp only [InductiveNiceTree.IsChild, InductiveNiceTree.children,
              List.mem_map]
            constructor
            · rintro ⟨a, ha, hac⟩
              have hac' : a = childNode := Option.some.inj hac
              simpa [hac'] using ha
            · intro hc
              exact ⟨childNode, hc, rfl⟩
          · exact hchildBag
          · exact hadhesionChild
  | @forget childBag v child present ih =>
      cases n with
      | none =>
          apply decode_encodeLetter_eq
          · exact hbag.trans ((hbags none).trans
              (InductiveNiceTree.nodeBag_root (.forget v child present))).symm
          · exact hadhesion
      | some n =>
          have hchildBag : ((((insert v bag : Finset V) : Finset V)) : Set V) = childBag :=
            coe_insert_eq_of_coe_eq_diff_singleton bag childBag v hbag present
          have hcodeChild :
              (InductiveNiceTree.forget v child present).IsChild none
                (some (InductiveNiceTree.root child)) := by
            simp [InductiveNiceTree.IsChild, InductiveNiceTree.children,
              InductiveNiceTree.root]
          have hmathChild :
              D.IsChild (target none) (target (some (InductiveNiceTree.root child))) :=
            (hchildren _ _).2 hcodeChild
          have hadhesionChild :
              (bag : Set V) =
                D.adhesion (target (some (InductiveNiceTree.root child))) := by
            rw [D.adhesion_eq_inter_of_isChild hmathChild,
              hbags (some (InductiveNiceTree.root child)), hbags none]
            simp only [InductiveNiceTree.nodeBag]
            rw [InductiveNiceTree.nodeBag_root,
              Set.inter_eq_right.2 Set.diff_subset]
            exact hbag
          apply ih (target := fun m => target (some m))
              (bag := insert v bag) (adhesion := bag)
          · intro m
            simpa [InductiveNiceTree.nodeBag] using hbags (some m)
          · intro parent childNode
            rw [hchildren (some parent) (some childNode)]
            simp only [InductiveNiceTree.IsChild, InductiveNiceTree.children,
              List.mem_map]
            constructor
            · rintro ⟨a, ha, hac⟩
              have hac' : a = childNode := Option.some.inj hac
              simpa [hac'] using ha
            · intro hc
              exact ⟨childNode, hc, rfl⟩
          · exact hchildBag
          · exact hadhesionChild
  | @join bagSet left right ihl ihr =>
      cases n with
      | none =>
          apply decode_encodeLetter_eq
          · exact hbag.trans ((hbags none).trans
              (InductiveNiceTree.nodeBag_root (.join left right))).symm
          · exact hadhesion
      | some side =>
          cases side with
          | inl n =>
              have hcodeChild :
                  (InductiveNiceTree.join left right).IsChild none
                    (some (.inl (InductiveNiceTree.root left))) := by
                simp [InductiveNiceTree.IsChild, InductiveNiceTree.children,
                  InductiveNiceTree.root]
              have hmathChild :
                  D.IsChild (target none)
                    (target (some (.inl (InductiveNiceTree.root left)))) :=
                (hchildren _ _).2 hcodeChild
              have hadhesionChild :
                  (bag : Set V) =
                    D.adhesion (target (some (.inl (InductiveNiceTree.root left)))) := by
                rw [D.adhesion_eq_inter_of_isChild hmathChild,
                  hbags (some (.inl (InductiveNiceTree.root left))), hbags none]
                simpa [InductiveNiceTree.nodeBag] using hbag
              apply ihl (target := fun m => target (some (.inl m)))
                  (bag := bag) (adhesion := bag)
              · intro m
                simpa [InductiveNiceTree.nodeBag] using hbags (some (.inl m))
              · intro parent childNode
                rw [hchildren (some (.inl parent)) (some (.inl childNode))]
                simp only [InductiveNiceTree.IsChild, InductiveNiceTree.children,
                  List.mem_map]
                constructor
                · rintro ⟨a, ha, hac⟩
                  have hac' : a = childNode := Sum.inl.inj (Option.some.inj hac)
                  simpa [hac'] using ha
                · intro hc
                  exact ⟨childNode, hc, rfl⟩
              · exact hbag
              · exact hadhesionChild
          | inr n =>
              have hcodeChild :
                  (InductiveNiceTree.join left right).IsChild none
                    (some (.inr (InductiveNiceTree.root right))) := by
                simp [InductiveNiceTree.IsChild, InductiveNiceTree.children,
                  InductiveNiceTree.root]
              have hmathChild :
                  D.IsChild (target none)
                    (target (some (.inr (InductiveNiceTree.root right)))) :=
                (hchildren _ _).2 hcodeChild
              have hadhesionChild :
                  (bag : Set V) =
                    D.adhesion (target (some (.inr (InductiveNiceTree.root right)))) := by
                rw [D.adhesion_eq_inter_of_isChild hmathChild,
                  hbags (some (.inr (InductiveNiceTree.root right))), hbags none]
                simpa [InductiveNiceTree.nodeBag] using hbag
              apply ihr (target := fun m => target (some (.inr m)))
                  (bag := bag) (adhesion := bag)
              · intro m
                simpa [InductiveNiceTree.nodeBag] using hbags (some (.inr m))
              · intro parent childNode
                rw [hchildren (some (.inr parent)) (some (.inr childNode))]
                simp only [InductiveNiceTree.IsChild, InductiveNiceTree.children,
                  List.mem_map]
                constructor
                · rintro ⟨a, ha, hac⟩
                  have hac' : a = childNode := Sum.inr.inj (Option.some.inj hac)
                  simpa [hac'] using ha
                · intro hc
                  exact ⟨childNode, hc, rfl⟩
              · exact hbag
              · exact hadhesionChild

/-! ## End-to-end encoding refinement -/

/-- Decoding every label of the executable ordered encoding recovers the
existing proof-facing ordered encoding exactly. -/
theorem encode_map_decode [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V _ X.toMath.G)
    (color : V → Fin (omega + 1))
    (hcolor : T.tree.IsBagColoring color) :
    (encode X color T.tree).map ExecSigmaLetter.decode =
      T.orderedEncode X.toMath.pred color hcolor := by
  let D : @RootedTreeDecomposition V _ X.toMath.G := T.toRootedTreeDecomposition
  have hcolorMath : D.IsBagColoring color :=
    (T.isBagColoring_iff color).2 hcolor
  have hlabel : ∀ n : T.CodeNode,
      (encodeLabelAux X color T.tree ∅ ∅ n).decode =
        (T.encode X.toMath.pred color hcolor).letter (T.realize n) := by
    intro n
    have h := encodeLabelAux_decode_eq X D color hcolorMath T.tree T.realize
      (fun m => by
        simp [D, InductiveNiceTreeDecomposition.codeBag])
      (fun parent child => T.child_iff parent child)
      ∅ ∅ (by simp) (by
        change ((∅ : Finset V) : Set V) = D.adhesion (T.realize T.codeRoot)
        rw [T.realize_codeRoot]
        change ((∅ : Finset V) : Set V) = D.adhesion D.root
        simp) n
    simpa [D, InductiveNiceTreeDecomposition.encode,
      RootedTreeDecomposition.encode] using h
  unfold encode InductiveNiceTreeDecomposition.orderedEncode
  rw [encodeAux_eq_toBinTree, map_toBinTree]
  apply congrArg (fun label => T.tree.toBinTree label)
  funext n
  exact hlabel n

end GraphMSO.Executable

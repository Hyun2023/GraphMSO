import GraphMSO.Decomp.encoding

open scoped Classical

namespace SimpleGraph

variable {N : Type*} {T : SimpleGraph N}

/-- In a tree, the intersection of two connected vertex sets is connected. -/
theorem IsTree.induce_inter_preconnected (hT : T.IsTree)
    {U W : Set N} (hU : (T.induce U).Preconnected)
    (hW : (T.induce W).Preconnected) :
    (T.induce (U ∩ W)).Preconnected := by
  classical
  intro a b
  have hrU := hU ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
  have hrW := hW ⟨a.1, a.2.2⟩ ⟨b.1, b.2.2⟩
  rcases hrU with ⟨wU⟩
  rcases hrW with ⟨wW⟩
  let inclU : T.induce U →g T :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let inclW : T.induce W →g T :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let pU := wU.toPath
  let pW := wW.toPath
  let qU : T.Path a.1 b.1 := pU.map inclU Subtype.val_injective
  let qW : T.Path a.1 b.1 := pW.map inclW Subtype.val_injective
  have heq : qU = qW := hT.IsAcyclic.path_unique qU qW
  have hsupport : ∀ z ∈ qU.1.support, z ∈ U ∩ W := by
    intro z hz
    constructor
    · have hz' := hz
      change z ∈ (pU.1.map inclU).support at hz'
      rw [SimpleGraph.Walk.support_map] at hz'
      rcases List.mem_map.mp hz' with ⟨zu, _hzu, rfl⟩
      exact zu.2
    · have hz' : z ∈ qW.1.support := by
        rw [← heq]
        exact hz
      change z ∈ (pW.1.map inclW).support at hz'
      rw [SimpleGraph.Walk.support_map] at hz'
      rcases List.mem_map.mp hz' with ⟨zw, _hzw, rfl⟩
      exact zw.2
  exact ⟨qU.1.induce (U ∩ W) hsupport⟩

end SimpleGraph

namespace SigmaTree

variable {P : Type*} {omega : Nat}

abbrev Occurrence (S : SigmaTree P omega) :=
  Σ t : S.Node, (S.letter t).verts

abbrev ColorNode (S : SigmaTree P omega) (i : BagColorSet omega) :=
  {t : S.Node // (S.letter t).HasVertex i}

noncomputable def skeleton (S : SigmaTree P omega) [Fintype S.Node] :
    RootedTreeDecomposition (⊥ : SimpleGraph (Fin 0)) where
  Node := S.Node
  nodeFintype := inferInstance
  T := S.T
  T_istree := S.T_istree
  node2bag := fun _ => ∅
  VertexCoverage := fun v => Fin.elim0 v
  EdgeCoverage := by intro u; exact Fin.elim0 u
  Connectivity := fun v => Fin.elim0 v
  root := S.root

@[simp] theorem skeleton_parent (S : SigmaTree P omega) [Fintype S.Node]
    (t : S.Node) : S.skeleton.parent t = S.parent t := rfl

@[simp] theorem skeleton_isChild_iff (S : SigmaTree P omega) [Fintype S.Node]
    (parent child : S.Node) :
    S.skeleton.IsChild parent child ↔ S.IsChild parent child := Iff.rfl

def colorGraph (S : SigmaTree P omega) (i : BagColorSet omega) :
    SimpleGraph (S.ColorNode i) where
  Adj := fun x y => S.T.Adj x.1 y.1 ∧
    ((S.IsChild x.1 y.1 ∧ (S.letter y.1).RootContains i) ∨
      (S.IsChild y.1 x.1 ∧ (S.letter x.1).RootContains i))
  symm := by
    rintro x y ⟨hxy, h | h⟩
    · exact ⟨hxy.symm, Or.inr h⟩
    · exact ⟨hxy.symm, Or.inl h⟩
  loopless := by
    intro x hx
    exact S.T.loopless x.1 hx.1

def OccRel (S : SigmaTree P omega) (a b : S.Occurrence) : Prop :=
  ∃ (i : BagColorSet omega)
      (ha : (S.letter a.1).HasVertex i)
      (hb : (S.letter b.1).HasVertex i),
    a.2.1 = i ∧ b.2.1 = i ∧
      (S.colorGraph i).Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩

theorem occRel_refl (S : SigmaTree P omega) (a : S.Occurrence) :
    S.OccRel a a :=
  ⟨a.2.1, a.2.2, a.2.2, rfl, rfl, SimpleGraph.Reachable.refl _⟩

theorem occRel_symm (S : SigmaTree P omega) {a b : S.Occurrence}
    (h : S.OccRel a b) : S.OccRel b a := by
  rcases h with ⟨i, ha, hb, hai, hbi, hreach⟩
  exact ⟨i, hb, ha, hbi, hai, hreach.symm⟩

theorem occRel_trans (S : SigmaTree P omega) {a b c : S.Occurrence}
    (hab : S.OccRel a b) (hbc : S.OccRel b c) : S.OccRel a c := by
  rcases hab with ⟨i, ha, hb, hai, hbi, hab⟩
  rcases hbc with ⟨j, hb', hc, hbj, hcj, hbc⟩
  have hij : i = j := hbi.symm.trans hbj
  cases hij
  exact ⟨i, ha, hc, hai, hcj, hab.trans hbc⟩

def occurrenceSetoid (S : SigmaTree P omega) : Setoid S.Occurrence where
  r := S.OccRel
  iseqv := ⟨S.occRel_refl, S.occRel_symm, S.occRel_trans⟩

abbrev DecodedVertex (S : SigmaTree P omega) := Quotient S.occurrenceSetoid

def vertex (S : SigmaTree P omega) (t : S.Node)
    (i : (S.letter t).verts) : S.DecodedVertex :=
  Quotient.mk _ ⟨t, i⟩

theorem vertex_eq_of_occRel (S : SigmaTree P omega) {a b : S.Occurrence}
    (h : S.OccRel a b) :
    Quotient.mk S.occurrenceSetoid a = Quotient.mk S.occurrenceSetoid b :=
  Quotient.sound h

def decodedColor (S : SigmaTree P omega) :
    S.DecodedVertex → BagColorSet omega :=
  Quotient.lift (fun a => a.2.1) (by
    intro a b h
    rcases h with ⟨i, _ha, _hb, hai, hbi, _⟩
    exact hai.trans hbi.symm)

@[simp] theorem decodedColor_vertex (S : SigmaTree P omega) (t : S.Node)
    (i : (S.letter t).verts) :
    S.decodedColor (S.vertex t i) = i.1 := rfl

def colorGraphHom (S : SigmaTree P omega) (i : BagColorSet omega) :
    S.colorGraph i →g S.T where
  toFun := fun t => t.1
  map_rel' := fun h => h.1

theorem colorGraph_adj_of_reachable_of_tree_adj (S : SigmaTree P omega)
    {i : BagColorSet omega} {a b : S.ColorNode i}
    (hreach : (S.colorGraph i).Reachable a b)
    (hadj : S.T.Adj a.1 b.1) :
    (S.colorGraph i).Adj a b := by
  classical
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let pPath : (S.colorGraph i).Path a b := ⟨p, hp⟩
  let mapped : S.T.Path a.1 b.1 :=
    pPath.map (S.colorGraphHom i) Subtype.val_injective
  have hab : a.1 ≠ b.1 := hadj.ne
  let direct : S.T.Walk a.1 b.1 :=
    SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
  have hdirect : direct.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    constructor
    · exact SimpleGraph.Walk.IsPath.nil
    · simpa [direct] using hab
  have heq : mapped = (⟨direct, hdirect⟩ : S.T.Path a.1 b.1) :=
    S.T_istree.IsAcyclic.path_unique _ _
  have hlen : p.length = 1 := by
    have := congrArg (fun q : S.T.Path a.1 b.1 => q.1.length) heq
    simpa [mapped, pPath, direct] using this
  exact p.adj_of_length_eq_one hlen

theorem rootContains_iff_vertex_eq_parent (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) {t : S.Node}
    (ht : t ≠ S.root) (i : BagColorSet omega)
    (hit : (S.letter t).HasVertex i) :
    (S.letter t).RootContains i ↔
      ∃ hip : (S.letter (S.parent t)).HasVertex i,
        S.vertex t ⟨i, hit⟩ = S.vertex (S.parent t) ⟨i, hip⟩ := by
  have hchild : S.IsChild (S.parent t) t := ⟨ht, rfl⟩
  constructor
  · intro hroot
    have hcompat := hlegal.compatible_of_isChild hchild
    have hip := hcompat.1 i hroot
    refine ⟨hip, Quotient.sound ?_⟩
    have hadj : S.T.Adj t (S.parent t) := (S.parent_adj ht).symm
    have hactive : (S.colorGraph i).Adj
        ⟨t, hit⟩ ⟨S.parent t, hip⟩ :=
      ⟨hadj, Or.inr ⟨hchild, hroot⟩⟩
    exact ⟨i, hit, hip, rfl, rfl, SimpleGraph.Adj.reachable hactive⟩
  · rintro ⟨hip, heq⟩
    have hrel : S.OccRel ⟨t, ⟨i, hit⟩⟩
        ⟨S.parent t, ⟨i, hip⟩⟩ := Quotient.exact heq
    rcases hrel with ⟨c, hct, hcp, hitc, hipc, hreach⟩
    have hi : i = c := hitc
    subst c
    have htreeAdj : S.T.Adj t (S.parent t) := (S.parent_adj ht).symm
    have hactive := S.colorGraph_adj_of_reachable_of_tree_adj hreach htreeAdj
    rcases hactive.2 with hwrong | hright
    · have hdown : S.skeleton.IsChild t (S.parent t) := hwrong.1
      have hup : S.skeleton.IsChild (S.parent t) t := hchild
      have hd := hdown.rootDepth_eq_add_one
      have hu := hup.rootDepth_eq_add_one
      omega
    · exact hright.2

theorem tagOnColor_iff_tag (A : SigmaLetter P omega)
    (p : P) (i : BagColorSet omega) (hi : A.HasVertex i) :
    A.TagOnColor p i ↔ A.tag p ⟨i, hi⟩ := by
  constructor
  · rintro ⟨hi', hp⟩
    simpa only [Subsingleton.elim hi' hi] using hp
  · intro hp
    exact ⟨hi, hp⟩

theorem adjOnColors_iff_adj (A : SigmaLetter P omega)
    (i j : BagColorSet omega) (hi : A.HasVertex i) (hj : A.HasVertex j) :
    A.AdjOnColors i j ↔ A.G.Adj ⟨i, hi⟩ ⟨j, hj⟩ := by
  constructor
  · rintro ⟨hi', hj', hadj⟩
    simpa only [Subsingleton.elim hi' hi, Subsingleton.elim hj' hj] using hadj
  · intro hadj
    exact ⟨hi, hj, hadj⟩

theorem tag_iff_of_colorGraph_adj (S : SigmaTree P omega)
    (hlegal : S.IsLegal) (p : P) {i : BagColorSet omega}
    {a b : S.ColorNode i} (hab : (S.colorGraph i).Adj a b) :
    (S.letter a.1).tag p ⟨i, a.2⟩ ↔
      (S.letter b.1).tag p ⟨i, b.2⟩ := by
  rcases hab.2 with h | h
  · have hcompat := hlegal.compatible_of_isChild h.1
    have htags := hcompat.2.2 p i h.2
    exact ((tagOnColor_iff_tag (S.letter b.1) p i b.2).symm.trans
      (htags.trans (tagOnColor_iff_tag (S.letter a.1) p i a.2))).symm
  · have hcompat := hlegal.compatible_of_isChild h.1
    have htags := hcompat.2.2 p i h.2
    exact (tagOnColor_iff_tag (S.letter a.1) p i a.2).symm.trans
      (htags.trans (tagOnColor_iff_tag (S.letter b.1) p i b.2))

theorem tag_iff_of_colorGraph_reachable (S : SigmaTree P omega)
    (hlegal : S.IsLegal) (p : P) {i : BagColorSet omega}
    {a b : S.ColorNode i} (hreach : (S.colorGraph i).Reachable a b) :
    (S.letter a.1).tag p ⟨i, a.2⟩ ↔
      (S.letter b.1).tag p ⟨i, b.2⟩ := by
  rcases hreach with ⟨walk⟩
  induction walk with
  | nil => rfl
  | @cons a next b hadj walk ih =>
      exact (S.tag_iff_of_colorGraph_adj hlegal p hadj).trans ih

def decodedAdj (S : SigmaTree P omega) (x y : S.DecodedVertex) : Prop :=
  ∃ (t : S.Node) (i j : (S.letter t).verts),
    S.vertex t i = x ∧ S.vertex t j = y ∧ (S.letter t).G.Adj i j

def decodedGraph (S : SigmaTree P omega) : SimpleGraph S.DecodedVertex where
  Adj := S.decodedAdj
  symm := by
    rintro x y ⟨t, i, j, hi, hj, hadj⟩
    exact ⟨t, j, i, hj, hi, hadj.symm⟩
  loopless := by
    rintro x ⟨t, i, j, hi, hj, hadj⟩
    have hq : S.vertex t i = S.vertex t j := hi.trans hj.symm
    have hrel : S.OccRel ⟨t, i⟩ ⟨t, j⟩ := Quotient.exact hq
    rcases hrel with ⟨c, _hci, _hcj, hic, hjc, _⟩
    have hij : i = j := Subtype.ext (hic.trans hjc.symm)
    subst j
    exact (S.letter t).G.loopless i hadj

def decodedPred (S : SigmaTree P omega) (p : P) (x : S.DecodedVertex) : Prop :=
  ∃ (t : S.Node) (i : (S.letter t).verts),
    S.vertex t i = x ∧ (S.letter t).tag p i

theorem decodedPred_vertex_iff (S : SigmaTree P omega)
    (hlegal : S.IsLegal) (p : P) (t : S.Node)
    (i : (S.letter t).verts) :
    S.decodedPred p (S.vertex t i) ↔ (S.letter t).tag p i := by
  constructor
  · rintro ⟨s, j, hvertex, htag⟩
    have hrel : S.OccRel ⟨s, j⟩ ⟨t, i⟩ := Quotient.exact hvertex
    rcases hrel with ⟨c, hcs, hct, hjc, hic, hreach⟩
    have hjEq : j = ⟨c, hcs⟩ := Subtype.ext hjc
    have hiEq : i = ⟨c, hct⟩ := Subtype.ext hic
    rw [hjEq] at htag
    rw [hiEq]
    exact (S.tag_iff_of_colorGraph_reachable hlegal p hreach).mp htag
  · intro htag
    exact ⟨t, i, rfl, htag⟩

def decodeTauGraph (S : SigmaTree P omega) : τPGraph P where
  V := S.DecodedVertex
  G := S.decodedGraph
  pred := S.decodedPred

def decodedBag (S : SigmaTree P omega) (t : S.Node) : Set S.DecodedVertex :=
  {x | ∃ i : (S.letter t).verts, S.vertex t i = x}

theorem vertex_mem_decodedBag (S : SigmaTree P omega) (t : S.Node)
    (i : (S.letter t).verts) : S.vertex t i ∈ S.decodedBag t :=
  ⟨i, rfl⟩

theorem colorGraph_reachable_to_decodedBag (S : SigmaTree P omega)
    {i : BagColorSet omega} {a b : S.ColorNode i}
    (hreach : (S.colorGraph i).Reachable a b)
    (x : S.DecodedVertex)
    (ha : S.vertex a.1 ⟨i, a.2⟩ = x) :
    ∃ hb : S.vertex b.1 ⟨i, b.2⟩ = x,
      (S.T.induce {t | x ∈ S.decodedBag t}).Reachable
        ⟨a.1, ⟨⟨i, a.2⟩, ha⟩⟩
        ⟨b.1, ⟨⟨i, b.2⟩, hb⟩⟩ := by
  rcases hreach with ⟨walk⟩
  induction walk with
  | nil => exact ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons a next b hadj walk ih =>
      have hrel : S.OccRel ⟨a.1, ⟨i, a.2⟩⟩
          ⟨next.1, ⟨i, next.2⟩⟩ :=
        ⟨i, a.2, next.2, rfl, rfl,
          SimpleGraph.Adj.reachable hadj⟩
      have hv : S.vertex a.1 ⟨i, a.2⟩ =
          S.vertex next.1 ⟨i, next.2⟩ := Quotient.sound hrel
      have hnext : S.vertex next.1 ⟨i, next.2⟩ = x := hv.symm.trans ha
      obtain ⟨hb, hrest⟩ := ih hnext
      have hedge :
          (S.T.induce {t | x ∈ S.decodedBag t}).Adj
            ⟨a.1, ⟨⟨i, a.2⟩, ha⟩⟩
            ⟨next.1, ⟨⟨i, next.2⟩, hnext⟩⟩ := by
        change S.T.Adj a.1 next.1
        exact hadj.1
      exact ⟨hb, (SimpleGraph.Adj.reachable hedge).trans hrest⟩

noncomputable instance occurrenceFintype (S : SigmaTree P omega)
    [Fintype S.Node] : Fintype S.Occurrence := by
  classical
  exact Fintype.ofFinite S.Occurrence

noncomputable instance decodedVertexFintype (S : SigmaTree P omega)
    [Fintype S.Node] : Fintype S.DecodedVertex := by
  classical
  exact Fintype.ofFinite S.DecodedVertex

noncomputable instance decodeTauGraphFintype (S : SigmaTree P omega)
    [Fintype S.Node] : Fintype S.decodeTauGraph.V := by
  change Fintype S.DecodedVertex
  infer_instance

noncomputable def decodeDecomposition (S : SigmaTree P omega)
    [Fintype S.Node] (_hlegal : S.IsLegal) :
    RootedTreeDecomposition S.decodeTauGraph.G where
  Node := S.Node
  nodeFintype := inferInstance
  T := S.T
  T_istree := S.T_istree
  node2bag := S.decodedBag
  VertexCoverage := by
    intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨t, i⟩
    exact ⟨t, i, rfl⟩
  EdgeCoverage := by
    rintro x y ⟨t, i, j, hi, hj, hadj⟩
    exact ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  Connectivity := by
    intro x a b
    rcases a with ⟨a, haBag⟩
    rcases b with ⟨b, hbBag⟩
    rcases haBag with ⟨ia, hia⟩
    rcases hbBag with ⟨ib, hib⟩
    have hquot : S.vertex a ia = S.vertex b ib := hia.trans hib.symm
    rcases (Quotient.exact hquot : S.OccRel ⟨a, ia⟩ ⟨b, ib⟩) with
      ⟨i, hai, hbi, hcolorA, hcolorB, hreach⟩
    have hiaEq : ia = ⟨i, hai⟩ := Subtype.ext hcolorA
    have hstart : S.vertex a ⟨i, hai⟩ = x := by
      rw [← hiaEq]
      exact hia
    obtain ⟨hend, hlift⟩ :=
      S.colorGraph_reachable_to_decodedBag hreach x hstart
    exact hlift
  root := S.root

@[simp] theorem decodeDecomposition_bag (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (t : S.Node) :
    (S.decodeDecomposition hlegal).bag t = S.decodedBag t := rfl

theorem decodedColor_isBagColoring (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) :
    (S.decodeDecomposition hlegal).IsBagColoring S.decodedColor := by
  intro t x hx y hy hxy
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have hc : i.1 = j.1 := by
    simpa [← hi, ← hj] using hxy
  have hij : i = j := Subtype.ext hc
  subst j
  exact hi.symm.trans hj

theorem decodedColor_image_bag (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (t : S.Node) :
    S.decodedColor '' (S.decodeDecomposition hlegal).bag t =
      (S.letter t).verts := by
  ext i
  constructor
  · rintro ⟨x, ⟨j, hj⟩, hcolor⟩
    have : j.1 = i := by simpa [← hj] using hcolor
    rw [← this]
    exact j.2
  · intro hi
    let j : (S.letter t).verts := ⟨i, hi⟩
    exact ⟨S.vertex t j, S.vertex_mem_decodedBag t j, by
      change j.1 = i
      rfl⟩

def LocalAdj (S : SigmaTree P omega) (x y : S.DecodedVertex)
    (t : S.Node) : Prop :=
  ∃ (i j : (S.letter t).verts),
    S.vertex t i = x ∧ S.vertex t j = y ∧ (S.letter t).G.Adj i j

theorem rootContains_decodedColor_of_mem_parent_bags
    (S : SigmaTree P omega) [Fintype S.Node]
    (hlegal : S.IsLegal) {t : S.Node} (ht : t ≠ S.root)
    {x : S.DecodedVertex} (hxt : x ∈ S.decodedBag t)
    (hxp : x ∈ S.decodedBag (S.parent t)) :
    (S.letter t).RootContains (S.decodedColor x) := by
  rcases hxt with ⟨it, hit⟩
  rcases hxp with ⟨ip, hip⟩
  have hct : it.1 = S.decodedColor x := by
    rw [← hit]
    rfl
  have hcp : ip.1 = S.decodedColor x := by
    rw [← hip]
    rfl
  let it' : (S.letter t).verts := ⟨S.decodedColor x, hct ▸ it.2⟩
  let ip' : (S.letter (S.parent t)).verts :=
    ⟨S.decodedColor x, hcp ▸ ip.2⟩
  have hitEq : it = it' := Subtype.ext hct
  have hipEq : ip = ip' := Subtype.ext hcp
  apply (S.rootContains_iff_vertex_eq_parent hlegal ht
    (S.decodedColor x) it'.2).2
  refine ⟨ip'.2, ?_⟩
  calc
    S.vertex t it' = S.vertex t it := congrArg (S.vertex t) hitEq.symm
    _ = x := hit
    _ = S.vertex (S.parent t) ip := hip.symm
    _ = S.vertex (S.parent t) ip' :=
      congrArg (S.vertex (S.parent t)) hipEq

theorem localAdj_iff_adjOnColors (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (x y : S.DecodedVertex)
    (t : S.Node) (hxt : x ∈ S.decodedBag t) (hyt : y ∈ S.decodedBag t) :
    S.LocalAdj x y t ↔
      (S.letter t).AdjOnColors (S.decodedColor x) (S.decodedColor y) := by
  have hcolor := S.decodedColor_isBagColoring hlegal
  constructor
  · rintro ⟨i, j, hi, hj, hadj⟩
    have hci : i.1 = S.decodedColor x := by rw [← hi]; rfl
    have hcj : j.1 = S.decodedColor y := by rw [← hj]; rfl
    let i' : (S.letter t).verts := ⟨S.decodedColor x, hci ▸ i.2⟩
    let j' : (S.letter t).verts := ⟨S.decodedColor y, hcj ▸ j.2⟩
    have hiEq : i = i' := Subtype.ext hci
    have hjEq : j = j' := Subtype.ext hcj
    rw [hiEq, hjEq] at hadj
    exact ⟨i'.2, j'.2, hadj⟩
  · rintro ⟨hi, hj, hadj⟩
    let i : (S.letter t).verts := ⟨S.decodedColor x, hi⟩
    let j : (S.letter t).verts := ⟨S.decodedColor y, hj⟩
    have hix : S.vertex t i = x := by
      apply hcolor t (S.vertex_mem_decodedBag t i) hxt
      rfl
    have hjy : S.vertex t j = y := by
      apply hcolor t (S.vertex_mem_decodedBag t j) hyt
      rfl
    exact ⟨i, j, hix, hjy, hadj⟩

theorem localAdj_iff_of_tree_adj (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (x y : S.DecodedVertex)
    {a b : S.Node} (hab : S.T.Adj a b)
    (hxa : x ∈ S.decodedBag a) (hya : y ∈ S.decodedBag a)
    (hxb : x ∈ S.decodedBag b) (hyb : y ∈ S.decodedBag b) :
    S.LocalAdj x y a ↔ S.LocalAdj x y b := by
  let D := S.decodeDecomposition hlegal
  rcases (D.adj_iff_isChild_or_isChild).1 hab with habChild | hbaChild
  · have habChild' : S.IsChild a b := habChild
    have hxroot := S.rootContains_decodedColor_of_mem_parent_bags hlegal
      habChild'.1 hxb (by simpa [habChild'.2] using hxa)
    have hyroot := S.rootContains_decodedColor_of_mem_parent_bags hlegal
      habChild'.1 hyb (by simpa [habChild'.2] using hya)
    have hcompat := hlegal.compatible_of_isChild habChild'
    exact (S.localAdj_iff_adjOnColors hlegal x y a hxa hya).trans
      ((hcompat.2.1 (S.decodedColor x) (S.decodedColor y)
        hxroot hyroot).symm.trans
          (S.localAdj_iff_adjOnColors hlegal x y b hxb hyb).symm)
  · have hbaChild' : S.IsChild b a := hbaChild
    have hxroot := S.rootContains_decodedColor_of_mem_parent_bags hlegal
      hbaChild'.1 hxa (by simpa [hbaChild'.2] using hxb)
    have hyroot := S.rootContains_decodedColor_of_mem_parent_bags hlegal
      hbaChild'.1 hya (by simpa [hbaChild'.2] using hyb)
    have hcompat := hlegal.compatible_of_isChild hbaChild'
    exact (S.localAdj_iff_adjOnColors hlegal x y a hxa hya).trans
      ((hcompat.2.1 (S.decodedColor x) (S.decodedColor y)
        hxroot hyroot).trans
          (S.localAdj_iff_adjOnColors hlegal x y b hxb hyb).symm)

def commonBagNodes (S : SigmaTree P omega) (x y : S.DecodedVertex) : Set S.Node :=
  {t | x ∈ S.decodedBag t ∧ y ∈ S.decodedBag t}

theorem localAdj_iff_of_interWalk (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (x y : S.DecodedVertex)
    {a b : S.commonBagNodes x y}
    (walk : (S.T.induce (S.commonBagNodes x y)).Walk a b) :
    S.LocalAdj x y a.1 ↔ S.LocalAdj x y b.1 := by
  induction walk with
  | nil => rfl
  | @cons a next b hadj walk ih =>
    exact (S.localAdj_iff_of_tree_adj hlegal x y hadj
      a.2.1 a.2.2 next.2.1 next.2.2).trans ih

theorem localAdj_iff_of_interReachable (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (x y : S.DecodedVertex)
    {a b : S.Node}
    (ha : x ∈ S.decodedBag a ∧ y ∈ S.decodedBag a)
    (hb : x ∈ S.decodedBag b ∧ y ∈ S.decodedBag b)
    (hreach : (S.T.induce (S.commonBagNodes x y)).Reachable
        ⟨a, ha⟩ ⟨b, hb⟩) :
    S.LocalAdj x y a ↔ S.LocalAdj x y b := by
  rcases hreach with ⟨walk⟩
  exact S.localAdj_iff_of_interWalk hlegal x y walk

theorem decodedAdj_iff_localAdj (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (x y : S.DecodedVertex)
    (t : S.Node) (hxt : x ∈ S.decodedBag t) (hyt : y ∈ S.decodedBag t) :
    S.decodedGraph.Adj x y ↔ S.LocalAdj x y t := by
  constructor
  · rintro ⟨s, i, j, hix, hjy, hadj⟩
    have hxs : x ∈ S.decodedBag s := ⟨i, hix⟩
    have hys : y ∈ S.decodedBag s := ⟨j, hjy⟩
    let D := S.decodeDecomposition hlegal
    have hcommon := S.T_istree.induce_inter_preconnected
      (D.Connectivity x) (D.Connectivity y)
    have hreach : (S.T.induce (S.commonBagNodes x y)).Reachable
        ⟨t, hxt, hyt⟩ ⟨s, hxs, hys⟩ := by
      simpa [D, commonBagNodes] using
        hcommon ⟨t, hxt, hyt⟩ ⟨s, hxs, hys⟩
    exact (S.localAdj_iff_of_interReachable hlegal x y
      ⟨hxt, hyt⟩ ⟨hxs, hys⟩ hreach).2 ⟨i, j, hix, hjy, hadj⟩
  · rintro ⟨i, j, hix, hjy, hadj⟩
    exact ⟨t, i, j, hix, hjy, hadj⟩

theorem decodedAdj_vertex_iff (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (t : S.Node)
    (i j : (S.letter t).verts) :
    S.decodedGraph.Adj (S.vertex t i) (S.vertex t j) ↔
      (S.letter t).G.Adj i j := by
  rw [S.decodedAdj_iff_localAdj hlegal _ _ t
    (S.vertex_mem_decodedBag t i) (S.vertex_mem_decodedBag t j)]
  rw [S.localAdj_iff_adjOnColors hlegal _ _ t
    (S.vertex_mem_decodedBag t i) (S.vertex_mem_decodedBag t j)]
  simpa using adjOnColors_iff_adj (S.letter t) i.1 j.1 i.2 j.2

theorem decodedColor_image_adhesion (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (t : S.Node) :
    S.decodedColor '' (S.decodeDecomposition hlegal).adhesion t =
      {i | (S.letter t).RootContains i} := by
  let D := S.decodeDecomposition hlegal
  ext i
  by_cases ht : t = S.root
  · subst t
    constructor
    · rintro ⟨x, hx, _⟩
      change x ∈ (S.decodeDecomposition hlegal).adhesion
        (S.decodeDecomposition hlegal).root at hx
      rw [(S.decodeDecomposition hlegal).adhesion_root] at hx
      exact hx.elim
    · intro hi
      have hR := hlegal.root_empty
      rcases hi with ⟨_hiv, hiR⟩
      rw [hR] at hiR
      exact hiR.elim
  · rw [(S.decodeDecomposition hlegal).adhesion_eq_inter_parent ht]
    constructor
    · rintro ⟨x, hx, hcolor⟩
      change x ∈ S.decodedBag t ∩ S.decodedBag (S.parent t) at hx
      rcases hx.1 with ⟨it, hit⟩
      rcases hx.2 with ⟨ip, hip⟩
      have hci : it.1 = i := by simpa [← hit] using hcolor
      have hcp : ip.1 = i := by
        have : S.decodedColor (S.vertex (S.parent t) ip) = i := by
          rw [hip]
          exact hcolor
        simpa using this
      let it' : (S.letter t).verts := ⟨i, hci ▸ it.2⟩
      let ip' : (S.letter (S.parent t)).verts := ⟨i, hcp ▸ ip.2⟩
      have hitEq : it = it' := Subtype.ext hci
      have hipEq : ip = ip' := Subtype.ext hcp
      have heq : S.vertex t it' = S.vertex (S.parent t) ip' := by
        rw [← hitEq, ← hipEq, hit, hip]
      exact (S.rootContains_iff_vertex_eq_parent hlegal ht i it'.2).2
        ⟨ip'.2, heq⟩
    · intro hroot
      have hit : (S.letter t).HasVertex i := by
        rcases hroot with ⟨hit, _⟩
        exact hit
      obtain ⟨hip, heq⟩ :=
        (S.rootContains_iff_vertex_eq_parent hlegal ht i hit).1 hroot
      let it : (S.letter t).verts := ⟨i, hit⟩
      let ip : (S.letter (S.parent t)).verts := ⟨i, hip⟩
      refine ⟨S.vertex t it, ⟨S.vertex_mem_decodedBag t it, ?_⟩, ?_⟩
      · exact ⟨ip, heq.symm⟩
      · rfl

/-- Two sigma letters carry the same color-indexed relational data. -/
def SigmaLetter.Equivalent (A B : SigmaLetter P omega) : Prop :=
  (∀ i, A.HasVertex i ↔ B.HasVertex i) ∧
  (∀ i, A.RootContains i ↔ B.RootContains i) ∧
  (∀ i j, A.AdjOnColors i j ↔ B.AdjOnColors i j) ∧
  (∀ p i, A.TagOnColor p i ↔ B.TagOnColor p i)

theorem decode_encode_letter_equivalent (S : SigmaTree P omega)
    [Fintype S.Node] (hlegal : S.IsLegal) (t : S.Node) :
    SigmaLetter.Equivalent
      ((S.decodeDecomposition hlegal).encodeLetter S.decodedPred
        S.decodedColor (S.decodedColor_isBagColoring hlegal) t)
      (S.letter t) := by
  let D := S.decodeDecomposition hlegal
  let hcolor := S.decodedColor_isBagColoring hlegal
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [D.encodeLetter_hasVertex_iff]
    simpa [D] using Set.ext_iff.mp (S.decodedColor_image_bag hlegal t) i
  · intro i
    rw [D.encodeLetter_rootContains_iff]
    simpa [D] using Set.ext_iff.mp (S.decodedColor_image_adhesion hlegal t) i
  · intro i j
    rw [D.encodeLetter_adjOnColors_iff]
    constructor
    · rintro ⟨x, y, hxt, hyt, hxi, hyj, hxy⟩
      have hlocal := (S.decodedAdj_iff_localAdj hlegal x y t hxt hyt).1 hxy
      have hcolors :=
        (S.localAdj_iff_adjOnColors hlegal x y t hxt hyt).1 hlocal
      simpa [hxi, hyj] using hcolors
    · intro hij
      rcases hij with ⟨hi, hj, hadj⟩
      let ii : (S.letter t).verts := ⟨i, hi⟩
      let jj : (S.letter t).verts := ⟨j, hj⟩
      refine ⟨S.vertex t ii, S.vertex t jj,
        S.vertex_mem_decodedBag t ii, S.vertex_mem_decodedBag t jj,
        rfl, rfl, ?_⟩
      exact (S.decodedAdj_vertex_iff hlegal t ii jj).2 hadj
  · intro p i
    rw [D.encodeLetter_tagOnColor_iff]
    constructor
    · rintro ⟨x, hxt, hxi, hpx⟩
      rcases hxt with ⟨j, rfl⟩
      have hji : j.1 = i := by simpa using hxi
      have hpj := (S.decodedPred_vertex_iff hlegal p t j).1 hpx
      have htag : (S.letter t).TagOnColor p j.1 :=
        (tagOnColor_iff_tag (S.letter t) p j.1 j.2).2 hpj
      simpa [hji] using htag
    · intro hip
      rcases hip with ⟨hi, hp⟩
      let ii : (S.letter t).verts := ⟨i, hi⟩
      refine ⟨S.vertex t ii, S.vertex_mem_decodedBag t ii, rfl, ?_⟩
      exact (S.decodedPred_vertex_iff hlegal p t ii).2 hp

section DecodeEncoding

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def occurrenceOriginal (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.IsBagColoring color)
    (a : (T.encode vpred color hcolor).Occurrence) : V :=
  Classical.choose a.2.2

theorem occurrenceOriginal_mem (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.IsBagColoring color)
    (a : (T.encode vpred color hcolor).Occurrence) :
    occurrenceOriginal T vpred color hcolor a ∈ T.bag a.1 :=
  (Classical.choose_spec a.2.2).1

theorem occurrenceOriginal_color (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.IsBagColoring color)
    (a : (T.encode vpred color hcolor).Occurrence) :
    color (occurrenceOriginal T vpred color hcolor a) = a.2.1 :=
  (Classical.choose_spec a.2.2).2

theorem occurrenceOriginal_eq_of_active_child
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {i : BagColorSet omega} {parent child : T.Node}
    (hchild : (T.encode vpred color hcolor).IsChild parent child)
    (hroot : (T.encodeLetter vpred color hcolor child).RootContains i)
    (hip : (T.encodeLetter vpred color hcolor parent).HasVertex i)
    (hic : (T.encodeLetter vpred color hcolor child).HasVertex i) :
    occurrenceOriginal T vpred color hcolor
        ⟨parent, ⟨i, hip⟩⟩ =
      occurrenceOriginal T vpred color hcolor
        ⟨child, ⟨i, hic⟩⟩ := by
  rw [T.encodeLetter_rootContains_iff] at hroot
  rcases hroot with ⟨w, hwadh, hwi⟩
  have hwchild : w ∈ T.bag child := T.adhesion_subset_bag child hwadh
  have hwparent : w ∈ T.bag parent := by
    have hwinter : w ∈ T.bag child ∩ T.bag (T.parent child) := by
      rw [← T.adhesion_eq_inter_parent hchild.1]
      exact hwadh
    simpa [hchild.2] using hwinter.2
  have hparent := hcolor parent
    (occurrenceOriginal_mem T vpred color hcolor ⟨parent, ⟨i, hip⟩⟩)
    hwparent
    ((occurrenceOriginal_color T vpred color hcolor
      ⟨parent, ⟨i, hip⟩⟩).trans hwi.symm)
  have hchildEq := hcolor child
    (occurrenceOriginal_mem T vpred color hcolor ⟨child, ⟨i, hic⟩⟩)
    hwchild
    ((occurrenceOriginal_color T vpred color hcolor
      ⟨child, ⟨i, hic⟩⟩).trans hwi.symm)
  exact hparent.trans hchildEq.symm

theorem occurrenceOriginal_eq_of_colorGraph_adj
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {i : BagColorSet omega}
    {a b : (T.encode vpred color hcolor).ColorNode i}
    (hab : ((T.encode vpred color hcolor).colorGraph i).Adj a b) :
    occurrenceOriginal T vpred color hcolor ⟨a.1, ⟨i, a.2⟩⟩ =
      occurrenceOriginal T vpred color hcolor ⟨b.1, ⟨i, b.2⟩⟩ := by
  rcases hab.2 with hchild | hchild
  · exact occurrenceOriginal_eq_of_active_child T vpred color hcolor
      hchild.1 hchild.2 a.2 b.2
  · exact (occurrenceOriginal_eq_of_active_child T vpred color hcolor
      hchild.1 hchild.2 b.2 a.2).symm

theorem occurrenceOriginal_eq_of_colorGraph_reachable
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {i : BagColorSet omega}
    {a b : (T.encode vpred color hcolor).ColorNode i}
    (hreach : ((T.encode vpred color hcolor).colorGraph i).Reachable a b) :
    occurrenceOriginal T vpred color hcolor ⟨a.1, ⟨i, a.2⟩⟩ =
      occurrenceOriginal T vpred color hcolor ⟨b.1, ⟨i, b.2⟩⟩ := by
  rcases hreach with ⟨walk⟩
  induction walk with
  | nil => rfl
  | @cons a next b hadj walk ih =>
      exact (occurrenceOriginal_eq_of_colorGraph_adj T vpred color hcolor
        hadj).trans ih

def bagsColorGraphHom (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.IsBagColoring color) (v : V) :
    T.T.induce {t | v ∈ T.bag t} →g
      (T.encode vpred color hcolor).colorGraph (color v) where
  toFun := fun t => ⟨t.1, ⟨v, t.2, rfl⟩⟩
  map_rel' := by
    intro a b hab
    change T.T.Adj a.1 b.1 at hab
    refine ⟨hab, ?_⟩
    rcases (T.adj_iff_isChild_or_isChild).1 hab with hchild | hchild
    · left
      refine ⟨hchild, ?_⟩
      change (T.encodeLetter vpred color hcolor b.1).RootContains (color v)
      rw [T.encodeLetter_rootContains_iff]
      refine ⟨v, ?_, rfl⟩
      rw [T.adhesion_eq_inter_parent hchild.1]
      exact ⟨b.2, by rw [← hchild.2]; exact a.2⟩
    · right
      refine ⟨hchild, ?_⟩
      change (T.encodeLetter vpred color hcolor a.1).RootContains (color v)
      rw [T.encodeLetter_rootContains_iff]
      refine ⟨v, ?_, rfl⟩
      rw [T.adhesion_eq_inter_parent hchild.1]
      exact ⟨a.2, by rw [← hchild.2]; exact b.2⟩

theorem occurrenceOriginal_eq_of_occRel
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {a b : (T.encode vpred color hcolor).Occurrence}
    (hab : (T.encode vpred color hcolor).OccRel a b) :
    occurrenceOriginal T vpred color hcolor a =
      occurrenceOriginal T vpred color hcolor b := by
  rcases hab with ⟨i, hai, hbi, haColor, hbColor, hreach⟩
  have haEq : a.2 = ⟨i, hai⟩ := Subtype.ext haColor
  have hbEq : b.2 = ⟨i, hbi⟩ := Subtype.ext hbColor
  have haSigma : a = ⟨a.1, ⟨i, hai⟩⟩ :=
    Sigma.ext rfl (heq_of_eq haEq)
  have hbSigma : b = ⟨b.1, ⟨i, hbi⟩⟩ :=
    Sigma.ext rfl (heq_of_eq hbEq)
  rw [haSigma, hbSigma]
  exact occurrenceOriginal_eq_of_colorGraph_reachable
    T vpred color hcolor hreach

theorem occRel_of_occurrenceOriginal_eq
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {a b : (T.encode vpred color hcolor).Occurrence}
    (hab : occurrenceOriginal T vpred color hcolor a =
      occurrenceOriginal T vpred color hcolor b) :
    (T.encode vpred color hcolor).OccRel a b := by
  let v := occurrenceOriginal T vpred color hcolor a
  have hva : v ∈ T.bag a.1 := occurrenceOriginal_mem T vpred color hcolor a
  have hvb : v ∈ T.bag b.1 := by
    change occurrenceOriginal T vpred color hcolor a ∈ T.bag b.1
    rw [hab]
    exact occurrenceOriginal_mem T vpred color hcolor b
  have hcolorA : color v = a.2.1 :=
    occurrenceOriginal_color T vpred color hcolor a
  have hcolorB : color v = b.2.1 := by
    change color (occurrenceOriginal T vpred color hcolor a) = b.2.1
    rw [hab]
    exact occurrenceOriginal_color T vpred color hcolor b
  have haMem : (T.encodeLetter vpred color hcolor a.1).HasVertex (color v) :=
    ⟨v, hva, rfl⟩
  have hbMem : (T.encodeLetter vpred color hcolor b.1).HasVertex (color v) :=
    ⟨v, hvb, rfl⟩
  let source : {t : T.Node // v ∈ T.bag t} := ⟨a.1, hva⟩
  let target : {t : T.Node // v ∈ T.bag t} := ⟨b.1, hvb⟩
  have hreachBag := T.Connectivity v source target
  have hreachColor := hreachBag.map
    (bagsColorGraphHom T vpred color hcolor v)
  have hsource : (bagsColorGraphHom T vpred color hcolor v) source =
      ⟨a.1, haMem⟩ := by
    apply Subtype.ext
    rfl
  have htarget : (bagsColorGraphHom T vpred color hcolor v) target =
      ⟨b.1, hbMem⟩ := by
    apply Subtype.ext
    rfl
  rw [hsource, htarget] at hreachColor
  exact ⟨color v, haMem, hbMem, hcolorA.symm, hcolorB.symm, hreachColor⟩

theorem occRel_iff_occurrenceOriginal_eq
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    {a b : (T.encode vpred color hcolor).Occurrence} :
    (T.encode vpred color hcolor).OccRel a b ↔
      occurrenceOriginal T vpred color hcolor a =
        occurrenceOriginal T vpred color hcolor b :=
  ⟨occurrenceOriginal_eq_of_occRel T vpred color hcolor,
    occRel_of_occurrenceOriginal_eq T vpred color hcolor⟩

noncomputable def decodeToOriginal (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.IsBagColoring color) :
    (T.encode vpred color hcolor).DecodedVertex → V :=
  Quotient.lift (occurrenceOriginal T vpred color hcolor)
    (by
      intro a b hab
      exact occurrenceOriginal_eq_of_occRel T vpred color hcolor hab)

@[simp] theorem decodeToOriginal_vertex
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) (i : (T.encodeLetter vpred color hcolor t).verts) :
    decodeToOriginal T vpred color hcolor
      ((T.encode vpred color hcolor).vertex t i) =
      occurrenceOriginal T vpred color hcolor ⟨t, i⟩ := rfl

theorem occurrenceOriginal_eq_of_mem
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) (u : V) (hu : u ∈ T.bag t) :
    occurrenceOriginal T vpred color hcolor
      ⟨t, ⟨color u, ⟨u, hu, rfl⟩⟩⟩ = u := by
  apply hcolor t
    (occurrenceOriginal_mem T vpred color hcolor
      ⟨t, ⟨color u, ⟨u, hu, rfl⟩⟩⟩)
    hu
  exact occurrenceOriginal_color T vpred color hcolor
    ⟨t, ⟨color u, ⟨u, hu, rfl⟩⟩⟩

theorem decodeToOriginal_bijective
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color) :
    Function.Bijective (decodeToOriginal T vpred color hcolor) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro a b hab
    exact Quotient.sound
      ((occRel_iff_occurrenceOriginal_eq T vpred color hcolor).2 hab)
  · intro v
    rcases T.VertexCoverage v with ⟨t, ht⟩
    let i : (T.encodeLetter vpred color hcolor t).verts :=
      ⟨color v, ⟨v, ht, rfl⟩⟩
    refine ⟨(T.encode vpred color hcolor).vertex t i, ?_⟩
    exact occurrenceOriginal_eq_of_mem T vpred color hcolor t v ht

noncomputable def decodeOriginalEquiv
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color) :
    (T.encode vpred color hcolor).DecodedVertex ≃ V :=
  Equiv.ofBijective (decodeToOriginal T vpred color hcolor)
    (decodeToOriginal_bijective T vpred color hcolor)

@[simp] theorem decodeOriginalEquiv_apply
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (x : (T.encode vpred color hcolor).DecodedVertex) :
    decodeOriginalEquiv T vpred color hcolor x =
      decodeToOriginal T vpred color hcolor x := rfl

theorem encodeLetter_adj_iff_occurrenceOriginal
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) (i j : (T.encodeLetter vpred color hcolor t).verts) :
    (T.encodeLetter vpred color hcolor t).G.Adj i j ↔
      G.Adj (occurrenceOriginal T vpred color hcolor ⟨t, i⟩)
        (occurrenceOriginal T vpred color hcolor ⟨t, j⟩) := by
  constructor
  · rintro ⟨u, v, hu, hv, hui, hvj, huv⟩
    have huEq : occurrenceOriginal T vpred color hcolor ⟨t, i⟩ = u :=
      hcolor t (occurrenceOriginal_mem T vpred color hcolor ⟨t, i⟩) hu
        ((occurrenceOriginal_color T vpred color hcolor ⟨t, i⟩).trans hui.symm)
    have hvEq : occurrenceOriginal T vpred color hcolor ⟨t, j⟩ = v :=
      hcolor t (occurrenceOriginal_mem T vpred color hcolor ⟨t, j⟩) hv
        ((occurrenceOriginal_color T vpred color hcolor ⟨t, j⟩).trans hvj.symm)
    simpa [huEq, hvEq] using huv
  · intro huv
    exact ⟨occurrenceOriginal T vpred color hcolor ⟨t, i⟩,
      occurrenceOriginal T vpred color hcolor ⟨t, j⟩,
      occurrenceOriginal_mem T vpred color hcolor ⟨t, i⟩,
      occurrenceOriginal_mem T vpred color hcolor ⟨t, j⟩,
      occurrenceOriginal_color T vpred color hcolor ⟨t, i⟩,
      occurrenceOriginal_color T vpred color hcolor ⟨t, j⟩, huv⟩

theorem encodeLetter_tag_iff_occurrenceOriginal
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (p : P) (t : T.Node) (i : (T.encodeLetter vpred color hcolor t).verts) :
    (T.encodeLetter vpred color hcolor t).tag p i ↔
      vpred p (occurrenceOriginal T vpred color hcolor ⟨t, i⟩) := by
  constructor
  · rintro ⟨u, hu, hui, hpu⟩
    have huEq : occurrenceOriginal T vpred color hcolor ⟨t, i⟩ = u :=
      hcolor t (occurrenceOriginal_mem T vpred color hcolor ⟨t, i⟩) hu
        ((occurrenceOriginal_color T vpred color hcolor ⟨t, i⟩).trans hui.symm)
    simpa [huEq] using hpu
  · intro hp
    exact ⟨occurrenceOriginal T vpred color hcolor ⟨t, i⟩,
      occurrenceOriginal_mem T vpred color hcolor ⟨t, i⟩,
      occurrenceOriginal_color T vpred color hcolor ⟨t, i⟩, hp⟩

theorem decodedEncoding_adj_iff
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (x y : (T.encode vpred color hcolor).DecodedVertex) :
    (T.encode vpred color hcolor).decodedGraph.Adj x y ↔
      G.Adj (decodeToOriginal T vpred color hcolor x)
        (decodeToOriginal T vpred color hcolor y) := by
  constructor
  · rintro ⟨t, i, j, hix, hjy, hij⟩
    have horig := (encodeLetter_adj_iff_occurrenceOriginal
      T vpred color hcolor t i j).1 hij
    have hx := congrArg (decodeToOriginal T vpred color hcolor) hix
    have hy := congrArg (decodeToOriginal T vpred color hcolor) hjy
    simpa using hx ▸ hy ▸ horig
  · intro hxy
    revert hxy
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab
    rcases T.EdgeCoverage hab with ⟨t, ha, hb⟩
    let i : (T.encodeLetter vpred color hcolor t).verts :=
      ⟨color (occurrenceOriginal T vpred color hcolor a),
        ⟨occurrenceOriginal T vpred color hcolor a, ha, rfl⟩⟩
    let j : (T.encodeLetter vpred color hcolor t).verts :=
      ⟨color (occurrenceOriginal T vpred color hcolor b),
        ⟨occurrenceOriginal T vpred color hcolor b, hb, rfl⟩⟩
    have hiOrig : occurrenceOriginal T vpred color hcolor ⟨t, i⟩ =
        occurrenceOriginal T vpred color hcolor a :=
      occurrenceOriginal_eq_of_mem T vpred color hcolor t _ ha
    have hjOrig : occurrenceOriginal T vpred color hcolor ⟨t, j⟩ =
        occurrenceOriginal T vpred color hcolor b :=
      occurrenceOriginal_eq_of_mem T vpred color hcolor t _ hb
    have hix : (T.encode vpred color hcolor).vertex t i =
        Quotient.mk _ a := Quotient.sound
      ((occRel_iff_occurrenceOriginal_eq T vpred color hcolor).2 hiOrig)
    have hjy : (T.encode vpred color hcolor).vertex t j =
        Quotient.mk _ b := Quotient.sound
      ((occRel_iff_occurrenceOriginal_eq T vpred color hcolor).2 hjOrig)
    refine ⟨t, i, j, hix, hjy, ?_⟩
    exact (encodeLetter_adj_iff_occurrenceOriginal
      T vpred color hcolor t i j).2 (hiOrig ▸ hjOrig ▸ hab)

theorem decodedEncoding_pred_iff
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color)
    (p : P) (x : (T.encode vpred color hcolor).DecodedVertex) :
    (T.encode vpred color hcolor).decodedPred p x ↔
      vpred p (decodeToOriginal T vpred color hcolor x) := by
  constructor
  · rintro ⟨t, i, hix, hpi⟩
    have horig := (encodeLetter_tag_iff_occurrenceOriginal
      T vpred color hcolor p t i).1 hpi
    have hx := congrArg (decodeToOriginal T vpred color hcolor) hix
    simpa using hx ▸ horig
  · refine Quotient.inductionOn x ?_
    intro a ha
    refine ⟨a.1, a.2, rfl, ?_⟩
    exact (encodeLetter_tag_iff_occurrenceOriginal
      T vpred color hcolor p a.1 a.2).2 ha

structure τPGraph.Iso (X Y : τPGraph P) where
  toEquiv : X.V ≃ Y.V
  adj_iff : ∀ x y, X.G.Adj x y ↔ Y.G.Adj (toEquiv x) (toEquiv y)
  pred_iff : ∀ p x, X.pred p x ↔ Y.pred p (toEquiv x)

noncomputable def decode_encode_iso
    (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V → BagColorSet omega) (hcolor : T.IsBagColoring color) :
    τPGraph.Iso (T.encode vpred color hcolor).decodeTauGraph
      ({ V := V, G := G, pred := vpred } : τPGraph P) where
  toEquiv := decodeOriginalEquiv T vpred color hcolor
  adj_iff := decodedEncoding_adj_iff T vpred color hcolor
  pred_iff := decodedEncoding_pred_iff T vpred color hcolor

end DecodeEncoding

end SigmaTree


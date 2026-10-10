import OAI.RingTheory.BassTrace.MarkedSubdivisions

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

open scoped Classical Topology

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

def activatedUnion (A : I → Set V) (B : I → Set X) (x : X) : Set V :=
  ⋃ i, if x ∈ B i then A i else ∅

def replacementSet (P Z : Set V) (U S : I → Set V) (B : I → Set X) (x : X) : Set V :=
  (Z \ activatedUnion U B x) ∪ (P ∩ activatedUnion S B x)

omit [TopologicalSpace X] in
lemma activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    (A : I → Set V) (hA : ∀ i, IsMarked T (A i)) (B : I → Set X) (x : X) :
    IsMarked T (activatedUnion A B x) := by
  apply IsMarked.iUnion
  intro i
  split_ifs
  · exact hA i
  · intro p hp
    exact hp.elim

omit [TopologicalSpace X] in
lemma difference_activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    {Z : Set V} (hZ : IsMarked T Z) (U : I → Set V)
    (hU : ∀ i, IsMarked T (T.space \ U i)) (B : I → Set X) (x : X) :
    IsMarked T (Z \ activatedUnion U B x) := by
  have hh := hZ.inter_iInter (I := I)
    (Q := fun i => if x ∈ B i then (U i)ᶜ else Set.univ) (by
      intro i
      split_ifs
      · exact hU i
      · simpa only [Set.inter_univ] using isMarked_space T)
  convert hh using 1
  ext p
  simp only [Set.mem_sdiff,activatedUnion,Set.mem_iUnion,Set.mem_inter_iff,
    Set.mem_iInter]
  constructor
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun i => ?_⟩
    by_cases hi : x ∈ B i
    · simp only [hi,ite_true,Set.mem_compl_iff]
      intro hpi
      exact hout ⟨i,by simpa only [hi,ite_true] using hpi⟩
    · simp only [hi,ite_false,Set.mem_univ]
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun ⟨i,hi⟩ => ?_⟩
    have hoi := hout i
    by_cases hxi : x ∈ B i
    · simp only [hxi,ite_true] at hi hoi
      exact hoi hi
    · simp only [hxi,ite_false,Set.mem_empty_iff_false] at hi

omit [TopologicalSpace X] in
lemma replacementSet_marked (T : Geometry.SimplicialComplex ℝ V)
    {P Z : Set V} (hP : IsMarked T P) (hZ : IsMarked T Z)
    (U S : I → Set V) (hU : ∀ i, IsMarked T (T.space \ U i))
    (hS : ∀ i, IsMarked T (S i)) (B : I → Set X) (x : X) :
    IsMarked T (replacementSet P Z U S B x) := by
  exact (difference_activatedUnion_marked T hZ U hU B x).union
    (hP.inter (activatedUnion_marked T S hS B x))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] in
lemma replacementSet_subset {P Z : Set V} (hZ : Z ⊆ P)
    (U S : I → Set V) (B : I → Set X) (x : X) :
    replacementSet P Z U S B x ⊆ P := by
  intro p hp
  exact hp.elim (fun h => hZ h.1) (fun h => h.1)

namespace MarkedFamily

def replacement {T : SubdivisionFamily X K} (P Z : MarkedFamily T)
    (U S : I → Set V) (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hU : ∀ x i, IsMarked (T.val x).complex ((T.val x).complex.space \ U i))
    (hS : ∀ x i, IsMarked (T.val x).complex (S i))
    (hfinU : ∀ s ∈ K.faces, {i | (U i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces, {i | (S i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite) :
    MarkedFamily T :=
  ofSets T (fun x => replacementSet (P.val x) (Z.val x) U S B x)
    (fun x => replacementSet_marked (T.val x).complex (P.marked x) (Z.marked x)
      U S (hU x) (hS x) B x) (by
    intro s hs
    let Q := convexHull ℝ (s : Set V)
    have hZ := Z.set_localConstancy s hs
    have hP := P.set_localConstancy s hs
    have hU' := locallyConstant_active_union U B hB Q (hfinU s hs)
    have hS' := locallyConstant_active_union S B hB Q (hfinS s hs)
    have hh := (hZ.comp₂ hU' Set.diff).comp₂ (hP.comp₂ hS' Set.inter) Set.union
    convert hh using 1
    ext x p
    change (((p ∈ Z.val x ∧ p ∉ activatedUnion U B x) ∨
      (p ∈ P.val x ∧ p ∈ activatedUnion S B x)) ∧ p ∈ Q) ↔
      (((p ∈ Z.val x ∧ p ∈ Q) ∧ ¬ (p ∈ activatedUnion U B x ∧ p ∈ Q)) ∨
       ((p ∈ P.val x ∧ p ∈ Q) ∧ (p ∈ activatedUnion S B x ∧ p ∈ Q)))
    tauto)

end MarkedFamily

end

open Set Finset

open scoped Topology

variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma sphereUnion_componentDiameter (ρ : V → V → ℝ) (P : Set V)
    (hP : P ⊆ K.space) (f : I → V → ℝ) (t R : ℝ)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ (P \ (P ∩ ⋃ i, {p | f i p = t})) (2*R) := by
  intro C hC hCP p hp q hq
  have hCK : C ⊆ K.space := fun y hy => hP (hCP hy).1
  obtain ⟨i,hip⟩ := hcover p (hCK hp)
  have hq' : f i q < t := by
    by_contra hh
    obtain ⟨z,hz,hzt⟩ := hC.intermediate_value hp hq ((hcont i).mono hCK)
      ⟨hip.le,le_of_not_gt hh⟩
    exact (hCP hz).2 ⟨(hCP hz).1,Set.mem_iUnion.mpr ⟨i,hzt⟩⟩
  exact (htriangle i p (hCK hp) q (hCK hq)).trans (by linarith)

namespace UniversalCuts

variable (d : UniversalCuts V J)

def sphereStep (T : SubdivisionFamily X K) (P : MarkedFamily T)
    (ρ : V → V → ℝ) (R t : ℝ) (f : I → V → ℝ)
    (patch : I → Set V) (A : I → Finset J)
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p = t} = d.spherePatch (patch i) (A i))
    (hlevel : ∀ j, d.level j = t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v ≠ t)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) : AdmissibleStep ρ R T P := by
  let S := d.refineFamily T
  have hfiner (x : X) : Refines (S.val x).complex (T.val x).complex :=
    d.refine_refines (T.val x)
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) := by
    exact (S.val x).preserves_marked (hpatch i)
  let W : Set V := ⋃ i, d.spherePatch (patch i) (A i)
  have hW (x : X) : IsMarked (S.val x).complex W :=
    IsMarked.iUnion fun i => d.spherePatch_marked (hpatch' x i) (A i)
  have hspace (x : X) : (T.val x).complex.space = K.space := (T.val x).space_eq
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← hspace x]
    exact (P.marked x).subset_space
  have hP' (x : X) : IsMarked (S.val x).complex (P.val x) :=
    (hfiner x).preserves_marked (P.marked x)
  let Z : MarkedFamily S := MarkedFamily.ofSets S (fun x => P.val x ∩ W)
    (fun x => (hP' x).inter (hW x)) (by
      intro s hs
      have hh := (P.set_localConstancy s hs).comp (fun Q => Q ∩ W)
      convert hh using 1
      ext x p
      simp only [Function.comp_apply,Set.mem_inter_iff]
      tauto)
  refine { next := S
           finer := hfiner
           oldMarked := hP'
           zero := Z
           subset := fun _ => Set.inter_subset_left
           dimensionDrop := ?_
           diameter := ?_ }
  · intro x F hF hFP E hE hEF
    apply d.spherePatches_dimensionDrop (hpatch' x) A t hlevel (hgeneric x) (P.val x)
      F hF hFP E hE
    exact fun p hp => ⟨(hEF hp).1,(hEF hp).2.2⟩
  · intro x
    have he : P.val x ∩ W = P.val x ∩ ⋃ i, {p | f i p = t} := by
      ext p
      simp only [W,Set.mem_inter_iff,Set.mem_iUnion]
      constructor
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,((hsphere i).symm ▸ hi).2⟩
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,(hsphere i) ▸ ⟨hP x hp,hi⟩⟩
    change ComponentDiameter ρ (P.val x \ (P.val x ∩ W)) (2*R)
    rw [he]
    exact sphereUnion_componentDiameter ρ (P.val x) (hP x) f t R hcont hcover htriangle ht

end UniversalCuts

end BassTrace.Sparse.Cuts

end

end OAI

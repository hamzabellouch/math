import OAI.RingTheory.BassTrace.TreeArea

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Cuts

open Set Finset MeasureTheory

open scoped ENNReal

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

variable {T : SubdivisionFamily X K} (P : MarkedFamily T)

lemma MarkedFamily.trace_space (s : Finset V) (hs : s ∈ K.faces) (x : X) :
    (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space = P.val x ∩ convexHull ℝ (s : Set V) := by
  rw [restrictComplex_space_of_respects, (P.marked x).restriction_space]
  intro t ht
  exact (T.val x).respects s hs t ht.1

lemma MarkedFamily.localConstancy_inter (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) :
    IsLocallyConstant (fun x => P.val x ∩ W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(P.localConstancy s hs).eventually_eq x] with y hy
  have he : P.val y ∩ convexHull ℝ (s : Set V) = P.val x ∩ convexHull ℝ (s : Set V) := by
    rw [← P.trace_space s hs y, ← P.trace_space s hs x]
    congr 1
    exact Geometry.SimplicialComplex.ext hy
  have he' := congrArg (fun Q : Set V => Q ∩ W) he
  simpa only [Set.inter_assoc,Set.inter_eq_self_of_subset_right hW] using he'

def MarkedFamily.localArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (W : Set V) (j : ℕ) (x : X) : ℝ≥0∞ :=
  simplexArea Γ j (η '' (P.val x ∩ W))

lemma MarkedFamily.localArea_locallyConstant {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) :
    IsLocallyConstant (P.localArea Γ η W j) :=
  (P.localConstancy_inter s hs W hW).comp (fun Q => simplexArea Γ j (η '' Q))

lemma MarkedFamily.localArea_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (hη : ∀ p ∈ convexHull ℝ (s : Set V), ∑ i, η p i=1)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (T.val x).complex.faces,
      convexHull ℝ (t : Set V) ⊆ P.val x → t.card ≤ j+1) :
    P.localArea Γ η W j x < ∞ := by
  classical
  let L := restrictComplex (geometricRestriction (T.val x).complex (P.val x))
    (convexHull ℝ (s : Set V))
  have hf : L.faces.Finite := ((T.val x).finite s hs).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let A := F.image (fun t => t.image η)
  have hA : ∀ t ∈ A, ∀ p ∈ t, ∑ i,p i=1 := by
    rintro t ht p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact hη v (hl.2 hv)
  have hcard : ∀ t ∈ A, t.card ≤ j+1 := by
    rintro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact (Finset.card_image_le).trans (hd u hl.1.1 hl.1.2)
  apply simplexArea_polyhedral_lt_top Γ hΓ A hA hcard
  rintro _ ⟨p,hp,rfl⟩
  have hpL : p ∈ L.space := by
    change p ∈ (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space
    rw [P.trace_space s hs x]
    exact ⟨hp.1,hW hp.2⟩
  obtain ⟨u,hu,hpu⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
  apply Set.mem_iUnion₂.mpr
  refine ⟨u.image η,Finset.mem_image.mpr ⟨u,hf.mem_toFinset.mpr hu,rfl⟩,?_⟩
  rw [Finset.coe_image]
  change η.toAffineMap p ∈ convexHull ℝ (η.toAffineMap '' (u : Set V))
  rw [← η.toAffineMap.image_convexHull]
  exact ⟨p,hpu,rfl⟩

end Sparse.Cuts

namespace Sparse

section

open Set MeasureTheory

open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
lemma IsLocallyConstant.lintegral_lt_top {f : X → ℝ≥0∞} (hf : IsLocallyConstant f)
    (hfin : ∀ x, f x < ∞) (μ : Measure X) [IsFiniteMeasure μ] :
    ∫⁻ x, f x ∂μ < ∞ := by
  classical
  let F := hf.range_finite.toFinset
  have hb (x : X) : f x ≤ ∑ t ∈ F,t :=
    show f x ≤ ∑ t ∈ hf.range_finite.toFinset, (fun t : ℝ≥0∞ => t) t from
      Finset.single_le_sum (f := fun t : ℝ≥0∞ => t) (fun _ _ => bot_le)
        (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self x))
  apply lt_of_le_of_lt (lintegral_mono hb)
  rw [lintegral_const]
  apply ENNReal.mul_lt_top
  · apply ENNReal.sum_lt_top.mpr
    intro t ht
    obtain ⟨x,rfl⟩ := hf.range_finite.mem_toFinset.mp ht
    exact hfin x
  · exact measure_lt_top μ _

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

def simplexEnumeration {n : ℕ} (s : Finset Y) (hs : s.card=n+1) : Fin (n+1) ≃ s :=
  (Finset.equivFinOfCardEq hs).symm

def simplexVertices (s : Finset Y) : Finset (Y →₀ ℝ) :=
  s.image (fun y => Finsupp.single y (1 : ℝ))

def simplexCoordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Y →₀ ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
  LinearMap.pi (fun i => Finsupp.lapply (simplexEnumeration s hs i).val)

lemma simplexCoordinates_sum {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p ∈ convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    ∑ i, simplexCoordinates s hs p i = 1 := by
  have hprob : p ∈ probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  calc
    (∑ i, simplexCoordinates s hs p i) = ∑ y : s,p y :=
      (simplexEnumeration s hs).sum_comp (fun y : s => p y)
    _ = ∑ y ∈ s,p y := Finset.sum_attach s (fun y => p y)
    _ = 1 := (sum_coeff_of_support_subset s p hprob.2.2).trans hprob.2.1

def simplexGraph {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1) :
    SimpleGraph (Fin (n+1)) := Γ.comap (fun i => (simplexEnumeration s hs i).val)

omit [DecidableEq Y] in
lemma simplexGraph_connected {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1)
    (hΓ : (Γ.induce (s : Set Y)).Connected) : (simplexGraph Γ s hs).Connected := by
  let e : simplexGraph Γ s hs ≃g Γ.induce (s : Set Y) := {
    toEquiv := simplexEnumeration s hs
    map_rel_iff' := by intro a b; rfl }
  exact e.connected_iff.mpr hΓ

def SourceTop (K : PreAbstractSimplicialComplex Y) (n : ℕ) :=
  {s : Finset Y // s ∈ K.faces ∧ s.card=n+1}

instance (K : PreAbstractSimplicialComplex Y) (n : ℕ) : DecidableEq (SourceTop K n) :=
  inferInstanceAs (DecidableEq {s : Finset Y // s ∈ K.faces ∧ s.card=n+1})

def sourceInterior (s : Finset Y) : Set (Y →₀ ℝ) :=
  intrinsicInterior ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))

def originalArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : X → ℝ≥0∞ :=
  Q.P.localArea (simplexGraph Γ σ.val σ.property.2) (simplexCoordinates σ.val σ.property.2)
    (sourceInterior σ.val) j

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_locallyConstant {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : IsLocallyConstant (originalArea Γ Q σ j) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ intrinsicInterior_subset j

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (hΓ : (Γ.induce (σ.val : Set Y)).Connected) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    originalArea Γ Q σ j x < ∞ :=
  Q.P.localArea_lt_top _ (simplexGraph_connected Γ σ.val σ.property.2 hΓ) _
    (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    (fun _ hp => simplexCoordinates_sum σ.val σ.property.2 hp)
    _ intrinsicInterior_subset j x hd

lemma sourceTop_stabilizer_finite {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ.val) := by
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  apply Subtype.ext
  exact IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he)

def normalizedArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) (reps : Finset (SourceTop K n))
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) : ℝ≥0∞ :=
  ∑ σ ∈ reps, (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
    ∫⁻ x, originalArea Γ Q σ j x ∂μ

omit [BorelSpace X] in
lemma normalizedArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (hd : ∀ x t, t ∈ (Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    normalizedArea Γ μ reps Q j < ∞ := by
  apply ENNReal.sum_lt_top.mpr
  intro σ hσ
  apply ENNReal.mul_lt_top
  · let := sourceTop_stabilizer_finite (H := H) σ
    apply ENNReal.inv_lt_top.mpr
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer H σ.val))
  · exact IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
      (fun x => originalArea_lt_top Γ Q σ (hΓ σ hσ) j x (hd x)) μ

omit [BorelSpace X] in
lemma normalizedArea_filtration_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces,s.card ≤ n+1) {j : ℕ} (hj : j ≤ n) :
    normalizedArea Γ μ reps (Q.pair j) j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  apply (Q.point x).dimension_bound _ hj ht htp
  rintro _ ⟨s,hs,rfl⟩
  exact Finset.card_image_le.trans (hK s hs)

end

lemma exists_nearMinimizer {A : Type*} [Nonempty A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) {ε : ℝ} (hε : 0<ε) :
    ∃ a, ∀ b, f a ≤ f b+ε := by
  have hb : BddBelow (Set.range f) := ⟨0,by rintro _ ⟨a,rfl⟩; exact hf a⟩
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f)
    (lt_add_of_pos_right (sInf (Set.range f)) hε)
  refine ⟨a,fun b => ?_⟩
  exact ha.le.trans (by simpa only [add_comm] using add_le_add_right (csInf_le hb (Set.mem_range_self b)) ε)

end Sparse

end BassTrace

end

end OAI

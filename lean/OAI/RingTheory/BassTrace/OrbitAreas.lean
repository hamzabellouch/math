import OAI.RingTheory.BassTrace.SimplexMeasures

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

lemma finsuppRelabel_single (e : Y ≃ Z) (y : Y) :
    Finsupp.domLCongr (R := ℝ) e (Finsupp.single y (1 : ℝ)) = Finsupp.single (e y) 1 := by
  ext z
  change (Finsupp.single y (1 : ℝ)) (e.symm z) = (Finsupp.single (e y) 1) z
  simp only [Finsupp.single_apply]
  have hh : y=e.symm z ↔ e y=z := ⟨fun h => by rw [h,Equiv.apply_symm_apply],
    fun h => by rw [←h,Equiv.symm_apply_apply]⟩
  simp [hh]

lemma simplexVertices_relabel (e : Y ≃ Z) (s : Finset Y) :
    (simplexVertices (s.map e.toEmbedding) : Set (Z →₀ ℝ)) =
      Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ)) := by
  simp only [simplexVertices,Finset.coe_image,Finset.coe_map,Set.image_image]
  congr 1
  funext y
  exact (finsuppRelabel_single e y).symm

lemma sourceInterior_relabel (e : Y ≃ Z) (s : Finset Y) :
    sourceInterior (s.map e.toEmbedding) = Finsupp.domLCongr (R := ℝ) e '' sourceInterior s := by
  unfold sourceInterior
  rw [simplexVertices_relabel]
  have hh : convexHull ℝ (Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ))) =
      (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry ''
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) :=
    ((Finsupp.domLCongr (R := ℝ) e).toLinearMap.image_convexHull _).symm
  rw [hh]
  exact (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry.intrinsicInterior_image _

def simplexPermutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1) :
    Equiv.Perm (Fin (n+1)) :=
  ((simplexEnumeration s hs).trans (Finset.equivMap e.toEmbedding s)).trans
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)).symm

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexEnumeration_permutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (i : Fin (n+1)) :
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)
      (simplexPermutation e s hs i)).val = e (simplexEnumeration s hs i).val := by
  simp [simplexPermutation]

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexCoordinates_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (p : Y →₀ ℝ) :
    simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) (Finsupp.domLCongr (R := ℝ) e p) =
      relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p) := by
  ext j
  obtain ⟨i,rfl⟩ := (simplexPermutation e s hs).surjective j
  change p (e.symm (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs i)).val) =
    p (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs i))).val
  rw [simplexEnumeration_permutation,Equiv.symm_apply_apply,Equiv.symm_apply_apply]

omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexGraph_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) :
    simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs) =
      (simplexPermutation e s hs).simpleGraph (simplexGraph Γ s hs) := by
  ext a b
  obtain ⟨u,rfl⟩ := (simplexPermutation e s hs).surjective a
  obtain ⟨v,rfl⟩ := (simplexPermutation e s hs).surjective b
  change Δ.Adj (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs u)).val
    (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs v)).val ↔
    Γ.Adj (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs u))).val
      (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs v))).val
  rw [simplexEnumeration_permutation,simplexEnumeration_permutation,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact he _ _

omit [DecidableEq Z] in
lemma originalSimplexArea_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : Q⊆convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexArea (simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs)) j
      (simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) '' (Finsupp.domLCongr (R := ℝ) e '' Q)) =
      simplexArea (simplexGraph Γ s hs) j (simplexCoordinates s hs '' Q) := by
  rw [simplexGraph_relabel e s hs Γ Δ he,Set.image_image]
  have hi : (fun p => simplexCoordinates (s.map e.toEmbedding) (by simpa using hs)
      (Finsupp.domLCongr (R := ℝ) e p)) =
      (fun p => relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p)) :=
    funext (simplexCoordinates_relabel e s hs)
  rw [hi,← Set.image_image]
  apply simplexArea_relabel
  rintro _ ⟨p,hp,rfl⟩
  exact simplexCoordinates_sum s hs (hQ hp)

end

open Finset Set

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

lemma smul_finset_eq_map (h : H) (s : Finset Y) :
    h • s=s.map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [Finset.mem_smul_finset,Finset.mem_map]
  rfl

abbrev sourceTopAction : MulAction H (SourceTop K n) where
  smul h σ := ⟨h • σ.val,by rw [smul_finset_eq_map]; exact hact h σ.val σ.property.1,
    by simpa only [Finset.card_smul_finset] using σ.property.2⟩
  one_smul σ := Subtype.ext (one_smul H σ.val)
  mul_smul h k σ := Subtype.ext (mul_smul h k σ.val)

lemma sourceTop_stabilizer_eq (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    MulAction.stabilizer H σ=MulAction.stabilizer H σ.val := by
  let := sourceTopAction K n hact
  ext h
  change (h • σ=σ) ↔ h • σ.val=σ.val
  exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩

lemma finite_sourceTop_stabilizer [IsCancelSMul H Y] (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    Finite (MulAction.stabilizer H σ) := by
  let := sourceTopAction K n hact
  rw [sourceTop_stabilizer_eq K n hact]
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  exact Subtype.ext (IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he))

end Sparse

namespace Sparse.OrbitAreas

section

open scoped BigOperators Pointwise ENNReal

variable {H T : Type*} [Group H] [MulAction H T]

def representative (a : T) (b : MulAction.orbit H a) : H := b.property.choose

@[simp] lemma representative_smul (a : T) (b : MulAction.orbit H a) :
    representative a b • a = b.val := b.property.choose_spec

def orbitTimesStabilizer (a : T) : MulAction.orbit H a × MulAction.stabilizer H a ≃ H where
  toFun p := representative a p.1 * p.2.val
  invFun h := (⟨h • a,⟨h,rfl⟩⟩,⟨(representative a ⟨h • a,⟨h,rfl⟩⟩)⁻¹*h,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (eq_inv_smul_iff.mpr (representative_smul a ⟨h • a,⟨h,rfl⟩⟩)).symm⟩)
  left_inv p := by
    have he : (representative a p.1 * p.2.val) • a = p.1.val := by
      rw [mul_smul, p.2.property,representative_smul]
    apply Prod.ext
    · exact Subtype.ext he
    · apply Subtype.ext
      dsimp
      have hb : (⟨(representative a p.1 * p.2.val) • a,
          ⟨representative a p.1 * p.2.val,rfl⟩⟩ : MulAction.orbit H a) = p.1 := Subtype.ext he
      rw [hb,inv_mul_cancel_left]
  right_inv h := by simp

@[simp] lemma orbitTimesStabilizer_smul (a : T)
    (p : MulAction.orbit H a × MulAction.stabilizer H a) :
    orbitTimesStabilizer a p • a = p.1.val := by
  change (representative a p.1 * p.2.val) • a = _
  rw [mul_smul,p.2.property,representative_smul]

lemma sum_orbit_multiplicity (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (∑' h : H, f (h • a)) =
      (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞) *
        ∑' b : MulAction.orbit H a, f b.val := by
  let := Fintype.ofFinite (MulAction.stabilizer H a)
  rw [← (orbitTimesStabilizer (H := H) a).tsum_eq (fun h => f (h • a))]
  simp only [orbitTimesStabilizer_smul]
  rw [ENNReal.tsum_prod (f := fun (b : MulAction.orbit H a) (_ : MulAction.stabilizer H a) => f b.val)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left,Nat.card_eq_fintype_card]

lemma normalized_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  rw [sum_orbit_multiplicity,← mul_assoc]
  have hn : Nat.card (MulAction.stabilizer H a) ≠ 0 := Nat.card_pos.ne'
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn) (by simp),one_mul]

lemma normalized_inverse_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h⁻¹ • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  have he : (∑' h : H, f (h⁻¹ • a)) = ∑' h : H, f (h • a) :=
    (Equiv.inv H).tsum_eq (fun h => f (h • a))
  rw [he]
  exact normalized_orbit_sum a f

lemma normalized_all_orbits (f : T → ℝ≥0∞)
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H, f (h⁻¹ • o.out)) = ∑' a : T, f a := by
  simp only [normalized_inverse_orbit_sum]
  rw [← ENNReal.tsum_sigma]
  exact (MulAction.selfEquivSigmaOrbits H T).symm.tsum_eq f

lemma finite_finset_stabilizer {Y : Type*} [MulAction H Y] [IsCancelSMul H Y]
    [DecidableEq Y] (s : Finset Y) (hs : s.Nonempty) :
    Finite (MulAction.stabilizer H s) := by
  obtain ⟨v,hv⟩ := hs
  let f : MulAction.stabilizer H s → s := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  apply Subtype.ext
  exact IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he)

end

section

open MeasureTheory Set

open scoped ENNReal

variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]

def orbitActivated (B : Set X) (f : T → X → ℝ≥0∞) (a : T) (h : H) (x : X) : ℝ≥0∞ :=
  B.indicator (f (h⁻¹ • a)) (h⁻¹ • x)

omit [Countable H] [Countable T] in
lemma measurable_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    Measurable (orbitActivated B f a h) :=
  ((hf (h⁻¹ • a)).indicator hB).comp (hμ h⁻¹).measurable

omit [Countable H] [Countable T] in
lemma integral_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    (∫⁻ x,orbitActivated B f a h x ∂μ) = ∫⁻ x in B,f (h⁻¹ • a) x ∂μ := by
  unfold orbitActivated
  rw [(hμ h⁻¹).lintegral_comp ((hf _).indicator hB), lintegral_indicator hB]

lemma normalized_activated_integral (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a))
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,orbitActivated B f o.out h x ∂μ) =
      ∫⁻ x in B,∑' a : T,f a x ∂μ := by
  calc
    _ = ∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H,∫⁻ x in B,f (h⁻¹ • o.out) x ∂μ := by
          apply tsum_congr
          intro o
          congr 1
          rw [lintegral_tsum (fun h => (measurable_orbitActivated μ hμ B hB f hf o.out h).aemeasurable)]
          exact tsum_congr (fun h => integral_orbitActivated μ hμ B hB f hf o.out h)
    _ = ∑' a : T,∫⁻ x in B,f a x ∂μ := normalized_all_orbits (fun a => ∫⁻ x in B,f a x ∂μ)
    _ = _ := (lintegral_tsum (fun a => (hf a).aemeasurable)).symm

end

open Set Finset MeasureTheory

open scoped Pointwise ENNReal Classical

variable {H T : Type*} [Group H] [MulAction H T]

lemma finite_orbit_quotient (F : Finset T)
    (hF : ∀ a : T, ∃ b∈F, ∃ h : H,h • b=a) :
    Finite (MulAction.orbitRel.Quotient H T) := by
  let f : F → MulAction.orbitRel.Quotient H T := fun b => Quotient.mk'' b.val
  apply Finite.of_surjective f
  intro o
  obtain ⟨b,hb,h,he⟩ := hF o.out
  refine ⟨⟨b,hb⟩,?_⟩
  change Quotient.mk'' b=o
  rw [←Quotient.out_eq o]
  apply Quotient.sound
  exact ⟨h⁻¹,(eq_inv_smul_iff.mpr he).symm⟩

variable [Finite (MulAction.orbitRel.Quotient H T)]

def orbitReps : Finset T :=
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  (Finset.univ : Finset (MulAction.orbitRel.Quotient H T)).image Quotient.out

lemma sum_orbitReps (f : T → ℝ≥0∞) :
    (∑ a∈orbitReps (H := H) (T := T), f a) =
      ∑' o : MulAction.orbitRel.Quotient H T,f o.out := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  rw [tsum_fintype]
  exact Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)

lemma orbitReps_complete (a : T) :
    ∃ b∈orbitReps (H := H) (T := T), ∃ h : H,h • b=a := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  let o : MulAction.orbitRel.Quotient H T := Quotient.mk'' a
  refine ⟨o.out,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨o,Finset.mem_univ _,rfl⟩
  · have hh : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H T)=Quotient.mk'' a :=
      Quotient.out_eq o
    obtain ⟨h,he⟩ := Quotient.exact hh
    exact ⟨h⁻¹,(eq_inv_smul_iff.mpr he).symm⟩

end Sparse.OrbitAreas

end BassTrace

end

end OAI

import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedBlockBoundary
import OAI.Topology.ArtinGroups.Harmonic.NullPatch2

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [LinearOrder S] in
def RelativeNullData (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit) : Prop :=
  sourcePositiveComponent M (p q) i ⊆ U ∧
  (∀ j ∈ sourcePositiveComponent M (p q) i, (framedCartan M *ᵥ p q) j=0) ∧
  ∀ j ∈ sourceClosedRegion M (sourcePositiveComponent M (p q) i), ∀ d, q<d → p d j=0

omit [LinearOrder S] in
lemma relativeNullData_of_positive (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit)
    (hp:0<p q i) (h:relativePositiveSign (framedCartan M) U p q i) : RelativeNullData M U p q i := by
  obtain ⟨hU,hr,hh⟩ := (relativePositiveSign_component_iff M U p q i hp).mp h
  refine ⟨hU,hr,?_⟩
  intro j hj d hd
  apply hh d hd j
  rcases hj with hj|⟨a,ha,hja⟩
  · exact Or.inl hj
  · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩

omit [LinearOrder S] in
lemma relativePositive_of_nullData (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit)
    (hp:0<p q i) (h:RelativeNullData M U p q i) : relativePositiveSign (framedCartan M) U p q i := by
  apply (relativePositiveSign_component_iff M U p q i hp).mpr
  refine ⟨h.1,h.2.1,?_⟩
  intro d hd j hj
  apply h.2.2 j _ d hd
  rcases hj with hj|⟨a,ha,haj⟩
  · exact Or.inl hj
  · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩

lemma pointedPositiveComponent_type_neighbor (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (j:S⊕Unit)
    (hj:j∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) (k:S) (hk:k∈P.val.1)
    (hjk:framedCartan M j (.inl k)<0) :
    (.inl k:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i := by
  have hp:=sourcePositiveComponent_positive M _ i hi j hj
  have hkp:=pointedProfile_positive_neighbor M f cutoff P q k hk j (by rwa [framedCartan_symm]) hp
  exact hj.tail ⟨hp,hjk,hkp⟩

lemma pointedPositiveBlock_commutes (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (j k:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i)
    (hk:k∈P.val.1) (hkI:(.inl k:S⊕Unit)∉sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    M j k=2 := by
  by_contra hn
  exact hkI (pointedPositiveComponent_type_neighbor M f cutoff P q i hi (.inl j) hjI k hk
    (framedCartan_neg_of_label_ne_two M j k (by rintro rfl;exact hkI hjI) hn))

lemma relativeNullSign_image (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) :
    Sum.inl '' {j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}=
      sourcePositiveComponent M (pointedProfile M f P cutoff q) i := by
  ext v
  constructor
  · rintro ⟨j,hj,rfl⟩;exact hj
  · intro hv
    rcases v with j|u
    · exact ⟨j,hv,rfl⟩
    · obtain ⟨a,ha⟩ := hU (hn.1 hv)
      cases ha

lemma relativeNullSign_peak (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (j:S) (_hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    relativePeak M f cutoff P j=q := by
  apply le_antisymm
  · by_contra h
    have hh:q<relativePeak M f cutoff P j:=lt_of_not_ge h
    have hz:=hn.2.2 (.inl j) (Or.inl hjI) (relativePeak M f cutoff P j) hh
    exact (ne_of_gt (relativePeak_positive M f cutoff P j ⟨q, sourcePositiveComponent_positive M _ i hi _ hjI⟩)) hz
  · exact relativePeak_bound M f cutoff P j q (ne_of_gt (sourcePositiveComponent_positive M _ i hi _ hjI))

lemma relativeNullSign_sign (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    relativeSign M U (pointedProfile M f P cutoff) q v=1 := by
  have he:=sourcePositiveComponent_eq M (pointedProfile M f P cutoff q) v
    (sourcePositiveComponent M (pointedProfile M f P cutoff q) i)
    (sourcePositiveComponent_spec M _ i hi) hv
  have hnv:RelativeNullData M U (pointedProfile M f P cutoff) q v := by
    unfold RelativeNullData
    rw [he]
    exact hn
  have hsign := relativePositive_of_nullData M U _ q v
    (sourcePositiveComponent_positive M _ i hi v hv) hnv
  simp only [relativeSign, ne_of_gt (sourcePositiveComponent_positive M _ i hi v hv),
    hsign, ↓reduceIte]

noncomputable def relativeNullPatch (P:Deligne M) (q:ℕ) (i:S⊕Unit) (v:S⊕Unit) : ℝ :=
  if v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i then pointedProfile M f P cutoff q v else 0

lemma relativeNullPatch_nonneg (P:Deligne M) (q:ℕ) (i v:S⊕Unit) : 0 ≤ relativeNullPatch M f cutoff P q i v := by
  unfold relativeNullPatch
  split_ifs
  · exact pointedCosetVector_nonneg M f P (cutoff+q) v
  · rfl

lemma relativeNullPatch_row (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i) :
    (framedCartan M *ᵥ relativeNullPatch M f cutoff P q i) v=0 := by
  trans (framedCartan M *ᵥ pointedProfile M f P cutoff q) v
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu:u∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i
    · simp only [relativeNullPatch,ite_eq_left hu]
    · simp only [relativeNullPatch,ite_eq_right hu,MulZeroClass.mul_zero]
      by_cases hh:framedCartan M v u<0
      · rw [sourcePositiveComponent_boundary_zero M (pointedProfile M f P cutoff q)
          (fun v => pointedCosetVector_nonneg M f P (cutoff+q) v) i hi u hu
          ⟨v,hv,by rwa [framedCartan_symm]⟩,MulZeroClass.mul_zero]
      · have he:framedCartan M v u=0:=le_antisymm (framedCartan_off M v u
          (by rintro rfl;exact hu hv)) (le_of_not_gt hh)
        rw [he,MulZeroClass.zero_mul]
  · exact hn.2.1 v hv

lemma relativePositive_exterior (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (sourcePositiveComponent M (pointedProfile M f P cutoff q) i))
    (ho:v∉Sum.inl '' (P.val.1∩{j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i})) :
    v∉Sum.inl '' P.val.1 := by
  rintro ⟨j,hj,rfl⟩
  apply ho
  refine ⟨j,⟨hj,?_⟩,rfl⟩
  rcases hv with hv|⟨u,hu,huj⟩
  · exact hv
  · exact pointedPositiveComponent_type_neighbor M f cutoff P q i hi u hu j hj (by rwa [framedCartan_symm])

lemma relativePositive_block_cap (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}
    ∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' (P.val.1∩I))) (cutoff+q) := by
  intro I H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have hv:=sourceNeighborhood_project M (Sum.inl '' I) hα.1
  rw [relativeNullSign_image M f U cutoff P q i hn hU] at hv
  have hout:=relativePositive_exterior M f cutoff P q i hi α.1 hv hα.2
  have hk0:0≤k-cutoff:=by omega
  have he:cutoff+((k-cutoff).toNat:ℤ)=k:=by rw [Int.toNat_of_nonneg hk0];omega
  have hz:=hn.2.2 α.1 hv (k-cutoff).toNat (by omega)
  change pointedCosetVector M f P (cutoff+(k-cutoff).toNat) α.1=0 at hz
  rw [he,pointedCosetVector_open_at M f P x hx α.1 hout k] at hz
  exact (pointedMultiplicity_zero_iff M f x k α.1).mp hz H α.2

lemma relativePositive_block_values (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<pointedProfile M f P cutoff q i)
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q i)
    (hU : U ⊆ Set.range (Sum.inl:S→S⊕Unit)) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) i}
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' (P.val.1∩I)) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      pointedMultiplicity M f x (cutoff+q) v=relativeNullPatch M f cutoff P q i v := by
  intro I v hv
  have hI:Sum.inl '' I=sourcePositiveComponent M (pointedProfile M f P cutoff q) i:=relativeNullSign_image M f U cutoff P q i hn hU
  rw [hI] at hv
  rcases hv with ⟨hv,ho⟩|⟨ho,hv⟩
  · rw [←pointedCosetVector_open_at M f P x hx v (relativePositive_exterior M f cutoff P q i hi v (Or.inl hv) ho) (cutoff+q)]
    simp only [relativeNullPatch,ite_eq_left hv]
    rfl
  · have hoB:v∉Sum.inl '' (P.val.1∩I):=by
      intro h
      exact ho (hI ▸ Set.image_mono Set.inter_subset_right h)
    rw [←pointedCosetVector_open_at M f P x hx v (relativePositive_exterior M f cutoff P q i hi v (Or.inr hv) hoB) (cutoff+q)]
    rw [relativeNullPatch,ite_eq_right ho]
    exact sourcePositiveComponent_boundary_zero M _ (pointedCosetVector_nonneg M f P (cutoff+q)) i hi v ho hv


end HarmonicArtin.ParabolicIntersections

end OAI

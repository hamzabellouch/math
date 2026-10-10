import Mathlib
import OAI.Topology.ArtinGroups.Quivers.LinearMatrix
import OAI.Topology.ArtinGroups.Complexes.HomSpaceDuality

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def homStep (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    homSpace Q E F n v →ₗ[K] homSpace Q E F m v :=
  (homDifferential Q E F n).restrict fun _ hf =>
    hm ▸ homDifferential_mem Q E F n v hf

omit [Fintype V] [DecidableEq A] in
lemma homStep_range (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    (LinearMap.range (homStep Q E F n m v hm)).map (homSpace Q E F m v).subtype =
      homBoundaries Q E F m v := by
  subst m
  ext f
  change (∃ g, (∃ h, homStep Q E F n (n+1) v rfl h = g) ∧ g.val = f) ↔ _
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    change ∃ g, g ∈ homSpace Q E F (n+1-1) v ∧
      homDifferential Q E F (n+1-1) g = homDifferential Q E F n h.val
    simpa only [add_sub_cancel_right] using
      (show ∃ g, g ∈ homSpace Q E F n v ∧ homDifferential Q E F n g =
        homDifferential Q E F n h.val from ⟨h.val, h.property, rfl⟩)
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ homSpace Q E F n v := by
      change g ∈ homSpace Q E F (n+1-1) v at hg
      rwa [add_sub_cancel_right] at hg
    refine ⟨homStep Q E F n (n+1) v rfl ⟨g, hg'⟩, ⟨⟨g, hg'⟩, rfl⟩, ?_⟩
    dsimp only [homStep, LinearMap.restrict_apply]
    simp only [add_sub_cancel_right]

omit [Fintype V] [DecidableEq A] in
lemma homStep_range_finrank (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (LinearMap.range (homStep Q E F n m v hm)) =
      Module.finrank K (homBoundaries Q E F m v) := by
  rw [← homStep_range Q E F n m v hm, Submodule.finrank_map_subtype_eq]

noncomputable def homCycleKernelEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    homCycles Q E F n v ≃ₗ[K] LinearMap.ker (homStep Q E F n m v hm) where
  toFun f := ⟨⟨f.val, f.property.1⟩, Subtype.ext f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, congrArg Subtype.val f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq A] in

lemma hom_exact_dimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v + Module.finrank K (homBoundaries Q E F n v) +
      Module.finrank K (homBoundaries Q E F (n+1) v) =
      Module.finrank K (homSpace Q E F n v) := by
  have hq := ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype).finrank_quotient_add_finrank
  have hc := (Submodule.comapSubtypeEquivOfLe (homBoundaries_le_homCycles Q E F n v)).finrank_eq
  have hk := (homCycleKernelEquiv Q E F n (n+1) v rfl).finrank_eq
  have hr := homStep_range_finrank Q E F n (n+1) v rfl
  have he := (homStep Q E F n (n+1) v rfl).finrank_range_add_finrank_ker
  change homDimension Q E F n v + _ = _ at hq
  omega

lemma homStep_rank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n m v : ℤ) (hm : m = n+1) :
    Module.finrank K (homBoundaries Q E F m v) =
      Module.finrank K (homBoundaries Q F E (-n) (2-v)) := by
  have hneg : -n = -m+1 := by omega
  let d := homStep Q E F n m v hm
  let d' := homStep Q F E (-m) (-n) (2-v) hneg
  let e₀ := homSpaceDuality Q E F m v
  let e₁ := (homSpaceDuality Q E F n v).trans
    (LinearEquiv.smulOfNeZero K (Module.Dual K (homSpace Q E F n v))
      (cochainSign (K := K) m) (cochainSign_ne_zero m))
  have ha : e₁.toLinearMap.comp d' = d.dualMap.comp e₀.toLinearMap := by
    ext g f
    change cochainSign (K := K) m *
      supertrace Q E (f.val * homDifferential Q F E (-m) g.val) =
      supertrace Q E (homDifferential Q E F n f.val * g.val)
    have hh := homDifferential_adjoint Q E F m f.val g.val
    have he : m-1=n := by omega
    rw [he] at hh
    exact hh.symm
  have hr := congrArg (fun l : homSpace Q F E (-m) (2-v) →ₗ[K] Module.Dual K (homSpace Q E F n v) =>
    Module.finrank K (LinearMap.range l)) ha
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top] at hr
  rw [e₁.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range] at hr
  rw [homStep_range_finrank Q F E (-m) (-n) (2-v) hneg,
    homStep_range_finrank Q E F n m v hm] at hr
  exact hr.symm

lemma homDimension_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v = homDimension Q F E (-n) (2-v) := by
  have he := hom_exact_dimension Q E F n v
  have hf := hom_exact_dimension Q F E (-n) (2-v)
  have hs := homSpace_finrank_dual Q E F n v
  have h₁ := homStep_rank_dual Q E F (n-1) n v (by omega)
  have h₂ := homStep_rank_dual Q E F n (n+1) v rfl
  have hh : -(n-1) = -n+1 := by omega
  rw [hh] at h₁
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI

import Mathlib
import OAI.RingTheory.Multiplicity.FiniteModuleCech
import OAI.RingTheory.Multiplicity.RootSectionBase

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (m : Fin n → ℤ)

abbrev CechSection (s : Finset (Fin (n+1))) :=
  (hs : PLift s.Nonempty) → Sections R n s hs.down m
abbrev cechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R :=
  ModuleCat.of R (CechSection R n m s)

def cechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) : cechObj R n m s ⟶ cechObj R n m t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then sectionsRestrictionBase R n hs ht.down m hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs <;> simp only [Pi.add_apply,map_add,add_zero]
    map_smul' r x := by
      funext ht
      split_ifs <;> simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_zero] }

lemma cechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : CechSection R n m s) :
    (cechRes R n m hst).hom x ⟨ht⟩ = sectionsRestrictionBase R n hs ht m hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _) = _
  rw [dite_eq_left hs]

lemma cechRes_self (s : Finset (Fin (n+1))) :
    cechRes R n m (Finset.Subset.refl s) = 𝟙 (cechObj R n m s) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (cechRes_apply R n m _ hs.down hs.down x).trans (sectionsRestrictionBase_self R n hs.down m (x hs))

lemma cechRes_comp {s t v : Finset (Fin (n+1))} (hst : s ⊆ t) (htv : t ⊆ v) :
    cechRes R n m hst ≫ cechRes R n m htv = cechRes R n m (hst.trans htv) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hv
  obtain ⟨hv⟩ := hv
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono hst
    change (cechRes R n m htv).hom ((cechRes R n m hst).hom x) ⟨hv⟩ = _
    rw [cechRes_apply R n m htv ht hv,cechRes_apply R n m hst hs ht,
      cechRes_apply R n m (hst.trans htv) hs hv]
    exact sectionsRestrictionBase_comp R n hs ht hv m hst htv (x ⟨hs⟩)
  · change (if ht : t.Nonempty then
      sectionsRestrictionBase R n ht hv m htv (if hs : s.Nonempty then _ else 0) else 0) =
        if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    split_ifs <;> simp only [map_zero]

def cechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := cechObj R n m
  res := cechRes R n m
  res_self := cechRes_self R n m
  res_comp := cechRes_comp R n m

abbrev zeroAugGrid (s : Finset (Fin (n+1))) :=
  AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun s => grid R n m s ∅) s

def gridCechEquiv (s : Finset (Fin (n+1))) :
    zeroAugGrid R n m s ≃ₗ[R] CechSection R n m s where
  toFun x hs := ⟨x.val,by
    change x.val ∈ grid R n m s ∅
    simpa only [zeroAugGrid,AlternatingCech.zeroAugmentation,
      ite_eq_right (Finset.nonempty_iff_ne_empty.mp hs.down)] using x.property⟩
  invFun x := if hs : s.Nonempty then ⟨(x ⟨hs⟩).val,by
    have hx : (x ⟨hs⟩).val ∈ grid R n m s ∅ := (x ⟨hs⟩).property
    simpa only [zeroAugGrid,AlternatingCech.zeroAugmentation,
      ite_eq_right (Finset.nonempty_iff_ne_empty.mp hs)] using hx⟩ else 0
  left_inv x := by
    classical
    by_cases hs : s.Nonempty
    · simp only [dite_eq_left hs]
    · simp only [dite_eq_right hs]
      apply Subtype.ext
      have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hx : x.val=0 := by simpa [zeroAugGrid,AlternatingCech.zeroAugmentation,he] using x.property
      exact hx.symm
  right_inv x := by
    classical
    funext hs
    simp only [dite_eq_left hs.down]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma gridCechEquiv_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (x : zeroAugGrid R n m s) :
    gridCechEquiv R n m t
      (Submodule.inclusion (AlternatingCech.zeroAugmentation_mono R (GridAmbient R n)
        (fun s => grid R n m s ∅) (grid_target_mono R n m ∅) hst) x)=
      (cechRes R n m hst).hom (gridCechEquiv R n m s x) := by
  classical
  funext ht
  by_cases hs : s.Nonempty
  · rw [cechRes_apply R n m hst hs ht.down]
    rfl
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hx : x.val=0 := by
      simpa [zeroAugGrid,AlternatingCech.zeroAugmentation,he] using x.property
    have hz : (cechRes R n m hst).hom (gridCechEquiv R n m s x) ht=0 := by
      change (if hs : s.Nonempty then _ else 0)=0
      rw [dite_eq_right hs]
    rw [hz]
    apply Subtype.ext
    exact hx

variable [LinearOrder (Chart n)]
 
def gridComplexIso : targetCech R n m ≅ FiniteModuleCech.complex (cechDiagram R n m) :=
  HomologicalComplex.Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard (Fin (n+1)) q =>
      gridCechEquiv R n m s.val)).toModuleIso) (by
        intro q r h
        obtain rfl : q+1=r := h
        dsimp only [targetCech,AlternatingCech.unaugmentedComplex]
        rw [FiniteModuleCech.complex_d,AlternatingCech.sortedComplex_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext s
        change _ = gridCechEquiv R n m s.val
          (∑ j : Fin (q+1), (-1:ℤ)^j.val •
            Submodule.inclusion _ (x (AlternatingCech.delete s j)))
        rw [map_sum]
        simp only [map_zsmul]
        change (∑ j : Fin (q+1), (-1:ℤ)^j.val •
          (cechRes R n m (AlternatingCech.delete_subset s j)).hom
            (gridCechEquiv R n m (AlternatingCech.delete s j).val (x (AlternatingCech.delete s j)))) = _
        apply Finset.sum_congr rfl
        intro j _
        rw [gridCechEquiv_natural])
end Lech.ProjectiveRoot

end

end OAI

import Mathlib
import OAI.RingTheory.Multiplicity.ScalarChartComparison

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
  {D E : Diagram R ι}
omit [Fintype ι] [LinearOrder ι] in
lemma nonempty_card {q : ℕ} (s : Set.powersetCard ι (q+1)) : s.val.Nonempty :=
  Finset.card_pos.mp (by rw [s.property]; omega)
 
def positiveIsoOfNonempty (e : ∀ s (_hs : s.Nonempty),D.obj s ≃ₗ[R] E.obj s)
    (he : ∀ {s t : Finset ι} (hst : s⊆t) (hs : s.Nonempty) (ht : t.Nonempty) (x : D.obj s),
      e t ht ((D.res hst).hom x)=(E.res hst).hom (e s hs x)) :
    positiveComplex D ≅ positiveComplex E :=
  Hom.isoOfComponents (fun q =>
    (LinearEquiv.piCongrRight (fun s : Set.powersetCard ι (q+1) => e s.val (nonempty_card s))).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d,positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      symm
      change e s.val (nonempty_card s) (∑ j : Fin (q+2),(-1:ℤ)^j.val •
        (D.res (AlternatingCech.delete_subset s j)).hom (x (AlternatingCech.delete s j)))=_
      rw [map_sum]
      simp only [map_zsmul]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun y => (-1:ℤ)^j.val • y)
        (he (AlternatingCech.delete_subset s j) (nonempty_card _) (nonempty_card _) _))
end Lech.FiniteModuleCech
namespace Lech.ReesRoot
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
def scalarCechIso : FiniteModuleCech.positiveComplex (scalarCechDiagram I z hz) ≅
    FiniteModuleCech.positiveComplex (FilteredCech.diagram I z hz 0) :=
  FiniteModuleCech.positiveIsoOfNonempty (scalarSectionEquiv I z hz)
    (fun hst hs ht x => scalarSectionEquiv_natural I z hz hst hs ht x)
end Lech.ReesRoot

end

end OAI

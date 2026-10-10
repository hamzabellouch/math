import Mathlib
import OAI.RingTheory.Multiplicity.CechReduction

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)

include hzero in
lemma Map.cochains_comp_zero (q : ℕ) : ψ.cochains q ∘ₗ φ.cochains q=0 := by
  apply LinearMap.ext
  intro x
  funext s
  exact congrArg (fun f : D.obj s.val ⟶ G.obj s.val => f.hom (x s)) (hzero s.val)

def diagramShortComplex (s : Finset ι) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (φ.app s) (ψ.app s) (hzero s)

def cochainsShortComplex (q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (φ.cochains q)) (ModuleCat.ofHom (ψ.cochains q))
    (ModuleCat.hom_ext (Map.cochains_comp_zero φ ψ hzero q))

lemma cochains_shortExact (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) (q : ℕ) :
    (cochainsShortComplex φ ψ hzero q).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext s
    exact (hs s.val).moduleCat_injective_f (congrFun hxy s))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro y
    choose x hx using fun s : Set.powersetCard ι q => (hs s.val).moduleCat_surjective_g (y s)
    exact ⟨x,funext hx⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    have hys (s : Set.powersetCard ι q) : (ψ.app s.val).hom (y s)=0 := congrFun hy s
    choose x hx using fun s : Set.powersetCard ι q =>
      (ShortComplex.moduleCat_exact_iff _).mp (hs s.val).exact (y s) (hys s)
    exact ⟨x,funext hx⟩)

variable [Fintype ι] [LinearOrder ι]

def complexShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk φ.complex ψ.complex (by
    apply Hom.ext
    funext q
    apply ModuleCat.hom_ext
    exact Map.cochains_comp_zero φ ψ hzero q)

lemma complex_shortExact (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) :
    (complexShortComplex φ ψ hzero).ShortExact :=
  shortExact_of_degreewise_shortExact _ (cochains_shortExact φ ψ hzero hs)

def positiveShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk φ.positiveComplex ψ.positiveComplex (by
    apply Hom.ext
    funext q
    apply ModuleCat.hom_ext
    exact Map.cochains_comp_zero φ ψ hzero (q+1))

lemma positive_shortExact (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) :
    (positiveShortComplex φ ψ hzero).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun q => cochains_shortExact φ ψ hzero hs (q+1))

end Lech.FiniteModuleCech

end

end OAI

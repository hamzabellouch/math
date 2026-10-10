import Mathlib
import OAI.RingTheory.Multiplicity.CechProducts
import OAI.RingTheory.Multiplicity.ReesRootEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (m : Fin n → ℤ) (i : Fin n)

def eulerCechLeft : Map (cechDiagram I z hz m)
    (prodDiagram (cechDiagram I z hz (Pi.single i 1+m)) (cechDiagram I z hz (Pi.single i 1+m))) :=
  (coordinateCechMap I z hz m i false).prodLift (coordinateCechMap I z hz m i true).neg

def eulerCechRight : Map
    (prodDiagram (cechDiagram I z hz (Pi.single i 1+m)) (cechDiagram I z hz (Pi.single i 1+m)))
    (cechDiagram I z hz (Pi.single i 1+(Pi.single i 1+m))) :=
  (coordinateCechMap I z hz (Pi.single i 1+m) i true).prodDesc
    (coordinateCechMap I z hz (Pi.single i 1+m) i false)

lemma eulerCech_zero (s : Finset (Fin (n+1))) :
    (eulerCechLeft I z hz m i).app s ≫ (eulerCechRight I z hz m i).app s=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (euler_shortExact I z hz s hs.down m i).2.1.apply_apply_eq_zero (x hs)

lemma eulerCech_shortExact (s : Finset (Fin (n+1))) :
    (diagramShortComplex (eulerCechLeft I z hz m i) (eulerCechRight I z hz m i)
      (eulerCech_zero I z hz m i) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext hs
    apply (euler_shortExact I z hz s hs.down m i).1
    exact Prod.ext (congrFun (congrArg Prod.fst hxy) hs) (congrFun (congrArg Prod.snd hxy) hs))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro y
    choose x hx using fun hs : PLift s.Nonempty => (euler_shortExact I z hz s hs.down m i).2.2 (y hs)
    exact ⟨(fun hs => (x hs).1,fun hs => (x hs).2),funext hx⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    have hys (hs : PLift s.Nonempty) : eulerRight I z hz s hs.down m i (y.1 hs,y.2 hs)=0 := congrFun hy hs
    choose x hx using fun hs : PLift s.Nonempty =>
      (euler_shortExact I z hz s hs.down m i).2.1 (y.1 hs,y.2 hs) |>.mp (hys hs)
    exact ⟨x,Prod.ext (funext (fun hs => congrArg Prod.fst (hx hs)))
      (funext (fun hs => congrArg Prod.snd (hx hs)))⟩)

 

def eulerCechSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  positiveShortComplex (eulerCechLeft I z hz m i) (eulerCechRight I z hz m i) (eulerCech_zero I z hz m i)
lemma eulerCechSequence_shortExact : (eulerCechSequence I z hz m i).ShortExact :=
  positive_shortExact _ _ _ (eulerCech_shortExact I z hz m i)
end Lech.ReesRoot

end

end OAI

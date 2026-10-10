import Mathlib
import OAI.RingTheory.Multiplicity.BicomplexImageLift
import OAI.RingTheory.Multiplicity.ReesRootGLayer

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) {M N : ModuleCat.{u} R} (f : M ⟶ N)
lemma rowMap_power_range (a : ℕ) (hf : f.hom.range=I^a • (⊤ : Submodule R N)) :
    ((rowFunctor I F h s hd p).map f).hom.range =
      I^a • (⊤ : Submodule R ((rowFunctor I F h s hd p).obj N)) := by
  rw [rowMap_eq]
  exact TensorIdeal.restrictIdeal_range _ _ _ (TensorIdeal.range_lTensor I f.hom a hf (F.X p))
end Lech.IdealFiltered

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)

abbrev enlargedPath (a N : ℕ) :=
  TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
    (enlargedStep I z hz F h s hd m a) N

include hgen in
lemma enlarged_power_range (a : ℕ) (p q : ℤ) :
    (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)).f p).f q).hom.range =
      I^a • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact IdealFiltered.rowMap_power_range I F h s hd p ((cechInclusionZ I z hz m a).f q) a
    (cechInclusionZ_range I z hz m hgen a q)

lemma enlarged_power_injective (a : ℕ) (p q : ℤ) [Module.Flat R (F.X p)] :
    Function.Injective (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)).f p).f q).hom :=
  IdealFiltered.rowMap_injective I F h s hd p _ (cechInclusionZ_injective I z hz m a q)

include hgen in
lemma enlargedStep_range (a N : ℕ) (p q : ℤ) :
    (((enlargedStep I z hz F h s hd m a N).f p).f q).hom.range =
      I^a • (⊤ : Submodule R (((enlargedAt I z hz F h s hd (twistSequence m a N)).X p).X q)) :=
  enlarged_power_range I z hz F h s hd (twistSequence m a N) hgen a p q

include hgen in
lemma enlargedPath_range (a N : ℕ) (p q : ℤ) :
    (((enlargedPath I z hz F h s hd m a N).f p).f q).hom.range =
      I^(a*N) • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact TotalGhost.towerPath_range I
    (X:=fun j => enlargedAt I z hz F h s hd (twistSequence m a j))
    (enlargedStep I z hz F h s hd m a) a
    (enlargedStep_range I z hz F h s hd m hgen a) N p q

lemma enlargedPath_injective (hflat : ∀ p,Module.Flat R (F.X p)) (a N : ℕ) (p q : ℤ) :
    Function.Injective (((enlargedPath I z hz F h s hd m a N).f p).f q).hom := by
  apply TotalGhost.towerPath_injective
  intro i p q
  let := hflat p
  exact enlarged_power_injective I z hz F h s hd _ a p q

include hgen in
 

theorem uniform_unit_nilpotence
    (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ M : ℕ, 0<M ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
      homologyMap (total.map (enlargedPath I z hz F h s hd m 1 M) (.up ℤ)) i=0 := by
  obtain ⟨a,ha0,hzero⟩ := uniform_enlarged_nilpotence I z hz F h s hd hp hfin hb ha
  refine ⟨a*(h+1),Nat.mul_pos ha0 (by omega),?_⟩
  intro m i
  apply TotalGhost.homology_zero_of_range (enlargedPath I z hz F h s hd m a (h+1))
    (enlargedPath_injective I z hz F h s hd m hflat a (h+1)) _ _ i (hzero m i)
  intro p q
  have hleft := enlargedPath_range I z hz F h s hd m hgen 1 (a * (h + 1)) p q
  simp only [one_mul] at hleft
  exact le_of_eq (hleft.trans
    (enlargedPath_range I z hz F h s hd m hgen a (h + 1) p q).symm)
end Lech.ReesRoot

end

end OAI

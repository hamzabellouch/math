import Mathlib
import OAI.RingTheory.Multiplicity.RootHomogeneousCoordinates
import OAI.RingTheory.Multiplicity.RootOverlap

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ProductSourceCover
open UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def powerSection (e : PowerIndex n) : GridAmbient R n :=
  ∏ i,embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n)^(powerExponent n e i)
end Lech.ProductSourceCover

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
local instance : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
local instance : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance : Module (A R n k) (GridAmbient R n) := Algebra.toModule
variable [Module.FaithfullyFlat (A R n k) B]
local instance : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance : IsScalarTower (A R n k) (D R n k t v hv d) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => ((algebraPoint R n k t v hv d (fun _ => false)).commutes a).symm
local instance (m : Fin n → ℤ) : Module (D R n k t v hv d)
    (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) := Submodule.module _

lemma globalCoefficientA_homogeneous (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    globalCoefficientA R n k t v hv d (fun i => (m i:ℤ))
      (RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d m e he)=
      ∏ i,embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n)^(e i) := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d
      (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false))
      (fun i => (m i:ℤ))).symm
      (1 ⊗ₜ[D R n k t v hv d]
        ((RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d _).symm
          (RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d m e he)))= _
  rw [RootInvariants.commonBasis_homogeneous]
  apply Finset.prod_congr rfl
  intro i hi
  have hx : chartToGridD R n k t v hv d (fun _ => false)
      (RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d (fun _ => false) i true)=
        embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n) := by
    change chartToGrid R n k t v hv d (fun _ => false)
      (coordinate R n k t v hv d (fun _ => false) i true)=_
    rw [chartToGrid_coordinate]
    simp only [↓reduceIte,chartScalar,AlgHom.comp_apply,ProductLaurent.chartMap_a,
      Bool.false_eq_true,Units.val_one,one_mul]
  have hy : chartToGridD R n k t v hv d (fun _ => false)
      (RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d (fun _ => false) i false)=1 := by
    change chartToGrid R n k t v hv d (fun _ => false)
      (coordinate R n k t v hv d (fun _ => false) i false)=_
    rw [chartToGrid_coordinate]
    simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
      ProductLaurent.chartMap_b,Units.val_one,map_one]
  rw [hx,hy,one_pow,mul_one]

lemma globalCoefficientA_consecutive (e : PowerIndex n) :
    globalCoefficientA R n k t v hv d (fun i => (powerWeight n i:ℤ))
      (RootInvariants.consecutiveSection (f R n k) n (hn R n k) t v hv d e)=powerSection R n e := by
  have he : RootInvariants.consecutiveSection (f R n k) n (hn R n k) t v hv d e =
      RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d
        (powerWeight n) (powerExponent n e) (powerExponent_bound n e) := by
    apply Subtype.ext
    exact binaryPower_prod t n d.roots e
  rw [he,globalCoefficientA_homogeneous]
  rfl

include t v hv d in
lemma exists_consecutive_section_basis :
    ∃ b : Module.Basis (PowerIndex n) (A R n k)
      (sectionModule R n k (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  obtain ⟨b,hb⟩ := RootInvariants.exists_consecutive_basis (f R n k) n (hn R n k) t v hv d
  refine ⟨b.map (globalSectionEquiv R n k t v hv d _),?_⟩
  intro e
  rw [Module.Basis.map_apply,hb]
  exact globalCoefficientA_consecutive R n k t v hv d e
end Lech.RootChartAtlas

namespace Lech.ProductSourceCover
open UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 

theorem exists_powerSection_basis :
    ∃ b : Module.Basis (PowerIndex n) (UniversalCoefficientChart.Ring R n k)
      (sectionModule R n k (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact RootChartAtlas.exists_consecutive_section_basis R n k (PrimitiveRootModule.coordinate f)
    (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
    (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k))
end Lech.ProductSourceCover

namespace Lech.ProjectiveRoot
open ProductSourceCover UniversalSplitting
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

 
theorem exists_powerSection_basis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ∃ b : Module.Basis (PowerIndex n) (Ring R n s)
      (Sections R n s hs (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  let k := hs.choose
  have hk : k∈s := hs.choose_spec
  let : Fact (k∈s) := ⟨hk⟩
  let : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
    coefficientAlgebra R n k s hk
  obtain ⟨b,hb⟩ := ProductSourceCover.exists_powerSection_basis R n k
  refine ⟨(b.baseChange (Ring R n s)).map (chartBaseChange R n k s hs _),?_⟩
  intro e
  rw [Module.Basis.map_apply,Module.Basis.baseChange_apply]
  rw [chartBaseChange_one R n k s hs _ (b e)]
  exact hb e

 
def powerSectionBasis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module.Basis (PowerIndex n) (Ring R n s)
      (Sections R n s hs (fun i => (powerWeight n i:ℤ))) :=
  (exists_powerSection_basis R n s hs).choose
lemma powerSectionBasis_val (s : Finset (Fin (n+1))) (hs : s.Nonempty) (e : PowerIndex n) :
    (powerSectionBasis R n s hs e : GridAmbient R n)=powerSection R n e :=
  (exists_powerSection_basis R n s hs).choose_spec e
end Lech.ProjectiveRoot

end

end OAI

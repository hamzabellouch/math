import Mathlib
import OAI.RingTheory.Multiplicity.FiniteComplexTopInclusion

namespace OAI

noncomputable section
namespace Lech.BicomplexTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev Diagonal (k : ℤ) := (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' {k}

def diagonal (k : ℤ) : Double (R:=R) ⥤ (Discrete (Diagonal k) ⥤ ModuleCat.{u} R) where
  obj K := Discrete.functor (fun pq => (K.X pq.val.1).X pq.val.2)
  map f := Discrete.natTrans (fun pq => (f.f pq.as.val.1).f pq.as.val.2)

instance diagonal_preservesFiniteLimits (k : ℤ) : PreservesFiniteLimits (diagonal (R:=R) k) := by
  apply preservesFiniteLimits_of_evaluation
  intro pq
  change PreservesFiniteLimits (eval (Row (R:=R)) (.up ℤ) pq.as.val.1 ⋙ eval (ModuleCat.{u} R) (.up ℤ) pq.as.val.2)
  infer_instance
instance diagonal_preservesFiniteColimits (k : ℤ) : PreservesFiniteColimits (diagonal (R:=R) k) := by
  apply preservesFiniteColimits_of_evaluation
  intro pq
  change PreservesFiniteColimits (eval (Row (R:=R)) (.up ℤ) pq.as.val.1 ⋙ eval (ModuleCat.{u} R) (.up ℤ) pq.as.val.2)
  infer_instance
instance diagonal_additive (k : ℤ) : (diagonal (R:=R) k).Additive where
  map_add := by intros; ext pq; rfl

lemma diagonal_colim_map (k : ℤ) {K L : Double (R:=R)} (f : K ⟶ L) :
    ((diagonal (R:=R) k ⋙ colim).map f) = ((functor (R:=R)).map f).f k := by
  apply total.hom_ext
  intro p q hpq
  change colimit.ι ((diagonal (R:=R) k).obj K) ⟨⟨(p,q),hpq⟩⟩ ≫
    colim.map ((diagonal (R:=R) k).map f) = _
  rw [colimit.ι_map]
  change (f.f p).f q ≫ ιTotal L (.up ℤ) p q k hpq = _
  exact (ιTotal_map K L f (.up ℤ) p q k hpq).symm

 
def totalDegreeIso (k : ℤ) : functor (R:=R) ⋙ eval (ModuleCat.{u} R) (.up ℤ) k ≅ diagonal k ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom]
    exact (diagonal_colim_map k f).symm)

lemma total_shortExact (S : ShortComplex (Double (R:=R))) (hS : S.ShortExact) :
    (S.map (functor (R:=R))).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro k
  have h := (hS.map_of_exact (diagonal k)).map_of_exact colim
  apply ShortComplex.shortExact_of_iso (S₁:=((S.map (diagonal k)).map colim)) _ h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom]
    exact diagonal_colim_map k S.f
  · simp only [Iso.refl_hom]
    exact diagonal_colim_map k S.g
end Lech.BicomplexTotal

end

end OAI

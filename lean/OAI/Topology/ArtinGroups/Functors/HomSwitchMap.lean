import Mathlib
import OAI.Topology.ArtinGroups.Functors.LeftHomPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

lemma homSwitch_degree [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Zigzag.MapDegree U (leftHomPlacement Q step hstep N hN p u c)
      (rightHomPlacement Q step hstep N hN p u c) 0 0
      (Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A p u c)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      change (p i).cochain = (p i).cochain+0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := evaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homSwitch,Matrix.blockDiagonal'_apply_eq] using h)
      change (p i).internal + Path.length y.2.val = (p i).internal + Path.length x.2.val + 0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim

omit [Fintype V] in
lemma homUnswitch_degree [DecidableEq T] (p : T → GeneratorPlacement (V × J)) (u:V) (c:J) :
    Zigzag.MapDegree U (rightHomPlacement Q step hstep N hN p u c)
      (leftHomPlacement Q step hstep N hN p u c) 0 0
      (Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A p u c)) := by
  apply Zigzag.scalarCornerMatrix_degree
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      change (p i).cochain = (p i).cochain+0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := inverseEvaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homUnswitch,Matrix.blockDiagonal'_apply_eq] using h)
      change (p i).internal + Path.length y.2.val = (p i).internal + Path.length x.2.val + 0
      omega
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim

section Isomorphism
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

local notation "L" => leftHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "R" => rightHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def homSwitchMap (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.Map U (L E u c) (R E u c) where
  matrix := Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := homSwitch_degree Q step hstep N hN orient μ A _ _ _
  commute := by
    change Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential) *
      Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c) =
      Zigzag.scalarCornerMatrix U (u,c) (homSwitch Q step hstep N hN orient μ A E.placement u c) *
      Zigzag.scalarCornerMatrix U (u,c) (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential)
    rw [Zigzag.scalarCornerMatrix_mul,Zigzag.scalarCornerMatrix_mul]
    congr 1
    exact homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def homUnswitchMap (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.Map U (R E u c) (L E u c) where
  matrix := Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c)
  entries := Zigzag.scalarCornerMatrix_entries U (u,c) _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := homUnswitch_degree Q step hstep N hN orient μ A _ _ _
  commute := by
    change Zigzag.scalarCornerMatrix U (u,c) (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential) *
      Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c) =
      Zigzag.scalarCornerMatrix U (u,c) (homUnswitch Q step hstep N hN orient μ A E.placement u c) *
      Zigzag.scalarCornerMatrix U (u,c) (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
    rw [Zigzag.scalarCornerMatrix_mul,Zigzag.scalarCornerMatrix_mul]
    congr 1
    exact homUnswitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

noncomputable def homComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) :
    Zigzag.BasedComplex.ChainIsomorphism U (L E u c) (R E u c) := by
  classical
  exact {
    forward := homSwitchMap Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
    backward := homUnswitchMap Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u c
    sourceEquation := by
      change Zigzag.scalarCornerMatrix U (u,c) _ * Zigzag.scalarCornerMatrix U (u,c) _ = _
      rw [Zigzag.scalarCornerMatrix_mul,homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
      exact Zigzag.scalarCornerMatrix_identity U (u,c) _ (fun _ => rfl)
    targetEquation := by
      change Zigzag.scalarCornerMatrix U (u,c) _ * Zigzag.scalarCornerMatrix U (u,c) _ = _
      rw [Zigzag.scalarCornerMatrix_mul,homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF]
      exact Zigzag.scalarCornerMatrix_identity U (u,c) _ (fun _ => rfl) }

end Isomorphism
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI

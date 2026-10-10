import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
universe u
variable {k : Type u} [Field k] [Infinite k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

noncomputable def torusExpansion (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (v : V) : ℤ →₀ V :=
  Classical.choose (rational_torus_integerExpansions k ρ hρ v)

omit [Infinite k] in
lemma torusExpansion_spec (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (v : V) (a : kˣ) :
    ρ (diagonalTorus k a) v = (torusExpansion ρ hρ v).sum
      (fun n x => integerCharacter k n a • x) :=
  Classical.choose_spec (rational_torus_integerExpansions k ρ hρ v) a

lemma torusExpansion_unique (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (v : V) (c : ℤ →₀ V)
    (hc : ∀ a, ρ (diagonalTorus k a) v = c.sum (fun n x => integerCharacter k n a • x)) :
    torusExpansion ρ hρ v = c := by
  apply function_finsupp_ext (fun n a => integerCharacter k n a)
    ((linearIndependent_monoidHom kˣ k).comp _ (integerCharacter_injective k))
  intro a
  rw [← torusExpansion_spec, hc]

 
noncomputable def torusWeightProjection (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (n : ℤ) : V →ₗ[k] V where
  toFun v := torusExpansion ρ hρ v n
  map_add' v w := by
    classical
    have h := torusExpansion_unique ρ hρ (v+w)
      (torusExpansion ρ hρ v + torusExpansion ρ hρ w) (fun a => by
        rw [Finsupp.sum_add_index (fun _ _ => smul_zero _) (fun _ _ _ _ => smul_add _ _ _)]
        rw [map_add, ← torusExpansion_spec, ← torusExpansion_spec])
    exact congrArg (fun c => c n) h
  map_smul' t v := by
    classical
    have h := torusExpansion_unique ρ hρ (t • v)
      (t • torusExpansion ρ hρ v) (fun a => by
        rw [Finsupp.sum_smul_index' (fun _ => smul_zero _), map_smul,
          torusExpansion_spec]
        simp only [Finsupp.sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact smul_comm t (integerCharacter k i a) _)
    exact congrArg (fun c => c n) h

lemma torusWeightProjection_eigen (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (n m : ℤ) (v : V)
    (hv : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k m a • v) :
    torusWeightProjection ρ hρ n v = if m = n then v else 0 := by
  classical
  have h := torusExpansion_unique ρ hρ v (Finsupp.single m v) (fun a => by
    simpa using hv a)
  change torusExpansion ρ hρ v n = _
  rw [h, Finsupp.single_apply]

lemma torusWeightProjection_zero_fixed (ρ : Representation k (SL2 k) V)
    (hρ : IsRational k ρ) (v : V)
    (hv : ∀ a, ρ (diagonalTorus k a) v = v) :
    torusWeightProjection ρ hρ 0 v = v := by
  rw [torusWeightProjection_eigen ρ hρ 0 0 v (by simpa [integerCharacter] using hv)]
  simp
end FiberFunctorProof

end OAI

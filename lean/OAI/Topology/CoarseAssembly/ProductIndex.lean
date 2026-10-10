import OAI.Topology.CoarseAssembly.UnitaryIndex
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

/-! # Additivity of the Fredholm index on products -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

def submoduleProductEquiv (P : Submodule ℂ H) (Q : Submodule ℂ K) :
    P.prod Q ≃ₗ[ℂ] P × Q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1, x.2), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quotientProductEquiv (P : Submodule ℂ H) (Q : Submodule ℂ K) :
    ((H × K) ⧸ P.prod Q) ≃ₗ[ℂ] (H ⧸ P) × (K ⧸ Q) := by
  let f := P.mkQ.prodMap Q.mkQ
  have hf : Function.Surjective f := by
    rintro ⟨x, y⟩
    obtain ⟨x', rfl⟩ := P.mkQ_surjective x
    obtain ⟨y', rfl⟩ := Q.mkQ_surjective y
    exact ⟨(x', y'), rfl⟩
  have hk : f.ker = P.prod Q := by simp only [f, LinearMap.ker_prodMap, Submodule.ker_mkQ]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

theorem finrank_submoduleProduct (P : Submodule ℂ H) (Q : Submodule ℂ K)
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q] :
    Module.finrank ℂ (P.prod Q) = Module.finrank ℂ P + Module.finrank ℂ Q := by
  rw [(submoduleProductEquiv P Q).finrank_eq, Module.finrank_prod]

theorem finrank_quotientProduct (P : Submodule ℂ H) (Q : Submodule ℂ K)
    [FiniteDimensional ℂ (H ⧸ P)] [FiniteDimensional ℂ (K ⧸ Q)] :
    Module.finrank ℂ ((H × K) ⧸ P.prod Q) =
      Module.finrank ℂ (H ⧸ P) + Module.finrank ℂ (K ⧸ Q) := by
  rw [(quotientProductEquiv P Q).finrank_eq, Module.finrank_prod]

theorem fredholmIndex_prodMap (T : End H) (S : End K) (hT : T.IsFredholm) (hS : S.IsFredholm) :
    (T.toLinearMap.prodMap S.toLinearMap).index = T.toLinearMap.index + S.toLinearMap.index := by
  let := hT.finite_ker
  let := hS.finite_ker
  let := hT.finite_coker
  let := hS.finite_coker
  have hk : (T.toLinearMap.prodMap S.toLinearMap).ker = T.ker.prod S.ker :=
    LinearMap.ker_prodMap T.toLinearMap S.toLinearMap
  have hr : (T.toLinearMap.prodMap S.toLinearMap).range = T.range.prod S.range :=
    LinearMap.range_prodMap T.toLinearMap S.toLinearMap
  have hkdim : Module.finrank ℂ (T.toLinearMap.prodMap S.toLinearMap).ker =
      Module.finrank ℂ T.ker + Module.finrank ℂ S.ker := by
    rw [hk]
    exact finrank_submoduleProduct T.ker S.ker
  have hrdim : Module.finrank ℂ ((H × K) ⧸ (T.toLinearMap.prodMap S.toLinearMap).range) =
      Module.finrank ℂ (H ⧸ T.range) + Module.finrank ℂ (K ⧸ S.range) := by
    rw [hr]
    exact finrank_quotientProduct T.range S.range
  simp only [LinearMap.index_eq_finrank_sub]
  rw [hkdim, hrdim, Nat.cast_add, Nat.cast_add]
  omega

end CoarseAssembly.Analytic

end

end OAI

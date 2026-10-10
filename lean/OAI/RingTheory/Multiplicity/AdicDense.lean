import Mathlib

namespace OAI

noncomputable section
namespace Lech.AdicFlat
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

lemma map_pow_smul_top {M : Type*} [AddCommGroup M] [Module R M] [Module T M]
    [IsScalarTower R T M] (I : Ideal R) (J : Ideal T)
    (hJ : I.map (algebraMap R T)=J) (n : ℕ) :
    (J^n • (⊤ : Submodule T M)).restrictScalars R=I^n • (⊤ : Submodule R M) := by
  simpa only [Ideal.map_pow,hJ,Submodule.restrictScalars_top] using
    Submodule.restrictScalars_map_smul_eq (I^n) (⊤ : Submodule T M)

lemma completion_dense (I : Ideal R) (J : Ideal T) (hJ : I.map (algebraMap R T)=J)
    (hfg : J.FG) (n : ℕ) (s : AdicCompletion J T) :
    ∃ t : T,s-algebraMap T (AdicCompletion J T) t ∈
      I^n • (⊤ : Submodule R (AdicCompletion J T)) := by
  obtain ⟨t,ht⟩ := (J^n • (⊤ : Submodule T T)).mkQ_surjective
    (AdicCompletion.eval J T n s)
  refine ⟨t,?_⟩
  rw [← map_pow_smul_top I J hJ]
  change s-AdicCompletion.of J T t ∈ J^n • (⊤ : Submodule T (AdicCompletion J T))
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg,LinearMap.mem_ker,map_sub,
    AdicCompletion.eval_of,ht,sub_self]

lemma completion_contract (I : Ideal R) (J : Ideal T) (hJ : I.map (algebraMap R T)=J)
    (hfg : J.FG) (n : ℕ) (t : T)
    (ht : algebraMap T (AdicCompletion J T) t ∈
      I^n • (⊤ : Submodule R (AdicCompletion J T))) :
    t ∈ I^n • (⊤ : Submodule R T) := by
  rw [← map_pow_smul_top I J hJ] at ht ⊢
  change AdicCompletion.of J T t ∈ J^n • (⊤ : Submodule T (AdicCompletion J T)) at ht
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg,LinearMap.mem_ker,
    AdicCompletion.eval_of,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at ht
  exact ht
end Lech.AdicFlat

end

end OAI

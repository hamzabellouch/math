import OAI.RepresentationTheory.RestrictedTilting.StableRestriction
import OAI.RepresentationTheory.RestrictedTilting.RepProducts

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
variable (k : Type u) [Field k]

 
noncomputable def steinbergSpan (p r : ℕ) (A B : FDRep k (SL2 k)) :
    Submodule k (A ⟶ B) :=
  Submodule.span k {f | ∃ (X : FDRep k (SL2 k)), IsTilting k X ∧
    ∃ (a : A ⟶ steinberg k p r ⊗ X) (b : steinberg k p r ⊗ X ⟶ B), f = a ≫ b}

variable (p r : ℕ)

lemma steinbergSpan.precomp {A B C : FDRep k (SL2 k)} (a : A ⟶ B) (f : B ⟶ C)
    (hf : f ∈ steinbergSpan k p r B C) : a ≫ f ∈ steinbergSpan k p r A C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨X,hX,b,c,rfl⟩ := hf
    exact Submodule.subset_span ⟨X,hX,a ≫ b,c,by simp⟩
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [Preadditive.comp_add] using
      (steinbergSpan k p r A C).add_mem ihf ihg
  | smul c f hf ih => simpa only [Linear.comp_smul] using
      (steinbergSpan k p r A C).smul_mem c ih

lemma steinbergSpan.postcomp {A B C : FDRep k (SL2 k)} (f : A ⟶ B) (a : B ⟶ C)
    (hf : f ∈ steinbergSpan k p r A B) : f ≫ a ∈ steinbergSpan k p r A C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨X,hX,b,c,rfl⟩ := hf
    exact Submodule.subset_span ⟨X,hX,b,c ≫ a,by simp⟩
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [Preadditive.add_comp] using
      (steinbergSpan k p r A C).add_mem ihf ihg
  | smul c f hf ih => simpa only [Linear.smul_comp] using
      (steinbergSpan k p r A C).smul_mem c ih

lemma steinbergSpan_of_high_left (X : FDRep k (SL2 k)) (hX : IsTilting k X)
    {B : FDRep k (SL2 k)} (f : steinberg k p r ⊗ X ⟶ B) :
    f ∈ steinbergSpan k p r _ B :=
  Submodule.subset_span ⟨X,hX,𝟙 _,f, by simp⟩

lemma steinbergSpan_of_high_right (X : FDRep k (SL2 k)) (hX : IsTilting k X)
    {A : FDRep k (SL2 k)} (f : A ⟶ steinberg k p r ⊗ X) :
    f ∈ steinbergSpan k p r A _ :=
  Submodule.subset_span ⟨X,hX,f,𝟙 _, by simp⟩

lemma steinbergSpan_to_ideal (A B : Tilting k) (f : A.obj ⟶ B.obj)
    (hf : f ∈ steinbergSpan k p r A.obj B.obj) :
    ObjectProperty.homMk f ∈ steinbergIdeal k p r A B := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨X,hX,a,b,hf⟩ := hf
    exact Submodule.subset_span ⟨⟨X,hX⟩,a,b,hf⟩
  | zero => exact (steinbergIdeal k p r A B).zero_mem
  | add f g hf hg ihf ihg => exact (steinbergIdeal k p r A B).add_mem ihf ihg
  | smul c f hf ih => exact (steinbergIdeal k p r A B).smul_mem c ih

end FiberFunctorProof

namespace FiberFunctorProof.FactorsThroughProjective
open CategoryTheory
variable {C : Type*} [Category* C] {A B D : C}
lemma precomp (a : A ⟶ B) {f : B ⟶ D} (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (a ≫ f) := by
  obtain ⟨P,hP,b,c,rfl⟩ := hf
  exact ⟨P,hP,a ≫ b,c,by simp⟩
lemma postcomp {f : A ⟶ B} (hf : FactorsThroughProjective f) (a : B ⟶ D) :
    FactorsThroughProjective (f ≫ a) := by
  obtain ⟨P,hP,b,c,rfl⟩ := hf
  exact ⟨P,hP,b,c ≫ a,by simp⟩
end FiberFunctorProof.FactorsThroughProjective

end OAI

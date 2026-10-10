import OAI.RepresentationTheory.RestrictedTilting.CompatibleJets

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
variable (k : Type u) [Field k]
variable {G : Type u} [Group G]

noncomputable def repProduct (A B : FDRep k G) : FDRep k G :=
  FDRep.of (Representation.prod A.ρ B.ρ)

noncomputable def repInl (A B : FDRep k G) : A ⟶ repProduct k A B :=
  fdrepHom k (LinearMap.inl k A B) (by
    intro g v
    change (A.ρ g v, (0 : B)) = (A.ρ g v, B.ρ g 0)
    rw [map_zero])
noncomputable def repInr (A B : FDRep k G) : B ⟶ repProduct k A B :=
  fdrepHom k (LinearMap.inr k A B) (by
    intro g v
    change ((0 : A), B.ρ g v) = (A.ρ g 0, B.ρ g v)
    rw [map_zero])
noncomputable def repFst (A B : FDRep k G) : repProduct k A B ⟶ A :=
  fdrepHom k (LinearMap.fst k A B) (by intros; rfl)
noncomputable def repSnd (A B : FDRep k G) : repProduct k A B ⟶ B :=
  fdrepHom k (LinearMap.snd k A B) (by intros; rfl)

lemma repProduct_shortExact (A B : FDRep k G) :
    (ShortComplex.mk (repInl k A B) (repSnd k A B) (by
      apply fdrep_hom_ext k; intro x; rfl)).ShortExact := by
  apply fdrep_shortExact k _ (by intro a b h; exact congrArg Prod.fst h)
    (by intro b; exact ⟨(0,b), rfl⟩)
  ext x
  constructor
  · rintro ⟨a,rfl⟩; rfl
  · intro h
    exact ⟨x.1, Prod.ext rfl h.symm⟩

lemma repProduct_decomposition (A B : FDRep k G) :
    repFst k A B ≫ repInl k A B + repSnd k A B ≫ repInr k A B = 𝟙 _ := by
  apply fdrep_hom_ext k
  intro x
  change (x.1, 0) + (0, x.2) = x
  exact Prod.ext (add_zero _) (zero_add _)

lemma IsTilting.product {A B : FDRep k (SL2 k)} (hA : IsTilting k A)
    (hB : IsTilting k B) : IsTilting k (repProduct k A B) :=
  hA.extension k hB (hA.1.prod k hB.1) _ _ _ (repProduct_shortExact k A B)
end FiberFunctorProof

end OAI

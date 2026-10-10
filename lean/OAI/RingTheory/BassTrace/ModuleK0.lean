import OAI.RingTheory.BassTrace.RightRetractions

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.RightProjective

open scoped Classical

universe u v

variable {R : Type u} [Ring R]

lemma Object.presentationClass_eq (P : Object.{u,v} R) (r : Retraction R P.carrier) :
    P.presentationClass=K0.classOf r.idempotent := P.retraction.class_eq r

lemma Object.presentationClass_iso (P Q : Object.{u,v} R)
    (i : P.carrier ≃ₗ[Rᵐᵒᵖ] Q.carrier) : P.presentationClass=Q.presentationClass := by
  rw [Q.presentationClass_eq (P.retraction.transport i), Retraction.transport_idempotent]
  rfl

lemma Object.presentationClass_prod (P Q : Object.{u,v} R) :
    (P.prod Q).presentationClass=P.presentationClass+Q.presentationClass := by
  calc
    _ = K0.classOf (P.retraction.prod Q.retraction).idempotent :=
      (P.prod Q).presentationClass_eq (P.retraction.prod Q.retraction)
    _ = P.presentationClass+Q.presentationClass := by
      rw [Retraction.prod_idempotent,classOf_directSum]
      rfl

def moduleClass (P : Object.{u,v} R) : ModuleK0.{u,v} R :=
  QuotientAddGroup.mk' (moduleRelations R) (FreeAbelianGroup.of P)

lemma moduleRelations_in_kernel : moduleRelations R≤(rawPresentation.{u,v} (R := R)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro x hx
  rcases hx with ⟨P,Q,⟨i⟩,rfl⟩ | ⟨P,Q,rfl⟩
  · change rawPresentation (FreeAbelianGroup.of P-FreeAbelianGroup.of Q)=0
    simp only [map_sub,rawPresentation,FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (P.presentationClass_iso Q i)
  · change rawPresentation
      (FreeAbelianGroup.of (P.prod Q)-FreeAbelianGroup.of P-FreeAbelianGroup.of Q)=0
    simp only [map_sub,rawPresentation,FreeAbelianGroup.lift_apply_of,Object.presentationClass_prod]
    abel

lemma presentation_moduleClass (P : Object.{u,v} R) :
    presentation (moduleClass P)=P.presentationClass := by
  simp [presentation,moduleClass,rawPresentation]

variable {G : Type u} [_root_.Group G]

lemma HattoriStallings_moduleClass (P : Object.{u,v} (MonoidAlgebra ℂ G))
    (r : Retraction (MonoidAlgebra ℂ G) P.carrier) :
    HattoriStallings (moduleClass P)=K0.classTrace (Matrix.trace r.idempotent.matrix) := by
  change K0.HattoriStallings (presentation (moduleClass P))=_
  rw [presentation_moduleClass,P.presentationClass_eq r,K0.HattoriStallings_classOf]

lemma HattoriStallings_moduleClass_coefficient (P : Object.{u,v} (MonoidAlgebra ℂ G))
    (r : Retraction (MonoidAlgebra ℂ G) P.carrier) (g : G) :
    HattoriStallings (moduleClass P) (ConjClasses.mk g)=
      classCoefficient g (Matrix.trace r.idempotent.matrix) := by
  rw [HattoriStallings_moduleClass P r,K0.classTrace_apply]

end BassTrace.RightProjective

end

end OAI

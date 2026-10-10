import Mathlib

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {S : Type*}

def restrictedMatrix (M : CoxeterMatrix S) (J : Set S) : CoxeterMatrix J where
  M i j := M i j
  isSymm := M.isSymm.submatrix Subtype.val
  diagonal i := M.diagonal i
  off_diagonal i j h := M.off_diagonal i j (fun he => h (Subtype.ext he))

@[simp] lemma restrictedMatrix_apply (M : CoxeterMatrix S) (J : Set S) (i j : J) :
    restrictedMatrix M J i j=M i j := rfl

noncomputable def restrictionHom (M : CoxeterMatrix S) (J : Set S) :
    (restrictedMatrix M J).Group →* M.Group :=
  (restrictedMatrix M J).toCoxeterSystem.lift
    ⟨fun i => M.simple i, fun i j => M.toCoxeterSystem.simple_mul_simple_pow i j⟩

@[simp] lemma restrictionHom_simple (M : CoxeterMatrix S) (J : Set S) (i : J) :
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.simple i)=M.toCoxeterSystem.simple i :=
  (restrictedMatrix M J).toCoxeterSystem.lift_apply_simple _ i

end HarmonicArtin.CoxeterExchange

end OAI

import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicReadBraid
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd

namespace OAI

/-! The parabolic gallery retraction as an action of the Artin presentation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J
local notation "State" => M.Group × Artin R

noncomputable def parabolicStepArtin (w : M.Group) (s : S) : Artin R :=
  wordArtin R (parabolicStepLetter cs J w s).toList

omit [Fintype S] in
lemma parabolicStepArtin_reverse (w : M.Group) (s : S) :
    parabolicStepArtin M J (w*(cs).simple s) s=parabolicStepArtin M J w s := by
  unfold parabolicStepArtin
  rw [parabolicStepLetter_reverse]

noncomputable def parabolicStepPerm (s : S) : Equiv.Perm State where
  toFun x := (x.1*(cs).simple s,x.2*parabolicStepArtin M J x.1 s)
  invFun x := (x.1*(cs).simple s,x.2*(parabolicStepArtin M J x.1 s)⁻¹)
  left_inv := by
    rintro ⟨w,a⟩
    apply Prod.ext
    · exact (cs).simple_mul_simple_cancel_right s
    · change (a*parabolicStepArtin M J w s)*(parabolicStepArtin M J (w*(cs).simple s) s)⁻¹=a
      rw [parabolicStepArtin_reverse,mul_inv_cancel_right]
  right_inv := by
    rintro ⟨w,a⟩
    apply Prod.ext
    · exact (cs).simple_mul_simple_cancel_right s
    · change (a*(parabolicStepArtin M J w s)⁻¹)*parabolicStepArtin M J (w*(cs).simple s) s=a
      rw [parabolicStepArtin_reverse,inv_mul_cancel_right]

noncomputable def parabolicWordPerm (u : List S) : (Equiv.Perm State)ᵐᵒᵖ :=
  (u.map fun s => MulOpposite.op (parabolicStepPerm M J s)).prod

omit [Fintype S] in
/-- Using the opposite permutation group makes the word act in its written order. -/
lemma parabolicWordPerm_apply (u : List S) (w : M.Group) (a : Artin R) :
    MulOpposite.unop (parabolicWordPerm M J u) (w,a) =
      (w*(cs).wordProd u,a*wordArtin R (parabolicRead cs J w u)) := by
  induction u generalizing w a with
  | nil => simp [parabolicWordPerm,parabolicRead,wordArtin]
  | cons s u ih =>
    change MulOpposite.unop (parabolicWordPerm M J u)
      (w*(cs).simple s,a*parabolicStepArtin M J w s)=_
    rw [ih]
    simp only [(cs).wordProd_cons,parabolicRead,wordArtin_append,parabolicStepArtin,mul_assoc]

lemma parabolicWordPerm_braid (i j : S) :
    parabolicWordPerm M J (altList i j (M i j))=
      parabolicWordPerm M J (altList j i (M i j)) := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  rintro ⟨w,a⟩
  rw [parabolicWordPerm_apply,parabolicWordPerm_apply,altList_braid cs i j,
    parabolicRead_braid M J w i j]

private lemma parabolicPerm_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => MulOpposite.op (parabolicStepPerm M J s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact parabolicWordPerm_braid M J i j

noncomputable def parabolicRetractionAction : Artin M →* (Equiv.Perm State)ᵐᵒᵖ :=
  PresentedGroup.toGroup (parabolicPerm_relators M J)

lemma parabolicRetractionAction_generator (s : S) :
    parabolicRetractionAction M J (generator M s)=MulOpposite.op (parabolicStepPerm M J s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI

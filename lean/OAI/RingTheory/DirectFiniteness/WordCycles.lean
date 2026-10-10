import OAI.RingTheory.DirectFiniteness.DiagramJoining

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

lemma follows_formPerm [DecidableEq α] (l : List α) : Follows l.formPerm l := by
  intro x _
  exact congrArg (fun d : DecidableEq α => @List.formPerm α d l x)
    (Subsingleton.elim _ _)

end KaplanskyCounterexample.Planar

end

end OAI

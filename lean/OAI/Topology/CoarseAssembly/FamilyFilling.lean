import OAI.Topology.CoarseAssembly.FilledWalks
import OAI.Topology.CoarseAssembly.CompactFamilyMap
import OAI.Topology.CoarseAssembly.RipsFamilyMap

namespace OAI

/-! # The entire family of base loops vanishes through its actual filling

Both arrows through the disjoint union of compact polygons are constructed
proper maps. The vanishing follows only from the specified published compact
homotopy and countable-additivity inputs.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable (o : ∀ j, Disc j) (p : ∀ j, (discGraph j).Walk (o j) (o j))

def baseBoundaryLoops (j : ℕ) : C(WindingCircle, Point (Disc j) 1) :=
  loopCircle (walkPath (by norm_num) discEdgeBound (p j))

def filledBoundaryLoops (j : ℕ) : C(WindingCircle, FilledDisc j) :=
  loopCircle (filledWalk (p j))

theorem boundaryFamily_factors :
    letI := separatedMetric o
    ripsFamilyMap o 1 (baseBoundaryLoops o p) =
      (ripsFamilyMap o 1 filledToRips).comp (compactFamilyMap (filledBoundaryLoops o p)) := by
  let := separatedMetric o
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change separatedRipsMap o 1 j (baseBoundaryLoops o p j z) =
    separatedRipsMap o 1 j (filledToRips j (filledBoundaryLoops o p j z))
  exact congrArg (separatedRipsMap o 1 j) (DFunLike.congr_fun (filledToRips_loop (p j)) z).symm

/-- Every class pushed along this family of closed base walks vanishes
already at scale one, before passage to the coarse direct limit. -/
theorem baseBoundaryFamily_zero (input : PublishedCompactHomotopyInput)
    (hadd : CountableAdditivityInput FilledDisc)
    (a : LocallyFiniteK1 (Sigma (fun _ : ℕ => WindingCircle))) :
    letI := separatedMetric o
    pushforward (ripsFamilyMap o 1 (baseBoundaryLoops o p)) a = 0 := by
  let := separatedMetric o
  let := contracted_family_odd_group_zero input FilledDisc filledDiscContraction hadd
  rw [boundaryFamily_factors o p, pushforward_comp, AddMonoidHom.comp_apply]
  have hzero : pushforward (compactFamilyMap (filledBoundaryLoops o p)) a = 0 :=
    Subsingleton.elim _ _
  rw [hzero, map_zero]

end CoarseAssembly

end

end OAI

import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.OrderMappingCylinder
import OAI.Topology.ArtinGroups.Realizations.WeightInsertRetract

namespace OAI

namespace HarmonicArtin
universe u
variable {P Q:Type u} [PartialOrder P] [PartialOrder Q]

theorem orderWeights_contractible_of_lower_preimages (f:P→oQ)
    (k:P→ℕ) (l:Q→ℕ) (N L:ℕ) (hk:∀p,k p≤N) (hl:∀q,l q≤L)
    (hkm:StrictMono k) (hlm:StrictMono l) (hQ:ContractibleSpace (OrderWeights Q))
    (hf:∀q,ContractibleSpace (OrderWeights {p:P // f p≤q})) :
    ContractibleSpace (OrderWeights P) := by
  let R:=OrderMappingCylinder f
  have hR:ContractibleSpace (OrderWeights R):=OrderMappingCylinder.weights_contractible f hQ
  have hF:∀v:R,v∉OrderMappingCylinder.old f →
      ContractibleSpace (OrderWeights {x:R // x∈OrderMappingCylinder.old f ∧ x<v}):=by
    intro v hv
    obtain ⟨q,rfl⟩:=(OrderMappingCylinder.not_old_iff f v).mp hv
    exact (weightHomeomorph (OrderMappingCylinder.oldLowerIso f q)).contractibleSpace_iff.mp (hf q)
  obtain ⟨r,hr⟩:=orderWeights_retract_of_lower_fibers (OrderMappingCylinder.old f)
    (OrderMappingCylinder.rank f k l N) (N+1+L)
    (OrderMappingCylinder.rank_bound f k l N L hk hl)
    (OrderMappingCylinder.rank_strict f k l N hk hkm hlm) hF
  have hA:ContractibleSpace (OrderWeights (OrderMappingCylinder.old f)):=
    contractible_of_continuous_retract
      ⟨weightMap (weightInclusion (OrderMappingCylinder.old f)),weightMap_continuous _⟩ r hr hR
  exact (weightHomeomorph (OrderMappingCylinder.oldIso f)).contractibleSpace_iff.mpr hA

end HarmonicArtin

end OAI

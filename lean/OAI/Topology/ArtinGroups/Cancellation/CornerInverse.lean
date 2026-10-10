import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.GaussianCancellation

lemma corner_inverse {R : Type*} [Ring R]
    (e n : R) (he : e * e = e)
    (hen : e * n = n) (hne : n * e = n) (hn : n * n * n = 0) :
    (e + n) * (e - n + n * n) = e ∧
    (e - n + n * n) * (e + n) = e := by
  have henn : e * (n * n) = n * n := by rw [← mul_assoc, hen]
  have hnnn : n * (n * n) = 0 := by rwa [← mul_assoc]
  constructor <;> noncomm_ring [he, hen, hne, henn, hnnn]

end HarmonicArtin.GaussianCancellation

end OAI

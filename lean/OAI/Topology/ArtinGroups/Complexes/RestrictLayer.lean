import Mathlib
import OAI.Topology.ArtinGroups.Quivers.PathZero
import OAI.Topology.ArtinGroups.Complexes.ExtendLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma pathOne_eq_zero {x : Q.Zigzag K} (h : x.arrow = 0) : pathOne Q x = 0 := by
  apply ext
  · rfl
  · exact h
  · rfl

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

def restrictLayer (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (l k : ℤ) : Matrix I J (Q.Zigzag K) →ₗ[K]
      Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K) where
  toFun f i j := f i.val j.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restrictLayer_extend (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)) :
    restrictLayer Q E F l k (extendLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  exact extendLayer_apply Q E F l k f i j

lemma restrictLayer_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homSpace Q E F n v) :
    restrictLayer Q E F l k f ∈ homSpace Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v :=
  ⟨⟨fun i j => hf.1.1 i.val j.val, fun i j => hf.1.2 i.val j.val⟩,
    fun i j => hf.2 i.val j.val⟩

lemma restrictLayer_matrixOne_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (matrixOne Q E.differential * g) =
      (show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * restrictLayer Q E F l k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, pathOne Q (E.differential i.val t) * g t j.val) =
    ∑ t : {i // (E.placement i).level = l}, E.differential i.val t.val * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (E.placement t).level ≠ (E.placement i.val).level := by
      intro he
      exact ht ⟨⟨t, he.trans i.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (E.differential_arrow_level Q hh), MulZeroClass.zero_mul]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => z * g t.val j.val)
      (pathOne_eq_self Q (E.pureLayer_linear Q hE l i t).1
        (E.pureLayer_linear Q hE l i t).2).symm

lemma restrictLayer_mul_matrixOne (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    (g : Matrix I J (Q.Zigzag K)) :
    restrictLayer Q E F l k (g * matrixOne Q F.differential) =
      restrictLayer Q E F l k g * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential) := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, g i.val t * pathOne Q (F.differential t j.val)) =
    ∑ t : {j // (F.placement j).level = k}, g i.val t.val * F.differential t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement j.val).level ≠ (F.placement t).level := by
      intro he
      exact ht ⟨⟨t, he.symm.trans j.property⟩, rfl⟩
    rw [pathOne_eq_zero Q (F.differential_arrow_level Q hh), MulZeroClass.mul_zero]
  · intro t
    exact congrArg (fun z : Q.Zigzag K => g i.val t.val * z)
      (pathOne_eq_self Q (F.pureLayer_linear Q hF k t j).1
        (F.pureLayer_linear Q hF k t j).2).symm

lemma layer_boundary_of_extended_boundary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hlin : LinearMatrix Q f)
    (hf : extendLayer Q E F l k f ∈ homBoundaries Q E F n v) :
    f ∈ homBoundaries Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v := by
  obtain ⟨g, hg, _, he⟩ := linear_boundary_primitive Q E F hE hF n v
    (extendLayer_linear Q E F l k hlin) hf
  refine ⟨restrictLayer Q E F l k g, restrictLayer_homSpace Q E F hE hF l k (n-1) v hg, ?_⟩
  have h := congrArg (restrictLayer Q E F l k) he
  rw [map_sub, map_smul, restrictLayer_matrixOne_mul Q E F hE,
    restrictLayer_mul_matrixOne Q E F hF, restrictLayer_extend] at h
  exact h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI

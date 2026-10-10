import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Dual
import OAI.Topology.ArtinGroups.Quivers.TraceLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def homSpacePairing (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v →ₗ[K] homSpace Q F E (-n) (2-v) →ₗ[K] K where
  toFun f :=
    { toFun := fun g => supertrace Q E (f.val * g.val)
      map_add' g h := by
        change supertrace Q E (f.val * (g.val+h.val)) = _
        rw [Matrix.mul_add, map_add]
      map_smul' r g := by
        change supertrace Q E (f.val * (r • g.val)) = _
        rw [Matrix.mul_smul, map_smul]; rfl }
  map_add' f g := by
    ext h
    change supertrace Q E ((f.val+g.val)*h.val) = _
    rw [Matrix.add_mul, map_add]
    rfl
  map_smul' r f := by
    ext g
    change supertrace Q E ((r • f.val)*g.val) = _
    rw [Matrix.smul_mul, map_smul]
    rfl

omit [DecidableEq A] in
lemma supertrace_mul_single [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (f : Matrix I J (Q.Zigzag K)) (i : I) (j : J)
    (z : Q.Zigzag K) :
    supertrace Q E (f * Matrix.single j i z) =
      cochainSign (K := K) (E.placement i).cochain * trace Q (f i j * z) := by
  unfold supertrace
  change (∑ k, cochainSign (K := K) (E.placement k).cochain *
    trace Q ((f * Matrix.single j i z) k k)) = _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.mul_single_apply_same]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, trace_zero, MulZeroClass.mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

lemma homSpacePairing_separatingLeft (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (f : homSpace Q E F n v) (h : ∀ g, homSpacePairing Q E F n v f g = 0) : f = 0 := by
  classical
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (pathCoordinates Q).injective
  funext p
  change pathCoordinates Q (f.val i j) p = pathCoordinates Q 0 p
  rw [coordinates_zero]
  by_contra hp
  have hcorner := coordinates_corner Q (f.property.1.1 i j) (f.property.1.2 i j) hp
  have hc : (F.placement j).cochain = (E.placement i).cochain + n := by
    by_contra hh
    exact hp (by rw [(f.property.2 i j).1 hh, coordinates_zero])
  have hl : Path.length p = v + (E.placement i).internal - (F.placement j).internal := by
    by_contra hh
    exact hp ((coordinates_homogeneous Q _ _).mp (f.property.2 i j).2 p hh)
  let z := pathBasis Q (K := K) (Path.dual Q p)
  have hz : Matrix.single j i z ∈ homSpace Q F E (-n) (2-v) := by
    constructor
    · apply projectiveEntries_single Q
      · simpa only [z, ← hcorner.2, ← Path.source_dual Q p] using
          pathBasis_left Q (K := K) (Path.dual Q p)
      · simpa only [z, ← hcorner.1, ← Path.target_dual Q p] using
          pathBasis_right Q (K := K) (Path.dual Q p)
    · apply mapDegree_single Q
      · omega
      · have hh := pathBasis_homogeneous Q (K := K) (Path.dual Q p)
        rw [Path.length_dual Q, hl] at hh
        convert hh using 1; omega
  have hh := h ⟨_, hz⟩
  change supertrace Q E (f.val * Matrix.single j i z) = 0 at hh
  rw [supertrace_mul_single Q, ← coordinates_trace Q (f.val i j) p] at hh
  have hs : cochainSign (K := K) (E.placement i).cochain ≠ 0 := by
    intro he
    have := cochainSign_mul_self (K := K) (E.placement i).cochain
    rw [he, MulZeroClass.zero_mul] at this
    exact zero_ne_one this
  exact hp ((mul_eq_zero.mp hh).resolve_left hs)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI

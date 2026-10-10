import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot
import OAI.Topology.ArtinGroups.Quivers.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma projectiveEntries_smul {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    (r : K) (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries Q p q (r • M) := by
  constructor
  · intro i j
    change vertexId Q _ * (r • M i j) = r • M i j
    rw [mul_smul, h.1]
  · intro i j
    change (r • M i j) * vertexId Q _ = r • M i j
    rw [smul_mul, h.2]

lemma mapDegree_smul {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (r : K) (h : MapDegree Q p q n v M) :
    MapDegree Q p q n v (r • M) := by
  intro i j
  exact ⟨fun hc => by change r • M i j = 0; rw [(h i j).1 hc, smul_zero],
    homogeneous_smul Q (h i j).2 r⟩

namespace BasedComplex

variable [Fintype I] [Fintype J]

def homSpace (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) where
  carrier := {f | ProjectiveEntries Q E.placement F.placement f ∧
    MapDegree Q E.placement F.placement n v f}
  zero_mem' := ⟨projectiveEntries_zero Q, mapDegree_zero Q n v⟩
  add_mem' hf hg := ⟨projectiveEntries_add Q hf.1 hg.1, mapDegree_add Q hf.2 hg.2⟩
  smul_mem' r _ hf := ⟨projectiveEntries_smul Q r hf.1, mapDegree_smul Q r hf.2⟩

def cochainSign (n : ℤ) : K := (n.negOnePow.val : K)

lemma cochainSign_zero : cochainSign (K := K) 0 = 1 := by
  simp [cochainSign]

lemma cochainSign_add_one (n : ℤ) : cochainSign (K := K) (n + 1) = -cochainSign n := by
  simp [cochainSign, Int.negOnePow_add]

lemma cochainSign_add (n m : ℤ) :
    cochainSign (K := K) (n + m) = cochainSign n * cochainSign m := by
  simp [cochainSign, Int.negOnePow_add]

lemma cochainSign_neg (n : ℤ) : cochainSign (K := K) (-n) = cochainSign n := by
  simp only [cochainSign, Int.negOnePow_neg]

lemma cochainSign_mul_self (n : ℤ) : cochainSign (K := K) n * cochainSign n = 1 := by
  conv_lhs => lhs; rw [← cochainSign_neg (K := K) n]
  rw [← cochainSign_add, neg_add_cancel, cochainSign_zero]

noncomputable def homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f := E.differential * f - cochainSign (K := K) n • (f * F.differential)
  map_add' f g := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r f := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    simp only [RingHom.id_apply]
    rw [smul_comm]

lemma homDifferential_mem (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homSpace Q E F n v) :
    homDifferential Q E F n f ∈ homSpace Q E F (n + 1) v := by
  change ProjectiveEntries Q E.placement F.placement
      (E.differential * f - cochainSign (K := K) n • (f * F.differential)) ∧
    MapDegree Q E.placement F.placement (n + 1) v
      (E.differential * f - cochainSign (K := K) n • (f * F.differential))
  rw [sub_eq_add_neg]
  constructor
  · exact projectiveEntries_add Q (projectiveEntries_mul Q E.entries hf.1)
      (projectiveEntries_neg Q (projectiveEntries_smul Q _
        (projectiveEntries_mul Q hf.1 F.entries)))
  · have h₁ := mapDegree_mul Q E.degree hf.2
    have h₂ := mapDegree_mul Q hf.2 F.degree
    simp only [zero_add, add_zero] at h₁ h₂
    rw [add_comm 1 n] at h₁
    exact mapDegree_add Q h₁ (mapDegree_neg Q (mapDegree_smul Q _ h₂))

lemma homDifferential_square_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E F (n + 1) (homDifferential Q E F n f) = 0 := by
  change E.differential * (E.differential * f - cochainSign n • (f * F.differential)) -
    cochainSign (n + 1) • ((E.differential * f - cochainSign n • (f * F.differential)) *
      F.differential) = 0
  have h₁ : E.differential * (E.differential * f) = 0 := by
    rw [← Matrix.mul_assoc, E.square_zero, Matrix.zero_mul]
  have h₂ : (f * F.differential) * F.differential = 0 := by
    rw [Matrix.mul_assoc, F.square_zero, Matrix.mul_zero]
  rw [cochainSign_add_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    h₁, h₂, neg_smul, smul_zero, sub_zero, zero_sub, Matrix.mul_assoc]
  abel

noncomputable def gradedHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q E F n v →ₗ[K] homSpace Q E F (n + 1) v :=
  (homDifferential Q E F n).restrict
    (fun _ hf => homDifferential_mem Q E F n v hf)

lemma homSpace_pure_total_degree_lower (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (h : n + v < k - l) : homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra he
  have hh := mapDegree_level_bound Q hf.2 he
  rw [hE i, hF j] at hh
  omega

lemma homSpace_pure_total_degree_upper (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (h : k - l + 2 < n + v) : homSpace Q E F n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  by_contra he
  have hc : (F.placement j).cochain = (E.placement i).cochain + n := by
    by_contra hc
    exact he ((hf.2 i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (hf.2 i j).2 he
  have he' := hE i
  have hf' := hF j
  dsimp only [GeneratorPlacement.level] at he' hf'
  omega

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI

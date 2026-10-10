import OAI.RepresentationTheory.Saxl.StaircaseSign

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma subrepProject_subtype {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) (x : S) :
    subrepProject S hS x.val = x := by
  change (subrepSelfDual S hS).symm (subrepSelfDual S hS x) = x
  exact (subrepSelfDual S hS).symm_apply_apply x

def wordTensorEquiv (n d e : ℕ) :
    ((wordRep n d).tprod (wordRep n e)).Equiv (wordRep n (d*e)) where
  toLinearEquiv := wordTensor n d e
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

def ambientSignMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (wordRep (staircase m).card ((staircase m).colLen 0))
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0))) :=
  (signTwistMap (spechtInclusion (stairRowTableau m))).comp
    (φ.toIntertwiningMap.comp (subrepProject (spechtSub (stairTableau m))
      (fun _ hx => cyclic_star _ (polytabloid_real _) hx)))

lemma ambientSignMap_subtype (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x : Specht (stairTableau m)) : ambientSignMap m φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub (stairTableau m)) _ x.val)).val = _
  exact congrArg (fun y : Specht (stairTableau m) => (φ y).val)
    (subrepProject_subtype (spechtSub (stairTableau m)) _ x)

def pairAntiMap (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap
      (signTwist (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)))
      (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorEquiv _ _ _).toIntertwiningMap.comp
    ((tensorAnti (wordRep _ _) (ambientSignMap m φ)).comp
      (signTwistMap (wordTensorEquiv _ _ _).symm.toIntertwiningMap))

lemma pairAntiMap_tensor (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x y : WordSpace (staircase m).card ((staircase m).colLen 0)) :
    pairAntiMap m φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] ambientSignMap m φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id (ambientSignMap m φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_staircase (m : ℕ) :
    letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
    ∑ g : columnGroup (stairRowTableau m), signC g.val •
      wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) g.val (staircaseWord m) =
    wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  change _ = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ]
    (∑ g : columnGroup (stairRowTableau m),
      spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (stairRowTableau m)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid (stairTableau m))) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_smul, signC_mul_self, one_smul]
  rfl

def dominatedQuotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Representation.IntertwiningMap (signTwist (staircaseCyclic m).toRepresentation)
      (wordRep (staircase m).card ((staircase m).colLen 0)) :=
  (orbitProjection (repeatedTarget m)).comp ((pairSumMap _ _ _).comp
    ((pairAntiMap m φ).comp (signTwistMap
      { toLinearMap := (staircaseCyclic m).toSubmodule.subtype
        isIntertwining' := fun _ => rfl })))

/- The exact staircase permutation generator occurs in the image of the
sign-twisted cyclic staircase module, with no Young-rule input. -/
theorem repeatedTarget_in_quotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  obtain ⟨c,hc,hφ⟩ := signEquiv_rowAverage m φ
  let x : (staircaseCyclic m).toSubmodule := ∑ g : columnGroup (stairRowTableau m), signC g.val •
    (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
    change (∑ g : columnGroup (stairRowTableau m), signC g.val •
      (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_staircase m
  let q : ℂ := (Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val
  have hq : q ≠ 0 := by
    apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne')
    intro hz
    have hh := signC_mul_self (rowReversal m).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hF : dominatedQuotient m φ x = (c*q) • Pi.single (repeatedTarget m) (1:ℂ) := by
    change orbitProjection (repeatedTarget m) (pairSumMap _ _ _ (pairAntiMap m φ x.val)) = _
    rw [hx, pairAntiMap_tensor, ambientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul, map_smul, map_smul, staircase_repeated_projection, smul_smul]
  have hm : (c*q) • Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range :=
    ⟨x,hF⟩
  exact (Submodule.smul_mem_iff _ (mul_ne_zero hc hq)).mp hm

end Saxl

end

end OAI

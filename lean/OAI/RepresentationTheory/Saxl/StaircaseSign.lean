import OAI.RepresentationTheory.Saxl.RepeatedProjection

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

def rowReversalCell (m : ℕ) (x : (staircase m).cells) : (staircase m).cells :=
  ⟨(x.val.1, m-1-x.val.1-x.val.2), by
    have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    apply mem_staircase.mpr
    omega⟩

lemma rowReversalCell_involutive (m : ℕ) : Function.Involutive (rowReversalCell m) := by
  intro x
  have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change m-1-x.val.1-(m-1-x.val.1-x.val.2) = x.val.2
    omega

def rowReversalEquiv (m : ℕ) : Equiv.Perm (staircase m).cells :=
  ⟨rowReversalCell m, rowReversalCell m, rowReversalCell_involutive m, rowReversalCell_involutive m⟩

def rowReversal (m : ℕ) : columnGroup (stairRowTableau m) :=
  ⟨((stairTableau m).trans (rowReversalEquiv m)).trans (stairTableau m).symm, by
    intro i
    change (stairTableau m ((stairTableau m).symm (rowReversalEquiv m (stairTableau m i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def repeatedTarget (m : ℕ) : Fin (staircase m).card → Fin ((staircase m).colLen 0) :=
  fun i => Fin.rev (rowWord (stairTableau m) i)

lemma repeatedTarget_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) (i) :
    repeatedTarget m (g.val i) = repeatedTarget m i := by
  apply congrArg Fin.rev
  apply Fin.ext
  exact g.property i

lemma repeated_letters_injective (m : ℕ) :
    Function.Injective (fun i => (repeatedTarget m i, rowWord (stairRowTableau m) i)) := by
  intro i j he
  apply (stairTableau m).injective
  apply Subtype.ext
  apply Prod.ext
  · have hh : Fin.rev (rowWord (stairTableau m) i) = Fin.rev (rowWord (stairTableau m) j) :=
      congrArg Prod.fst he
    exact congrArg Fin.val (Fin.rev_injective hh)
  · exact congrArg Fin.val (congrArg Prod.snd he)

lemma repeated_complement (m : ℕ) (i) :
    (rowWord (stairRowTableau m) i).val +
      (rowWord (stairRowTableau m) ((rowReversal m).val i)).val =
      (repeatedTarget m i).val := by
  have hi : (stairTableau m i).val.1 + (stairTableau m i).val.2 < m :=
    mem_staircase.mp (stairTableau m i).property
  simp only [rowWord, stairRowTableau, rowReversal, Equiv.trans_apply,
    Equiv.apply_symm_apply, repeatedTarget, Fin.val_rev, staircase_colLen, Nat.sub_zero]
  change (stairTableau m i).val.2 + (m-1-(stairTableau m i).val.1-(stairTableau m i).val.2) =
    m-((stairTableau m i).val.1+1)
  omega

theorem staircase_repeated_projection (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) =
      ((Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val) •
        Pi.single (repeatedTarget m) 1 := by
  exact repeated_alt_projection (columnGroup (stairRowTableau m))
    (rowWord (stairRowTableau m)) (repeatedTarget m) (rowReversal m)
    (repeatedTarget_fixed m) (repeated_letters_injective m) (repeated_complement m)

lemma staircase_repeated_projection_nonzero (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) ≠ 0 := by
  rw [staircase_repeated_projection]
  apply smul_ne_zero
  · apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne'
    · intro hh
      have he := signC_mul_self (rowReversal m).val
      rw [hh, zero_mul] at he
      exact zero_ne_one he
  · intro hz
    have he := congrFun hz (repeatedTarget m)
    simp at he


theorem staircase_sign_equiv (m : ℕ) :
    Nonempty ((spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) := by
  classical
  let t := stairTableau m
  let tt := stairRowTableau m
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin (staircase m).card) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin (staircase m).card), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep (staircase m).card ((staircase m).colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin (staircase m).card)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin (staircase m).card)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep (staircase m).card ((staircase m).colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin (staircase m).card)) •
        wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

lemma alternating_specht_line {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (y : Specht t) (hy : ∀ g : columnGroup t,
      spechtRep t g.val y = signC g.val • y) :
    ∃ c : ℂ, y.val = c • polytabloid t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  have he : columnAlt t y.val = (Fintype.card (columnGroup t) : ℂ) • y.val := by
    change (∑ g : columnGroup t, signC g.val • wordRep n (μ.colLen 0) g.val) y.val = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hh (g : columnGroup t) : wordRep n (μ.colLen 0) g.val y.val = signC g.val • y.val :=
      congrArg Subtype.val (hy g)
    simp only [hh, smul_smul, signC_mul_self, one_smul, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hm := columnAlt_tabloid t (spechtSub_le_tabloidSub t y.property)
  rw [he] at hm
  have hc : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx : y.val ∈ Submodule.span ℂ {polytabloid t} :=
    (Submodule.smul_mem_iff _ hc).mp hm
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c,hc.symm⟩

def rowAverage (m : ℕ) : Specht (stairTableau m) := by
  classical
  letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
  exact ∑ g : columnGroup (stairRowTableau m),
    spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩

lemma rowAverage_nonzero (m : ℕ) : rowAverage m ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  intro he
  have hh := congrArg (fun y : Specht (stairTableau m) => y.val (rowWord (stairTableau m))) he
  have hg (g : columnGroup (stairRowTableau m)) :
      rowWord (stairTableau m) ∘ g.val = rowWord (stairTableau m) := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [rowAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (stairRowTableau m),
    polytabloid (stairTableau m) (rowWord (stairTableau m) ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma rowAverage_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) :
    spechtRep (stairTableau m) g.val (rowAverage m) = rowAverage m := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  unfold rowAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (stairRowTableau m) =>
    spechtRep (stairTableau m) h.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩)

lemma signEquiv_rowAverage (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (rowAverage m)).val = c • polytabloid (stairRowTableau m) := by
  have ha (g : columnGroup (stairRowTableau m)) :
      spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) = signC g.val • φ (rowAverage m) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (rowAverage m)
    change φ (spechtRep (stairTableau m) g.val (rowAverage m)) =
      signC g.val • spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) at he
    rw [rowAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (stairRowTableau m) (φ (rowAverage m)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply rowAverage_nonzero m
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

def signTwistMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (signTwist ρ) (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC g • ρ g x) = signC g • σ g (f x)
    rw [map_smul, f.isIntertwining]

/- A sign intertwiner in the second factor twists the diagonal product. -/
def tensorAnti {n : ℕ} {X : Type uX} {Y : Type uY} {Z : Type uZ} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (f : Representation.IntertwiningMap σ (signTwist τ)) :
    Representation.IntertwiningMap (signTwist (ρ.tprod σ)) (ρ.tprod τ) where
  toLinearMap := TensorProduct.map LinearMap.id f.toLinearMap
  isIntertwining' g := by
    ext x y
    change TensorProduct.map LinearMap.id f.toLinearMap
      (signC g • (ρ g x ⊗ₜ[ℂ] σ g y)) = ρ g x ⊗ₜ[ℂ] τ g (f y)
    rw [map_smul, TensorProduct.map_tmul]
    change signC g • (ρ g x ⊗ₜ[ℂ] f (σ g y)) = _
    rw [f.isIntertwining]
    change signC g • (ρ g x ⊗ₜ[ℂ] (signC g • τ g (f y))) = _
    rw [TensorProduct.tmul_smul, smul_smul, signC_mul_self, one_smul]

end Saxl

end

end OAI

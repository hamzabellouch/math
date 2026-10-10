import OAI.RepresentationTheory.Saxl.SizedStrips

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Place the smaller tableau on any chosen block, with the remaining strip
colors on its complement. No transitivity or induction rule is assumed. -/
theorem placed_strip_restriction {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  classical
  obtain ⟨c,F,hF,hcb,hcz,hcount,hFe⟩ := stripChain_restriction_any hs s t
  let i := tableauInclusion s t hs.le
  let l : Fin a → Fin n := fun j => e.symm (Sum.inl j)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair l i
    (fun x y h => Sum.inl.inj (e.symm.injective h)) i.injective
  have hcL (j : Fin a) : c (p (e.symm (Sum.inl j))) = 0 := by
    rw [show p (e.symm (Sum.inl j)) = i j from hp j]
    exact (hcz _).mpr ⟨j,rfl⟩
  have hcRpos (j : Fin b) : 0 < c (p (e.symm (Sum.inr j))) := by
    by_contra hn
    have hz : c (p (e.symm (Sum.inr j))) = 0 := by omega
    obtain ⟨k,hk⟩ := (hcz _).mp hz
    have hh : e.symm (Sum.inl k) = e.symm (Sum.inr j) := p.injective ((hp k).trans hk)
    have := e.symm.injective hh
    cases this
  let cb : Fin b → Fin bs.length := fun j => ⟨c (p (e.symm (Sum.inr j)))-1, by
    have := hcRpos j
    have := hcb (p (e.symm (Sum.inr j)))
    omega⟩
  have hcR (j : Fin b) : c (p (e.symm (Sum.inr j))) = (cb j).val+1 := by
    have := hcRpos j
    change _ = (c (p (e.symm (Sum.inr j)))-1)+1
    omega
  let F' := F.comp (spechtRep t p)
  have hP : Function.Surjective (spechtRep t p) := by
    intro x
    refine ⟨spechtRep t p⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨cb,F',hF.comp hP, ?_⟩
  intro h q hq x
  let g := p * sumPerm e h q * p⁻¹
  have hgL (j : Fin a) : g (p (e.symm (Sum.inl j))) = p (e.symm (Sum.inl (h j))) := by
    simp [g]
  have hgR (j : Fin b) : g (p (e.symm (Sum.inr j))) = p (e.symm (Sum.inr (q j))) := by
    simp [g]
  have hgc (j : Fin n) : c (g j) = c j := by
    obtain ⟨z,rfl⟩ := p.surjective j
    obtain ⟨z,rfl⟩ := e.symm.surjective z
    cases z with
    | inl j => rw [hgL,hcL,hcL]
    | inr j =>
      rw [hgR,hcR,hcR]
      exact congrArg (fun x : Fin bs.length => x.val+1) (congrFun hq j)
  have hgi (j : Fin a) : g (i j) = i (h j) := by rw [← hp j,← hp (h j)]; exact hgL j
  change F (spechtRep t p (spechtRep t (sumPerm e h q) x)) = spechtRep s h (F (spechtRep t p x))
  have hmul : p * sumPerm e h q = g * p := by simp [g,mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
  exact hFe g h hgc hgi _

end Saxl

namespace Saxl

/- Required support transfer from a genuine iterated horizontal-strip
restriction and genuine independent high/band cyclic factors. -/
theorem strip_product_support {n a b d : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (f : Representation.IntertwiningMap (spechtRep s) (cyclic (wordRep a d) v).toRepresentation)
    (hf : f ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau b η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r) (cyclic (wordRep b d) u).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  classical
  obtain ⟨c,F,hF,hFe⟩ := placed_strip_restriction hs s t e
  let G := (subrepInclusion (cyclic (wordRep a d) v)).comp f
  let F₀ : Specht t →ₗ[ℂ] WordSpace a d := G.toLinearMap.comp F
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    apply Subtype.ext
    exact LinearMap.congr_fun hz x
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change G (F (spechtRep t (sumPerm e 1 q) x)) = G (F x)
    rw [hFe 1 q hq, map_one]
    rfl
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = wordRep a d h (F₀ x) := by
    change G (F (spechtRep t (sumPerm e h 1) x)) = wordRep a d h (G (F x))
    rw [hFe h 1 rfl]
    exact LinearMap.congr_fun (G.isIntertwining' h) (F x)
  let T := bandOrbitMap e (spechtRep t) c F₀
  have hTm (x : Specht t) (w : Fin b → Fin bs.length) : T x w ∈ cyclic (wordRep a d) v := by
    change (∑ g : Equiv.Perm (Fin b), _) ∈ (cyclic (wordRep a d) v).toSubmodule
    apply Submodule.sum_mem
    intro g hg
    apply Submodule.smul_mem
    exact (f (F (spechtRep t (sumPerm e 1 g⁻¹) x))).property
  obtain ⟨L,hL,hLe,hLm,hLs⟩ := bandGlue_sector_exists e (spechtRep t) v u A hv hu hband T
    (bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb)
    (bandOrbitMap_equivariant e (spechtRep t) (wordRep a d) c F₀ hFa) hTm
  apply sector_support_transfer (spechtRep t) (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L hL _ hLm
  · intro x w hw
    by_contra hn
    exact hw (hLs x w hn)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g := sumPerm_restrictions e g'
    rw [← heq]
    exact hLe _ _ x

end Saxl

end

end OAI

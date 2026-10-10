import OAI.RepresentationTheory.Saxl.SpechtSubmodule

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
def subrepPairMap {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap S.toRepresentation S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x.val y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    ext x y
    exact wordPair_move g x.val y.val

lemma subrepPairMap_injective {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Function.Injective (subrepPairMap S) := by
  classical
  apply (subrepPairMap S).toLinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hh : subrepPairMap S x = 0 := hx
  have hz : dotProduct x.val (star x.val) = 0 :=
    congrArg (fun f : Module.Dual ℂ S.toSubmodule => f ⟨star x.val, hS x.val x.property⟩) hh
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  exact Subtype.ext (dotProduct_self_star_eq_zero.mp hz)

/- Complex conjugation-stable invariant word subspaces are canonically self-dual
via bilinear evaluation, yielding equivariant projections. -/
def subrepSelfDual {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.Equiv S.toRepresentation S.toRepresentation.dual :=
  (subrepPairMap S).ofBijective
    ⟨subrepPairMap_injective S hS,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ℂ) (V := S.toSubmodule)).symm).mp (subrepPairMap_injective S hS)⟩

/- Actual self-duality of every complex Specht representation. -/
def spechtSelfDual {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.Equiv (spechtRep t) (spechtRep t).dual :=
  subrepSelfDual (spechtSub t) (fun _ hx => cyclic_star _ (polytabloid_real t) hx)

/- Restriction of the ambient bilinear coordinate pairing to an invariant subspace. -/
def subrepPairFromAmbient {n d : ℕ} (S : Subrepresentation (wordRep n d)) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation.dual where
  toLinearMap :=
    { toFun := fun x =>
        { toFun := fun y => dotProduct x y.val
          map_add' := by intro y z; exact dotProduct_add _ _ _
          map_smul' := by intro a y; exact dotProduct_smul a _ _ }
      map_add' := by intro x y; ext z; exact add_dotProduct _ _ _
      map_smul' := by intro a x; ext z; exact smul_dotProduct a _ _ }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact wordPair_move g x y.val

/- The genuine equivariant orthogonal-coordinate projection. -/
def subrepProject {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) :
    Representation.IntertwiningMap (wordRep n d) S.toRepresentation :=
  (subrepSelfDual S hS).symm.toIntertwiningMap.comp (subrepPairFromAmbient S)

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
def wordMap {n d e : ℕ} (L : Fin d → Fin e → ℂ) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) where
  toLinearMap :=
    { toFun := fun x b => ∑ a, x a * ∏ i, L (a i) (b i)
      map_add' := by
        intro x y
        ext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext b
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
          RingHom.id_apply] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext b
    change (∑ a, x (a ∘ g) * ∏ i, L (a i) (b i)) =
      ∑ a, x a * ∏ i, L (a i) (b (g i))
    apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n d g)
      (fun a => x a * ∏ i, L (a i) (b (g i))))
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [wordPerm]
    congr 1
    exact (Equiv.prod_comp g (fun i => L (a i) (b i))).symm

@[simp] lemma wordMap_single {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    wordMap L (Pi.single a 1) b = ∏ i, L (a i) (b i) := by
  classical
  simp [wordMap, Pi.single_apply]

/- A nonzero contraction with a real cyclic vector gives an actual nonzero
intertwiner into its cyclic representation. -/
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

end Saxl

end

end OAI

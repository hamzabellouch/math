import OAI.RepresentationTheory.Saxl.YoungRule

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

def equivOfSubrepEq {G : Type uG} {X : Type uX} [Group G] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} (S T : Subrepresentation ρ) (h : S = T) :
    Representation.Equiv S.toRepresentation T.toRepresentation := by
  subst T
  exact Representation.Equiv.refl _

/- Positive Young rule as a concrete orbit map (including reordered contents). -/
theorem young_orbit_map {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
    (hc : τ.card = θ.card) (hd : Dominates τ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
      F (Pi.single w 1) ≠ 0 := by
  classical
  have hn : τ.card = n := by
    have hh := Fintype.card_congr t
    simpa using hh.symm
  subst n
  obtain ⟨a,l,hl,hac,hle⟩ := young_invariant_functional θ τ hc hd
  obtain ⟨y,hy,hye⟩ := vector_of_invariant_functional (shapeTableau τ) a l hl hle
  let a' := e ∘ a
  have ha' : ∀ g : Equiv.Perm (Fin τ.card), a' ∘ g = a' →
      spechtRep (shapeTableau τ) g y = y := by
    intro g hg
    apply hye g
    funext i
    exact e.injective (congrFun hg i)
  let F := orbitAverage (spechtRep (shapeTableau τ)) a' y
  have hF : F (Pi.single a' 1) ≠ 0 := by
    rw [show F (Pi.single a' 1) = _ from orbitAverage_base _ a' y ha']
    apply smul_ne_zero _ hy
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1, by simp⟩
  have hcnt (j : Fin (θ.colLen 0)) :
      (Finset.univ.filter (fun i => w i = j)).card =
        (Finset.univ.filter (fun i => a' i = j)).card := by
    have haeq : Finset.univ.filter (fun i => a' i = j) =
        Finset.univ.filter (fun i => a i = e.symm j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact e.eq_symm_apply.symm
    rw [haeq, hac]
    simpa only [Equiv.apply_symm_apply] using hw (e.symm j)
  obtain ⟨g,hg⟩ := perm_of_equal_content w a' hcnt
  have hwF : F (Pi.single w 1) ≠ 0 := by
    have hw' : Pi.single w (1:ℂ) = wordRep τ.card (θ.colLen 0) g⁻¹ (Pi.single a' 1) := by
      rw [wordRep_single, inv_inv, hg]
    rw [hw', F.isIntertwining]
    intro hz
    apply hF
    have hh := congrArg (spechtRep (shapeTableau τ) g) hz
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at hh
    exact hh
  let E := equivOfSubrepEq (spechtSub (shapeTableau τ)) (spechtSub t)
    (spechtSub_tableau_independent _ _)
  refine ⟨E.toIntertwiningMap.comp F, ?_⟩
  intro hz
  exact hwF (E.injective (hz.trans (map_zero _).symm))



def intertwiningRangeEquiv {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ρ.Equiv f.range.toRepresentation where
  toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hf
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (f.isIntertwining' g) x

def staircaseCyclicInclusion (m : ℕ) :
    Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      ((staircaseTensorMap m).range.toRepresentation) where
  toLinearMap := Submodule.inclusion (staircaseCyclic_le_tensorRange m)
  isIntertwining' _ := rfl

def intertwiningLiftSubrep {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Representation.IntertwiningMap S.toRepresentation ρ := by
  let e : ρ.Equiv f.range.toRepresentation := intertwiningRangeEquiv f hf
  let i : Representation.IntertwiningMap S.toRepresentation f.range.toRepresentation :=
    { toLinearMap := Submodule.inclusion hS, isIntertwining' := fun _ => rfl }
  exact e.symm.toIntertwiningMap.comp i

lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

attribute [irreducible] intertwiningLiftSubrep

/- The genuine cyclic module is embedded in the actual staircase Specht square. -/
def staircaseToTensor (m : ℕ) :
    Representation.IntertwiningMap (staircaseCyclic m).toRepresentation
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) :=
  @intertwiningLiftSubrep (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

attribute [irreducible] staircaseToTensor

lemma staircaseToTensor_injective (m : ℕ) : Function.Injective (staircaseToTensor m) := by
  unfold staircaseToTensor
  exact @intertwiningLiftSubrep_injective (Equiv.Perm (Fin (staircase m).card))
    (Specht (stairTableau m) ⊗[ℂ] Specht (stairTableau m))
    (WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    _ _ _ _ _
    ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0))
    (staircaseTensorMap m) (staircaseTensorMap_injective m)
    (staircaseCyclic m) (staircaseCyclic_le_tensorRange m)

/- Every Specht type occurs in the specified staircase cyclic module. -/
def CyclicSaxlConjecture : Prop :=
  ∀ m, 1 ≤ m → ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
    ∃ f : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      (staircaseCyclic m).toRepresentation, f ≠ 0

/- A proof of cyclic support proves the original Kronecker-multiplicity target. -/
theorem saxl_of_cyclic_support (h : CyclicSaxlConjecture) : SaxlConjecture := by
  intro m hm μ hμ
  apply (kronecker_pos_iff _ _ _).mpr
  obtain ⟨f, hf⟩ := h m hm μ hμ
  refine ⟨(staircaseToTensor m).comp f, ?_⟩
  intro he
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply staircaseToTensor_injective m
  exact (congrArg (fun F : Representation.IntertwiningMap (spechtRep (canonicalTableau μ hμ))
      ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m))) => F x) he).trans
    (map_zero _).symm

end Saxl

end

end OAI

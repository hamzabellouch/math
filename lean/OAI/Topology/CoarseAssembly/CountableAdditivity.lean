import OAI.Topology.CoarseAssembly.ClopenRestriction
import Mathlib.Topology.Constructions

namespace OAI

/-! # Countable additivity in the first KK variable

The coordinate maps below are the proved extension-by-zero restrictions
on actual Fredholm-module groups. The sole published input is their
bijectivity: Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998),
Theorem 19.7.1, for a countable disjoint union of compact metrizable spaces.
Construction of a family class and vanishing from vanishing coordinates
are consequences, not assumed inputs.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)]

def sigmaComponent (j : ℕ) : Y j ↪ Sigma Y := ⟨Sigma.mk j, sigma_mk_injective⟩

theorem sigmaComponent_open (j : ℕ) : IsOpenEmbedding (sigmaComponent Y j) :=
  IsOpenEmbedding.sigmaMk

variable [∀ j, CompactSpace (Y j)] [∀ j, T2Space (Y j)]

def sigmaCoordinates : LocallyFiniteK1 (Sigma Y) →+ (∀ j, LocallyFiniteK1 (Y j)) where
  toFun a j := restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j) a
  map_zero' := by funext j; exact map_zero _
  map_add' a b := by funext j; exact map_add _ _ _

/-- The exact countable-additivity specialization used in this application.
This is a published input on a specified family of spaces. -/
def CountableAdditivityInput : Prop := Function.Bijective (sigmaCoordinates Y)

def sigmaKKEquiv (h : CountableAdditivityInput Y) :
    LocallyFiniteK1 (Sigma Y) ≃+ (∀ j, LocallyFiniteK1 (Y j)) :=
  AddEquiv.ofBijective (sigmaCoordinates Y) h

/-- Assemble an integral family before any tensoring with the rationals. -/
def familyClass (h : CountableAdditivityInput Y) (a : ∀ j, LocallyFiniteK1 (Y j)) :
    LocallyFiniteK1 (Sigma Y) := (sigmaKKEquiv Y h).symm a

@[simp] theorem familyClass_coordinate (h : CountableAdditivityInput Y)
    (a : ∀ j, LocallyFiniteK1 (Y j)) (j : ℕ) :
    restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j)
      (familyClass Y h a) = a j := by
  exact congrFun ((sigmaKKEquiv Y h).apply_symm_apply a) j

theorem eq_zero_of_coordinates (h : CountableAdditivityInput Y)
    (a : LocallyFiniteK1 (Sigma Y))
    (ha : ∀ j, restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j) a = 0) :
    a = 0 := by
  apply h.injective
  ext j
  change restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j) a =
    restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j) 0
  rw [ha j, map_zero]

theorem sigma_group_subsingleton (h : CountableAdditivityInput Y)
    [∀ j, Subsingleton (LocallyFiniteK1 (Y j))] :
    Subsingleton (LocallyFiniteK1 (Sigma Y)) := by
  refine ⟨fun a b => h.injective ?_⟩
  ext j
  exact Subsingleton.elim _ _

end CoarseAssembly.Analytic

end

end OAI

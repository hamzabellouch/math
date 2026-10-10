import OAI.RepresentationTheory.Saxl.TableauTransport

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def splitLeft {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin d :=
  fun i => (finProdFinEquiv.symm (w i)).1

def splitRight {n d e : ℕ} (w : Fin n → Fin (d*e)) : Fin n → Fin e :=
  fun i => (finProdFinEquiv.symm (w i)).2

def mergeWords {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) : Fin n → Fin (d*e) :=
  fun i => finProdFinEquiv (a i, b i)

@[simp] lemma splitLeft_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitLeft (mergeWords a b) = a := by ext i; simp [splitLeft, mergeWords]
@[simp] lemma splitRight_merge {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    splitRight (mergeWords a b) = b := by ext i; simp [splitRight, mergeWords]
@[simp] lemma merge_split {n d e : ℕ} (w : Fin n → Fin (d*e)) :
    mergeWords (splitLeft w) (splitRight w) = w := by
  funext i
  exact finProdFinEquiv.apply_symm_apply (w i)

def wordUncurry (n d e : ℕ) :
    ((Fin n → Fin e) → WordSpace n d) ≃ₗ[ℂ] WordSpace n (d*e) where
  toFun f w := f (splitRight w) (splitLeft w)
  invFun z b a := z (mergeWords a b)
  left_inv f := by ext b a; simp
  right_inv z := by ext w; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- Tensor regrouping by positions. -/
def wordTensor (n d e : ℕ) :
    WordSpace n d ⊗[ℂ] WordSpace n e ≃ₗ[ℂ] WordSpace n (d*e) :=
  TensorProduct.piScalarRight ℂ ℂ (WordSpace n d) (Fin n → Fin e) ≪≫ₗ wordUncurry n d e

@[simp] lemma wordTensor_tmul {n d e : ℕ} (x : WordSpace n d) (y : WordSpace n e)
    (w : Fin n → Fin (d*e)) :
    wordTensor n d e (x ⊗ₜ[ℂ] y) w = x (splitLeft w) * y (splitRight w) := by
  change y (splitRight w) • x (splitLeft w) = _
  exact mul_comm _ _

lemma wordTensor_equivariant {n d e : ℕ} (g : Equiv.Perm (Fin n))
    (z : WordSpace n d ⊗[ℂ] WordSpace n e) :
    wordTensor n d e (((wordRep n d).tprod (wordRep n e)) g z) =
      wordRep n (d*e) g (wordTensor n d e z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    ext w
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w = _
    change wordTensor n d e (wordRep n d g x ⊗ₜ[ℂ] wordRep n e g y) w =
      wordTensor n d e (x ⊗ₜ[ℂ] y) (w ∘ g)
    simp only [wordTensor_tmul]
    rfl

def wordTensorIntertwiner (n d e : ℕ) :
    Representation.IntertwiningMap ((wordRep n d).tprod (wordRep n e)) (wordRep n (d*e)) where
  toLinearMap := (wordTensor n d e).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    exact wordTensor_equivariant g z

end Saxl

namespace Saxl

/- Transposition is an honest permutation of the self-conjugate staircase. -/
def staircaseSwap (m : ℕ) : (staircase m).cells ≃ (staircase m).cells where
  toFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  invFun x := ⟨(x.val.2, x.val.1), by
    have h : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev stairTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  canonicalTableau (staircase m) rfl

def stairRowTableau (m : ℕ) : Tableau (staircase m).card (staircase m) :=
  (stairTableau m).trans (staircaseSwap m)

def staircaseWord (m : ℕ) : WordSpace (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) :=
  wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))

def staircaseCyclic (m : ℕ) : Subrepresentation
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  cyclic (wordRep _ _) (staircaseWord m)

def spechtInclusion {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) where
  toLinearMap := (spechtSub t).toSubmodule.subtype
  isIntertwining' _ := rfl

def staircaseTensorMap (m : ℕ) :
    Representation.IntertwiningMap ((spechtRep (stairTableau m)).tprod (spechtRep (stairTableau m)))
    (wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp
    ((spechtInclusion (stairTableau m)).tensor (spechtInclusion (stairTableau m)))

lemma staircaseTensorMap_injective (m : ℕ) : Function.Injective (staircaseTensorMap m) := by
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective
    (spechtSub (stairTableau m)).toSubmodule.subtype_injective

lemma staircaseCyclic_le_tensorRange (m : ℕ) :
    staircaseCyclic m ≤ (staircaseTensorMap m).range := by
  apply (cyclic_le _ _ _).mpr
  refine ⟨(⟨polytabloid (stairRowTableau m), polytabloid_mem_all _ _⟩ : Specht (stairTableau m)) ⊗ₜ[ℂ]
    (⟨polytabloid (stairTableau m), mem_cyclic _ _⟩ : Specht (stairTableau m)), ?_⟩
  rfl

attribute [irreducible] staircaseTensorMap

end Saxl

end

end OAI

import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomSpacePairing

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance zigzagFiniteDimensional : FiniteDimensional K (Q.Zigzag K) :=
  (pathBasis Q (K := K)).finiteDimensional_of_finite

lemma homSpacePairing_separatingRight (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (g : homSpace Q F E (-n) (2-v))
    (h : ∀ f, homSpacePairing Q E F n v f g = 0) : g = 0 := by
  apply homSpacePairing_separatingLeft Q F E (-n) (2-v) g
  intro f
  have hf : f.val ∈ homSpace Q E F n v := by
    simpa only [neg_neg, sub_sub_cancel] using f.property
  have hh := h ⟨f.val, hf⟩
  change supertrace Q E (f.val * g.val) = 0 at hh
  change supertrace Q F (g.val * f.val) = 0
  rw [supertrace_mul Q E F hf.2 g.val, hh, MulZeroClass.mul_zero]

instance homSpacePairing_perfect (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    (homSpacePairing Q E F n v).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro f hf
    change f = 0
    apply homSpacePairing_separatingLeft Q E F n v f
    intro g
    exact LinearMap.congr_fun hf g
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro g hg
    change g = 0
    apply homSpacePairing_separatingRight Q E F n v g
    intro f
    exact LinearMap.congr_fun hg f

noncomputable def homSpaceDuality (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homSpace Q F E (-n) (2-v) ≃ₗ[K] Module.Dual K (homSpace Q E F n v) :=
  (homSpacePairing Q E F n v).flip.toPerfPair

lemma homSpaceDuality_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (g : homSpace Q F E (-n) (2-v)) (f : homSpace Q E F n v) :
    homSpaceDuality Q E F n v g f = supertrace Q E (f.val * g.val) := rfl

lemma homSpace_finrank_dual (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    Module.finrank K (homSpace Q F E (-n) (2-v)) = Module.finrank K (homSpace Q E F n v) :=
  (homSpaceDuality Q E F n v).finrank_eq.trans Subspace.dual_finrank_eq

omit [DecidableEq A] in

lemma homDifferential_adjoint (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q E (homDifferential Q E F (n-1) f * g) =
      cochainSign (K := K) n * supertrace Q E (f * homDifferential Q F E (-n) g) := by
  have hcyc := supertrace_mul Q E E E.degree (f*g)
  have hs := cochainSign_mul_self (K := K) n
  have hn : cochainSign (K := K) (n-1) = -cochainSign n := by
    have hh := cochainSign_add_one (K := K) (n-1)
    rw [sub_add_cancel] at hh
    linear_combination hh
  change supertrace Q E ((E.differential*f - cochainSign (K := K) (n-1) • (f*F.differential))*g) =
    cochainSign (K := K) n * supertrace Q E (f*(F.differential*g - cochainSign (K := K) (-n) • (g*E.differential)))
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    map_sub, map_sub, map_smul, map_smul]
  change supertrace Q E (E.differential*f*g) - cochainSign (K := K) (n-1) *
    supertrace Q E (f*F.differential*g) = cochainSign (K := K) n *
    (supertrace Q E (f*(F.differential*g)) - cochainSign (K := K) (-n) *
    supertrace Q E (f*(g*E.differential)))
  rw [cochainSign_neg, hn, Matrix.mul_assoc f F.differential g,
    Matrix.mul_assoc E.differential f g]
  have h1 : cochainSign (K := K) 1 = -1 := by
    simpa only [zero_add, cochainSign_zero] using cochainSign_add_one (K := K) 0
  rw [h1, neg_one_mul, Matrix.mul_assoc] at hcyc
  have hh : supertrace Q E (E.differential*(f*g)) = -supertrace Q E (f*(g*E.differential)) := by
    linear_combination hcyc
  rw [hh]
  linear_combination (supertrace Q E (f*(g*E.differential))) * hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI

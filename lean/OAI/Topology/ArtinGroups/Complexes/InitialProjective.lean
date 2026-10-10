import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.HomDimension

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def initialProjective (α : V) : BasedComplex Q (K := K) PUnit where
  placement _ := ⟨α, 0, 0⟩
  differential := 0
  entries := projectiveEntries_zero Q
  degree := mapDegree_zero Q 1 0
  square_zero := Matrix.zero_mul _

omit [DecidableEq A] in
lemma homDimension_le_homSpace {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ Module.finrank K (homSpace Q E F n v) := by
  apply le_trans (Submodule.finrank_quotient_le _)
  exact Submodule.finrank_mono inf_le_left

omit [Fintype V] [DecidableEq A] in
lemma initial_homSpace_nonzero_cochain (α β : V) (n v : ℤ) (hn : n ≠ 0) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  apply (hf.2 i j).1
  change (0 : ℤ) ≠ 0 + n
  omega

omit [DecidableEq A] in
lemma initial_homSpace_orthogonal {α β : V} (h : OrthogonalVertices Q α β) (n v : ℤ) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q β) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  have he := sum_cornerPath Q (f i j) (hf.1.1 i j) (hf.1.2 i j)
  have hz : ∑ p : CornerPath Q α β, pathCoordinates Q (f i j) p.val • pathBasis Q (K := K) p.val = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact (no_corner_of_orthogonal Q h p).elim
  exact he.symm.trans hz

lemma initial_self_entry_decomposition (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) :
    f i j = (f i j).vertex α • vertexId Q α + (f i j).token α • tokenBasis Q α :=
  diagonal_corner_decomposition Q hn α (f i j) (hf.1.1 i j) (hf.1.2 i j)

omit [Fintype V] [DecidableEq A] in
lemma initial_self_entry_homogeneous (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) : Homogeneous Q v (f i j) := by
  simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2

lemma initial_homSpace_other_internal (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (hv₀ : v ≠ 0) (hv₂ : v ≠ 2) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q α) n v = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply Matrix.ext
  intro i j
  rw [initial_self_entry_decomposition Q hn α n v hf i j]
  have hh := initial_self_entry_homogeneous Q α n v hf i j
  rw [hh.1 hv₀, hh.2.2 hv₂]
  simp only [Pi.zero_apply, zero_smul, add_zero, Matrix.zero_apply]

noncomputable def initialCoordinate (α : V) (n v : ℤ) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q α) n v →ₗ[K] K where
  toFun f := if v = 0 then (f.val PUnit.unit PUnit.unit).vertex α
    else (f.val PUnit.unit PUnit.unit).token α
  map_add' f g := by split_ifs <;> rfl
  map_smul' r f := by split_ifs <;> rfl

lemma initialCoordinate_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) : Function.Injective (initialCoordinate Q (K := K) α n v) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change (initialCoordinate Q α n v) f = 0 at hf
  change f = 0
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hi : i = PUnit.unit := Subsingleton.elim _ _
  have hj : j = PUnit.unit := Subsingleton.elim _ _
  subst i
  subst j
  rw [initial_self_entry_decomposition Q hn α n v f.property PUnit.unit PUnit.unit]
  have hh := initial_self_entry_homogeneous Q α n v f.property PUnit.unit PUnit.unit
  by_cases hv : v = 0
  · have hzero : (f.val PUnit.unit PUnit.unit).vertex α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hv] using hf
    rw [hzero, hh.2.2 (by omega)]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl
  · have hzero : (f.val PUnit.unit PUnit.unit).token α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hv] using hf
    rw [hzero, hh.1 hv]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl

lemma initial_homDimension_le_one (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q α) n v ≤ 1 := by
  apply le_trans (homDimension_le_homSpace Q _ _ n v)
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective
    (initialCoordinate_injective Q (K := K) hn α n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI

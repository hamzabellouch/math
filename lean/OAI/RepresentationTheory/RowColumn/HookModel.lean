import OAI.RepresentationTheory.RowColumn.SignedWords

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

abbrev Color (h : ℕ) := Fin h ⊕ Fin h

def IsOdd {h : ℕ} : Color h → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

def template (x : Cell μ) : Color h :=
  if hx : row x < h then Sum.inl ⟨row x, hx⟩
  else Sum.inr ⟨col x, (H x.1 x.2).resolve_left hx⟩

lemma template_parity (x : Cell μ) : IsOdd (template μ h H x) ↔ h ≤ row x := by
  unfold template
  split_ifs <;> simp_all [IsOdd]
  omega

lemma template_row {x y : Cell μ} (he : template μ h H x = template μ h H y)
    (hx : row x < h) : row x = row y := by
  by_cases hy : row y < h
  · simp only [template, dite_eq_left hx, dite_eq_left hy] at he
    exact congrArg Fin.val (Sum.inl.inj he)
  · simp only [template, dite_eq_left hx, dite_eq_right hy] at he
    cases he

lemma template_col {x y : Cell μ} (he : template μ h H x = template μ h H y)
    (hx : h ≤ row x) : col x = col y := by
  have hn : ¬ row x < h := by omega
  by_cases hy : row y < h
  · simp only [template, dite_eq_right hn, dite_eq_left hy] at he
    cases he
  · simp only [template, dite_eq_right hn, dite_eq_right hy] at he
    exact congrArg Fin.val (Sum.inr.inj he)

abbrev oddCount := Fintype.card {x : Cell μ // IsOdd (template μ h H x)}

def templateWord : Words (S := Cell μ) (IsOdd (h := h)) (oddCount μ h H) :=
  ⟨template μ h H, rfl⟩

lemma row_preserved (r : CubeShuffle.Specht.rowGroup μ) (x : Cell μ) : row (r.1 x) = row x :=
  congrArg Fin.val (r.2 x)

/-- The nonzero coefficient of the Young symmetrizer is protected from sign
cancellation: surviving row motions fix bottom cells, and column motions fix
all top cells. -/
lemma template_rigidity (c : colGroup μ) (r : CubeShuffle.Specht.rowGroup μ)
    (hw : actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H) :
    (∀ x : Cell μ, row x < h → c.1 x = x) ∧
    (∀ x : Cell μ, h ≤ row x → r.1 x = x) := by
  have ht (x : Cell μ) : template μ h H (c.1 (r.1 x)) = template μ h H x :=
    word_stabilizer_eq _ _ hw x
  constructor
  · intro y hy
    let x := r.1⁻¹ y
    have hr : r.1 x = y := r.1.apply_symm_apply y
    have hx : row x < h := by
      have hh := row_preserved μ r x
      rw [hr] at hh
      omega
    apply Subtype.ext
    apply Prod.ext
    · change row (c.1 y) = row y
      have he := template_row μ h H (ht x).symm hx
      have hh := row_preserved μ r x
      rw [hr] at he hh
      exact he.symm.trans hh.symm
    · exact c.2 y
  · intro x hx
    apply Subtype.ext
    apply Prod.ext
    · exact row_preserved μ r x
    · change col (r.1 x) = col x
      have he := template_col μ h H (ht x).symm hx
      exact (c.2 (r.1 x)).symm.trans he.symm

lemma template_row_stabilized (r : CubeShuffle.Specht.rowGroup μ)
    (hr : ∀ x : Cell μ, h ≤ row x → r.1 x = x) :
    actWord r.1 (templateWord μ h H) = templateWord μ h H := by
  apply Subtype.ext
  funext x
  change template μ h H (r.1⁻¹ x) = template μ h H x
  have he : row (r.1⁻¹ x) = row x := row_preserved μ r⁻¹ x
  by_cases hx : row x < h
  · have hy : row (r.1⁻¹ x) < h := by omega
    simp only [template, dite_eq_left hx, dite_eq_left hy]
    exact congrArg Sum.inl (Fin.ext he)
  · have hy : h ≤ row (r.1⁻¹ x) := by omega
    have hh := hr (r.1⁻¹ x) hy
    simpa using congrArg (template μ h H) hh.symm

lemma template_young_sign (c : colGroup μ) (r : CubeShuffle.Specht.rowGroup μ)
    (hw : actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H) :
    permSign c.1 * permSign (oddPerm (c.1 * r.1) (templateWord μ h H)) = 1 := by
  obtain ⟨hc, hr⟩ := template_rigidity μ h H c r hw
  have hrw := template_row_stabilized μ h H r hr
  have hcw : actWord c.1 (templateWord μ h H) = templateWord μ h H := by
    rwa [actWord_mul, hrw] at hw
  have hro : oddPerm r.1 (templateWord μ h H) = 1 := by
    apply oddPerm_of_odd_fixed _ _ hrw
    intro x hx
    exact hr x ((template_parity μ h H x).mp hx)
  have hco : permSign (oddPerm c.1 (templateWord μ h H)) = permSign c.1 := by
    apply oddPerm_sign_of_stabilizes _ _ hcw
    intro x hx
    apply hc x
    have hh : ¬ h ≤ row x := fun he => hx ((template_parity μ h H x).mpr he)
    omega
  rw [oddPerm_mul, hrw, hro, mul_one, hco]
  exact permSign_sq c.1

end RowColumn.HookModel

namespace RowColumn
open CubeShuffle.Specht

section YoungMap
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (μ : YoungDiagram) (ρ : Representation ℂ (Equiv.Perm (Cell μ)) V) (v : V)

/-- The actual orbit sum giving the map out of the tabloid permutation module.
It is unnormalized, which is harmless for testing nonzero Young symmetrizers. -/
def tabloidOrbitMap : (Tabloid μ → ℂ) →ₗ[ℂ] V where
  toFun f := ∑ g : Equiv.Perm (Cell μ), f (tabloidAct g (baseTabloid μ)) • ρ g v
  map_add' := by
    intro f h
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

lemma tabloidOrbitMap_intertwines (g : Equiv.Perm (Cell μ)) (f : Tabloid μ → ℂ) :
    tabloidOrbitMap μ ρ v (tabloidRep μ g f) = ρ g (tabloidOrbitMap μ ρ v f) := by
  change (∑ h, f (tabloidAct g⁻¹ (tabloidAct h (baseTabloid μ))) • ρ h v) =
    ρ g (∑ h, f (tabloidAct h (baseTabloid μ)) • ρ h v)
  rw [map_sum]
  simp only [map_smul]
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro h
  simp only [Equiv.coe_mulLeft, tabloidAct_mul, Equiv.Perm.mul_apply,
    map_mul, Module.End.mul_apply]
  congr 1
  have hh : ρ g (ρ g⁻¹ (ρ h v)) = ρ h v := by
    change (ρ g * ρ g⁻¹) (ρ h v) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  exact hh.symm

lemma tabloidOrbitMap_delta_base :
    tabloidOrbitMap μ ρ v (delta (baseTabloid μ)) = symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v := by
  have hmem (g : Equiv.Perm (Cell μ)) :
      tabloidAct g (baseTabloid μ) = baseTabloid μ ↔ g ∈ CubeShuffle.Specht.rowGroup μ := by
    rw [← tabloid_stabilizer]
    rfl
  change (∑ g : Equiv.Perm (Cell μ),
    (if tabloidAct g (baseTabloid μ) = baseTabloid μ then (1 : ℂ) else 0) • ρ g v) = _
  simp only [hmem, ite_smul, one_smul, zero_smul]
  simp only [symmetrizer, LinearMap.sum_apply]
  change _ = ∑ g : CubeShuffle.Specht.rowGroup μ, ρ g.1 v
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro g; simp) (fun g => ρ g v)

lemma tabloidOrbitMap_polytabloid :
    tabloidOrbitMap μ ρ v (polytabloid μ) =
      alternator (colGroup μ) ρ (symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v) := by
  rw [polytabloid_formula, map_sum]
  simp only [map_smul, alternator, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [← tabloidRep_delta, tabloidOrbitMap_intertwines, tabloidOrbitMap_delta_base]

/-- Restricting the orbit map to the already constructed, proved irreducible
Specht module. -/
def youngIntertwiner : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ) ρ where
  toLinearMap := (tabloidOrbitMap μ ρ v).comp (space μ).subtype
  isIntertwining' g := by
    ext f
    exact tabloidOrbitMap_intertwines μ ρ v g f.1

/-- A nonvanishing actual column-alternator/row-symmetrizer vector supplies an
embedding; no Littlewood--Richardson occurrence statement is assumed. -/
theorem youngIntertwiner_injective
    (hn : alternator (colGroup μ) ρ (symmetrizer (CubeShuffle.Specht.rowGroup μ) ρ v) ≠ 0) :
    Function.Injective (youngIntertwiner μ ρ v) := by
  let := representation_irreducible μ
  rcases Representation.IsIrreducible.injective_or_eq_zero (youngIntertwiner μ ρ v) with hi | hz
  · exact hi
  · exfalso
    apply hn
    have he := congrArg (fun F : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ) ρ =>
      F ⟨polytabloid μ, polytabloid_mem_space μ⟩) hz
    change tabloidOrbitMap μ ρ v (polytabloid μ) = 0 at he
    rwa [tabloidOrbitMap_polytabloid] at he

end YoungMap
end RowColumn

namespace RowColumn.HookModel
open scoped BigOperators Classical
open CubeShuffle.Specht RowColumn.Signed

variable (μ : YoungDiagram) (h : ℕ) (H : RowColumn.InHook μ h)

abbrev hookRepresentation :=
  Signed.representation (S := Cell μ) (odd := IsOdd (h := h)) (k := oddCount μ h H)

def youngVector : EuclideanSpace ℂ (Words (S := Cell μ) (IsOdd (h := h)) (oddCount μ h H)) :=
  alternator (colGroup μ) (hookRepresentation μ h H)
    (symmetrizer (CubeShuffle.Specht.rowGroup μ) (hookRepresentation μ h H)
      (wordVector (templateWord μ h H)))

lemma youngVector_coefficient : youngVector μ h H (templateWord μ h H) =
    ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℂ) else 0 := by
  unfold youngVector
  simp only [alternator, symmetrizer, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  change permSign c.1 * ((hookRepresentation μ h H c.1 * hookRepresentation μ h H r.1)
    (wordVector (templateWord μ h H))) (templateWord μ h H) = _
  rw [← map_mul]
  change permSign c.1 * Signed.representation (c.1 * r.1)
    (wordVector (templateWord μ h H)) (templateWord μ h H) = _
  rw [wordVector_coefficient]
  split_ifs with he
  · exact template_young_sign μ h H c r he
  · exact mul_zero _

lemma youngVector_nonzero : youngVector μ h H ≠ 0 := by
  have he : (youngVector μ h H (templateWord μ h H)).re =
      ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℝ) else 0 := by
    rw [youngVector_coefficient]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> rfl
  have hp : 0 < ∑ c : colGroup μ, ∑ r : CubeShuffle.Specht.rowGroup μ,
      if actWord (c.1 * r.1) (templateWord μ h H) = templateWord μ h H then (1 : ℝ) else 0 := by
    apply Finset.sum_pos'
    · intro c _
      exact Finset.sum_nonneg (fun r _ => by split_ifs <;> norm_num)
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro r _
        split_ifs <;> norm_num
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        simp
  intro hz
  rw [hz] at he
  change 0 = _ at he
  linarith

/-- Explicit signed-slot realization of every (h,h)-hook Specht module.
The target, action, and intertwiner are concrete; no LR/Schur-Weyl occurrence
axiom is used. This supplies the first necessary step of weighted.tex:88–93. -/
def hookEmbedding : Representation.IntertwiningMap (CubeShuffle.Specht.representation μ)
    (hookRepresentation μ h H) :=
  RowColumn.youngIntertwiner μ (hookRepresentation μ h H) (wordVector (templateWord μ h H))

theorem hookEmbedding_injective : Function.Injective (hookEmbedding μ h H) :=
  RowColumn.youngIntertwiner_injective μ (hookRepresentation μ h H)
    (wordVector (templateWord μ h H)) (youngVector_nonzero μ h H)

end RowColumn.HookModel

end

end OAI

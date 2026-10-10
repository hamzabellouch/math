import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.HarmonicExtension

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
open Matrix
open scoped Classical

def PositiveSupportComponent {ι : Type*} (C : Matrix ι ι ℝ)
    (v : ι → ℝ) (I : Set ι) : Prop :=
  I.Nonempty ∧ (∀ i ∈ I, 0 < v i) ∧
    (∀ i j : I, Relation.ReflTransGen (fun a b : I => C a b < 0) i j) ∧
    ∀ i ∈ I, ∀ j, C i j < 0 → 0 < v j → j ∈ I

def harmonicPositiveSign {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (o : ι) (p : ℕ →₀ (ι → ℝ)) (k : ℕ) (i : ι) : Prop :=
  0 < k ∧ ∃ I : Set ι, i ∈ I ∧ o ∉ I ∧ PositiveSupportComponent C (p k) I ∧
    (∀ j ∈ I, (C *ᵥ p k) j = 0) ∧
    ∀ d, k < d → ∀ j, (j ∈ I ∨ ∃ a ∈ I, C a j < 0) → p d j = 0

def levelIncident {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (k : ℕ) (i : ι) : Prop :=
  0 < p k i ∨ ∃ j, C i j < 0 ∧ 0 < p k j

noncomputable def incidenceIndices {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : Finset ℕ :=
  p.support.filter (fun k => levelIncident C p k i)

noncomputable def incidenceLevel {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : ℕ :=
  (incidenceIndices C p i).sup id

def harmonicActive {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (o : ι) (p : ℕ →₀ (ι → ℝ)) (i : ι) : Prop :=
  let k := incidenceLevel C p i
  0 < (C *ᵥ p k) i ∨
    (C *ᵥ p k) i = 0 ∧ 0 < p k i ∧ ¬harmonicPositiveSign C o p k i

theorem levelIncident_support {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ∈ p.support := by
  rw [Finsupp.mem_support_iff]
  intro hk
  rcases h with h | ⟨j, _, h⟩ <;> simp only [hk, Pi.zero_apply, lt_self_iff_false] at h

theorem levelIncident_mem {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ∈ incidenceIndices C p i :=
  Finset.mem_filter.mpr ⟨levelIncident_support C p h, h⟩

theorem levelIncident_le {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ≤ incidenceLevel C p i :=
  Finset.le_sup (f := id) (levelIncident_mem C p h)

theorem incidenceLevel_incident {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) (h : ∃ k, levelIncident C p k i) :
    levelIncident C p (incidenceLevel C p i) i := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨d, hd, hlevel⟩ := Finset.exists_mem_eq_sup (incidenceIndices C p i)
    ⟨k, levelIncident_mem C p hk⟩ id
  change levelIncident C p ((incidenceIndices C p i).sup id) i
  rw [hlevel]
  exact (Finset.mem_filter.mp hd).2

theorem no_incidence_row_zero {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    {k : ℕ} {i : ι} (hn : ¬levelIncident C p k i) : (C *ᵥ p k) i = 0 := by
  have hi : p k i = 0 := le_antisymm
    (le_of_not_gt (fun h => hn (Or.inl h))) (hp k i)
  change ∑ j, C i j * p k j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · subst j; rw [hi, mul_zero]
  · by_cases hneg : C i j < 0
    · have hj : p k j = 0 := le_antisymm
        (le_of_not_gt (fun h => hn (Or.inr ⟨j, hneg, h⟩))) (hp k j)
      rw [hj, mul_zero]
    · rw [le_antisymm (hOff i j hij) (le_of_not_gt hneg), zero_mul]

theorem harmonic_active_component_posDef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (o : ι)
    (hFrame : ∀ i, i ≠ o → C i o < 0)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i) (hpFrame : 0 < p 0 o)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (G : Set ι) (hGo : o ∉ G)
    (hG : ∀ i ∈ G, i ∈ T ∨ harmonicActive C o p i)
    (hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j) :
    (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef := by
  classical
  by_cases hGT : G ⊆ T
  · exact hT.submatrix (e := fun i : G => (⟨i, hGT i.property⟩ : T))
      (fun a b h => Subtype.ext (congrArg (fun z : T => (z : ι)) h))
  have hGne : G.Nonempty := by
    by_contra hn
    exact hGT (fun i hi => (hn ⟨i, hi⟩).elim)
  let : Nonempty G := ⟨⟨hGne.choose, hGne.choose_spec⟩⟩
  let k := (Finset.univ : Finset G).sup (fun i => incidenceLevel C p i)
  have hmax (i : G) : incidenceLevel C p i ≤ k :=
    Finset.le_sup (f := fun j : G => incidenceLevel C p j) (Finset.mem_univ i)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset G)
    Finset.univ_nonempty (fun i => incidenceLevel C p i)
  have haInc : levelIncident C p k a := by
    rw [show k = incidenceLevel C p a from ha]
    apply incidenceLevel_incident C p a
    exact ⟨0, Or.inr ⟨o, hFrame a (fun e => hGo (e ▸ a.property)), hpFrame⟩⟩
  have hrows (i : G) : 0 ≤ (C *ᵥ p k) i := by
    rcases hG i i.property with hiT | hiAct
    · rw [hHarm k i hiT]
    · by_cases hik : incidenceLevel C p i = k
      · change 0 < (C *ᵥ p (incidenceLevel C p i)) i ∨
          (C *ᵥ p (incidenceLevel C p i)) i = 0 ∧ _ at hiAct
        rw [hik] at hiAct
        rcases hiAct with hpos | ⟨hz, _⟩
        · exact le_of_lt hpos
        · exact le_of_eq hz.symm
      · have hn : ¬levelIncident C p k i := by
          intro h
          exact hik (le_antisymm (hmax i) (levelIncident_le C p h))
        rw [no_incidence_row_zero C hOff p hp hn]
  have hInc : ∃ j, 0 < p k j ∧ (j ∈ G ∨ ∃ i : G, C i j < 0) := by
    rcases haInc with h | ⟨j, haj, hj⟩
    · exact ⟨a, h, Or.inl a.property⟩
    · exact ⟨j, hj, Or.inr ⟨a, haj⟩⟩
  rcases harmonic_support_alternative C hSym hOff G hConn (p k) (hp k)
    hrows hInc with hdef | ⟨hpos, hzero, hboundary⟩
  · exact hdef
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    have hz := hboundary a o hGo (hFrame a (fun e => hGo (e ▸ a.property)))
    rw [hk0] at hz
    exact (ne_of_gt hpFrame) hz
  have hcomponent : PositiveSupportComponent C (p k) G := by
    refine ⟨hGne, fun i hi => hpos ⟨i, hi⟩, hConn, ?_⟩
    intro i hi j hij hj
    by_contra hjG
    exact (ne_of_gt hj) (hboundary ⟨i, hi⟩ j hjG hij)
  have hhigher : ∀ d, k < d → ∀ j,
      (j ∈ G ∨ ∃ a ∈ G, C a j < 0) → p d j = 0 := by
    intro d hd j hj
    apply le_antisymm _ (hp d j)
    apply le_of_not_gt
    intro hjpos
    have hdk : d ≤ k := by
      rcases hj with hjG | ⟨i, hi, hij⟩
      · exact (levelIncident_le C p (Or.inl hjpos)).trans (hmax ⟨j, hjG⟩)
      · exact (levelIncident_le C p (Or.inr ⟨j, hij, hjpos⟩)).trans (hmax ⟨i, hi⟩)
    exact (not_le_of_gt hd) hdk
  have hsign (i : G) : harmonicPositiveSign C o p k i :=
    ⟨hk, G, i.property, hGo, hcomponent, fun j hj => hzero ⟨j, hj⟩, hhigher⟩
  exfalso
  apply hGT
  intro i hi
  rcases hG i hi with hiT | hiAct
  · exact hiT
  · have hik : incidenceLevel C p i = k := le_antisymm (hmax ⟨i, hi⟩)
      (levelIncident_le C p (Or.inl (hpos ⟨i, hi⟩)))
    change 0 < (C *ᵥ p (incidenceLevel C p i)) i ∨
      (C *ᵥ p (incidenceLevel C p i)) i = 0 ∧ _ at hiAct
    rw [hik, hzero ⟨i, hi⟩] at hiAct
    rcases hiAct with himposs | ⟨_, _, hnot⟩
    · exact (lt_irrefl 0 himposs).elim
    · exact (hnot (hsign ⟨i, hi⟩)).elim

theorem matrix_posDef_of_fibers {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i) (f : ι → κ)
    (hblock : ∀ i j, f i ≠ f j → C i j = 0)
    (hdef : ∀ b : κ,
      (C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ).PosDef) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j; exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  have hrow (b : κ) (i : {i // f i = b}) :
      (C *ᵥ x) i = ((C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ) *ᵥ
        (fun j : {i // f i = b} => x j)) i := by
    rw [harmonic_row_split C {i | f i = b} x i]
    have hz : (∑ j : ↥({i | f i = b}ᶜ), C i j * x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hblock i j (fun e => j.property (e.symm.trans i.property)), zero_mul]
    rw [hz, add_zero]
    rfl
  let Q (b : κ) : ℝ :=
    (fun i : {i // f i = b} => x i) ⬝ᵥ
      ((C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ) *ᵥ
        (fun j : {i // f i = b} => x j))
  have hsum : x ⬝ᵥ (C *ᵥ x) = ∑ b, Q b := by
    change (∑ i, x i * (C *ᵥ x) i) = _
    rw [← Fintype.sum_fiberwise f (fun i => x i * (C *ᵥ x) i)]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Q, dotProduct, hrow b]
  have hnonneg (b : κ) : 0 ≤ Q b := by
    simpa only [star_trivial] using
      (hdef b).posSemidef.dotProduct_mulVec_nonneg (fun i : {i // f i = b} => x i)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    apply hx
    funext i
    exact not_ne_iff.mp (fun hi => hn ⟨i, hi⟩)
  have hstrict : 0 < Q (f i) := by
    apply (hdef (f i)).dotProduct_mulVec_pos
    intro hz
    exact hi (congrFun hz ⟨i, rfl⟩)
  rw [hsum]
  exact Finset.sum_pos' (fun b _ => hnonneg b)
    ⟨f i, Finset.mem_univ _, hstrict⟩

theorem matrix_posDef_of_connected {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (hDiag : ∀ i, 0 ≤ C i i)
    (hComp : ∀ G : Set ι,
      (∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j) →
      (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef) : C.PosDef := by
  classical
  let graph : SimpleGraph ι := {
    Adj := fun i j => C i j < 0
    symm := ⟨fun {i j} h => (hSym i j) ▸ h⟩
    loopless := ⟨fun i => not_lt_of_ge (hDiag i)⟩ }
  let : Fintype graph.ConnectedComponent := Fintype.ofFinite _
  apply matrix_posDef_of_fibers C hSym graph.connectedComponentMk
  · intro i j hij
    have hne : i ≠ j := fun e => hij (congrArg graph.connectedComponentMk e)
    apply le_antisymm (hOff i j hne)
    apply le_of_not_gt
    intro hneg
    exact hij (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (G := graph) hneg)
  · intro b
    apply hComp b.supp
    intro i j
    exact (SimpleGraph.reachable_iff_reflTransGen i j).mp
      (b.connected_toSimpleGraph.preconnected i j)

theorem harmonic_active_posDef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (hDiag : ∀ i, 0 ≤ C i i) (o : ι)
    (hFrame : ∀ i, i ≠ o → C i o < 0)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i) (hpFrame : 0 < p 0 o)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (K : Set ι) (hKo : o ∉ K)
    (hK : ∀ i ∈ K, i ∈ T ∨ harmonicActive C o p i) :
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ).PosDef := by
  classical
  apply matrix_posDef_of_connected
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ)
    (fun i j => hSym i j)
    (fun i j hij => hOff i j (fun e => hij (Subtype.ext e))) (fun i => hDiag i)
  intro H hH
  let G : Set ι := {i | ∃ hi : i ∈ K, (⟨i, hi⟩ : K) ∈ H}
  let e : H ≃ G := Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ K) (· ∈ H)
  have hG : ∀ i ∈ G, i ∈ T ∨ harmonicActive C o p i := by
    intro i hi
    obtain ⟨hiK, _⟩ := hi
    exact hK i hiK
  have hGo : o ∉ G := by
    rintro ⟨hoK, _⟩
    exact hKo hoK
  have hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j := by
    intro i j
    have hh := Relation.ReflTransGen.lift
      (r := fun a b : H => C a.val.val b.val.val < 0)
      (p := fun a b : G => C a b < 0) e
      (fun a b hab => show C (e a) (e b) < 0 from hab)
      (e.symm i) (e.symm j) (hH (e.symm i) (e.symm j))
    change Relation.ReflTransGen (fun a b : G => C a b < 0) (e (e.symm i)) (e (e.symm j)) at hh
    simpa only [e.apply_symm_apply] using hh
  have hg := harmonic_active_component_posDef C hSym hOff o hFrame p hp hpFrame T hT
    hHarm G hGo hG hConn
  exact hg.submatrix e.injective

end HarmonicArtin

end OAI

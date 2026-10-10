import OAI.Topology.ArtinGroups.Harmonic.PositiveSupportComponent

namespace OAI

/-!
# Active colors for a relative frame

Section 6.3 of paper 082-03 requires an active-color argument without
universal adjacency of the frame. Null signs are allowed at every recorded
level, including the cutoff. All assertions here are proved from the
Cartan matrix and the finite profile.
-/

namespace HarmonicArtin.ParabolicIntersections

open Matrix

variable {ι : Type*} [Fintype ι]

/-- A closed positive null component, isolated from all higher levels. -/
def relativePositiveSign (C : Matrix ι ι ℝ) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (k : ℕ) (i : ι) : Prop :=
  ∃ I : Set ι, i ∈ I ∧ I ⊆ U ∧ PositiveSupportComponent C (p k) I ∧
    (∀ j ∈ I, (C *ᵥ p k) j = 0) ∧
    ∀ d, k < d → ∀ j, (j ∈ I ∨ ∃ a ∈ I, C a j < 0) → p d j = 0

/-- Active colors at their last recorded incidence. -/
def relativeActive (C : Matrix ι ι ℝ) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : Prop :=
  let k := incidenceLevel C p i
  0 < (C *ᵥ p k) i ∨
    (C *ᵥ p k) i = 0 ∧ 0 < p k i ∧ ¬relativePositiveSign C U p k i

/-- Every connected component formed from a positive definite closed
part and active colors remains positive definite. -/
theorem relative_active_component_posDef
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (G : Set ι) (hU : G ⊆ U)
    (hG : ∀ i ∈ G, i ∈ T ∨ relativeActive C U p i)
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
  have hsome : ∃ i : G, ∃ q, levelIncident C p q i := by
    obtain ⟨i, hi, hiT⟩ := Set.not_subset.mp hGT
    have hact := (hG i hi).resolve_left hiT
    refine ⟨⟨i, hi⟩, incidenceLevel C p i, ?_⟩
    by_contra hn
    have hz := no_incidence_row_zero C hOff p hp hn
    rcases hact with hpos | ⟨_, hpos, _⟩
    · exact (ne_of_gt hpos) hz
    · exact hn (Or.inl hpos)
  have haInc : ∃ i : G, levelIncident C p k i := by
    obtain ⟨i, q, hq⟩ := hsome
    by_cases hk : k = 0
    · have hi : incidenceLevel C p i = 0 := Nat.eq_zero_of_le_zero (hk ▸ hmax i)
      refine ⟨i, ?_⟩
      rw [hk, ← hi]
      exact incidenceLevel_incident C p i ⟨q, hq⟩
    · refine ⟨a, ?_⟩
      rw [show k = incidenceLevel C p a from ha]
      apply incidenceLevel_incident C p a
      by_contra hn
      have hempty : incidenceIndices C p a = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hn ⟨l, (Finset.mem_filter.mp hl).2⟩
      have hz : incidenceLevel C p a = 0 := by
        simp only [incidenceLevel, hempty, Finset.sup_empty, bot_eq_zero]
      exact hk (ha.trans hz)
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
    obtain ⟨a, hinc⟩ := haInc
    rcases hinc with h | ⟨j, haj, hj⟩
    · exact ⟨a, h, Or.inl a.property⟩
    · exact ⟨j, hj, Or.inr ⟨a, haj⟩⟩
  rcases harmonic_support_alternative C hSym hOff G hConn (p k) (hp k)
    hrows hInc with hdef | ⟨hpos, hzero, hboundary⟩
  · exact hdef
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
  have hsign (i : G) : relativePositiveSign C U p k i :=
    ⟨G, i.property, (fun _ hj => hU hj), hcomponent, fun j hj => hzero ⟨j, hj⟩, hhigher⟩
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

theorem relative_active_posDef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (hDiag : ∀ i, 0 ≤ C i i) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (K : Set ι) (hKU : K ⊆ U)
    (hK : ∀ i ∈ K, i ∈ T ∨ relativeActive C U p i) :
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ).PosDef := by
  classical
  apply matrix_posDef_of_connected
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ)
    (fun i j => hSym i j)
    (fun i j hij => hOff i j (fun e => hij (Subtype.ext e))) (fun i => hDiag i)
  intro H hH
  let G : Set ι := {i | ∃ hi : i ∈ K, (⟨i, hi⟩ : K) ∈ H}
  let e : H ≃ G := Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ K) (· ∈ H)
  have hG : ∀ i ∈ G, i ∈ T ∨ relativeActive C U p i := by
    intro i hi
    obtain ⟨hiK, _⟩ := hi
    exact hK i hiK
  have hGU : G ⊆ U := by
    rintro i ⟨hiK, _⟩
    exact hKU hiK
  have hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j := by
    intro i j
    have hh := Relation.ReflTransGen.lift
      (r := fun a b : H => C a.val.val b.val.val < 0)
      (p := fun a b : G => C a b < 0) e
      (fun a b hab => show C (e a) (e b) < 0 from hab)
      (e.symm i) (e.symm j) (hH (e.symm i) (e.symm j))
    change Relation.ReflTransGen (fun a b : G => C a b < 0) (e (e.symm i)) (e (e.symm j)) at hh
    simpa only [e.apply_symm_apply] using hh
  have hg := relative_active_component_posDef C hSym hOff U p hp T hT
    hHarm G hGU hG hConn
  exact hg.submatrix e.injective

end HarmonicArtin.ParabolicIntersections

end OAI

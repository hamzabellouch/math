import OAI.RingTheory.DirectFiniteness.SlabHoleEvents

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

abbrev ShortCandidate := Σ i : Fin 3, Candidate F (F.replacementRegion O) (i.val+3)
abbrev SlabEvent := (Σ v : SlabVariable F, F.LocalHolePair O v) ⊕ F.ShortCandidate O

instance : Fintype (F.ShortCandidate O) := by unfold ShortCandidate; infer_instance
instance : Fintype (F.SlabEvent O) := by unfold SlabEvent; infer_instance

def eventDeps : F.SlabEvent O → Finset (SlabVariable F)
  | .inl p => {p.1}
  | .inr c => c.2.deps F (F.replacementRegion O)

def eventVector : F.SlabEvent O → SlabVariable F → E
  | .inl p => fun _ => (F.localHolePairVector O p.1 p.2).2
  | .inr c => c.2.constraintVector F (F.replacementRegion O)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventDeps_nonempty (i : F.SlabEvent O) : (F.eventDeps O i).Nonempty := by
  cases i with
  | inl p => exact Finset.singleton_nonempty _
  | inr c => exact c.2.deps_nonempty F (F.replacementRegion O)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventDeps_card (i : F.SlabEvent O) : (F.eventDeps O i).card ≤ 4 := by
  cases i with
  | inl p => simp [eventDeps]
  | inr c => exact c.2.deps_card_le_four F (F.replacementRegion O) (by omega) (by omega)

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma eventVector_nonzero (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (i : F.SlabEvent O) (v : SlabVariable F) (hv : v ∈ F.eventDeps O i) :
    F.eventVector O i v ≠ 0 := by
  cases i with
  | inl p => exact F.localHolePairVector_nonzero S O hO p.1 p.2
  | inr c => exact c.2.constraintVector_nonzero F (F.replacementRegion O) v hv

omit [Fintype E] in
lemma holeEvent_load (p : ℝ) (v : SlabVariable F) :
    load (fun z : Σ t : SlabVariable F, F.LocalHolePair O t => {z.1})
      (fun _ => p) v = Fintype.card (F.LocalHolePair O v) * p := by
  rw [load,Fintype.sum_sigma]
  calc
    _ = ∑ slab : SlabVariable F,
        if v = slab then Fintype.card (F.LocalHolePair O slab) * p else 0 := by
      apply Finset.sum_congr rfl
      intro slab _
      change (∑ _ : F.LocalHolePair O slab,
        if v ∈ ({slab} : Finset (SlabVariable F)) then p else 0) = _
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_ite,mul_zero]
      exact ite_congr (propext Finset.mem_singleton) (fun _ => rfl) (fun _ => rfl)
    _ = _ := by rw [Finset.sum_ite_eq,ite_eq_left (Finset.mem_univ v)]

/-- A convenient literal finite arithmetic load bound, prior to specializing q. -/
def slabLoadBound (_F : DirectionFrame Q A R E) (p : ℝ) : ℝ := 100^2*p + ∑ i : Fin 3,
    ((Fintype.card R*(i.val+3)^2*2^(i.val+3)*(100*Fintype.card Q)^2*Fintype.card Q^(i.val+3) : ℕ)*p^2 +
    ((Fintype.card R*Fintype.card Q)*(i.val+3)^4*3^(i.val+3)*(Fintype.card Q*Fintype.card E)*
      (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^(i.val+3) : ℕ)*p^4)

lemma event_load_le (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (p : ℝ) (hp : 0 ≤ p) (v : SlabVariable F) :
    load (F.eventDeps O) (fun i => p^(F.eventDeps O i).card) v ≤
      F.slabLoadBound p := by
  rw [load,Fintype.sum_sum_type]
  simp only [eventDeps,Finset.card_singleton,pow_one]
  change
    load (fun z : Σ t : SlabVariable F, F.LocalHolePair O t => {z.1}) (fun _ => p) v +
    (∑ c : F.ShortCandidate O,
      if v ∈ c.2.deps F (F.replacementRegion O) then p^(c.2.deps F (F.replacementRegion O)).card else 0) ≤ _
  rw [F.holeEvent_load,Fintype.sum_sigma]
  change Fintype.card (F.LocalHolePair O v)*p +
    (∑ i : Fin 3, load (fun c : Candidate F (F.replacementRegion O) (i.val+3) => c.deps F (F.replacementRegion O))
      (fun c => p^(c.deps F (F.replacementRegion O)).card) v) ≤ _
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast F.localHolePair_card S O hO v) hp
  · apply Finset.sum_le_sum
    intro i _
    exact Candidate.load_le F (F.replacementRegion O) (i.val+3)
      (Nat.le_add_left 3 i.val) (Nat.add_le_add_right (Nat.le_of_lt_succ i.isLt) 3)
      (100*Fintype.card Q) (F.generic_region_card S O hO) p v

structure SuccessfulSlabs (P : SlabVariable F → Plane Q E) : Prop where
  holes : ∀ v (p : F.LocalHolePair O v), (F.localHolePairVector O v p).2 ∉ (P v).val
  candidates : ∀ k, 3 ≤ k → k ≤ 5 → ∀ c : Candidate F (F.replacementRegion O) k,
    ∃ v ∈ c.deps F (F.replacementRegion O), c.constraintVector F (F.replacementRegion O) v ∉ (P v).val

lemma exists_eventPlanes [Nonempty (Plane Q E)]
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hp : 0 ≤ inclusionProbability Q E)
    (hload : F.slabLoadBound (inclusionProbability Q E) ≤ 1/16) :
    ∃ P : SlabVariable F → Plane Q E, ∀ i, ∃ v ∈ F.eventDeps O i, F.eventVector O i v ∉ (P v).val := by
  let : MeasurableSpace (Plane Q E) := ⊤
  let : MeasurableSingletonClass (Plane Q E) := ⟨fun _ => trivial⟩
  apply exists_slab_assignment (F.eventDeps O) (F.eventVector O)
  · exact F.eventVector_nonzero S O hO
  · exact F.eventDeps_nonempty O
  · exact F.eventDeps_card O
  · intro v
    convert (F.event_load_le S O hO _ hp v).trans hload using 1
    unfold load
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl

omit [Fintype Q] [Fintype R] [Fintype E] in
lemma successful_of_eventPlanes (P : SlabVariable F → Plane Q E)
    (hP : ∀ i, ∃ v ∈ F.eventDeps O i, F.eventVector O i v ∉ (P v).val) :
    F.SuccessfulSlabs O P := by
  constructor
  · intro v p
    obtain ⟨v',hv',hn⟩ := hP (.inl ⟨v,p⟩)
    have he : v'=v := Finset.mem_singleton.mp hv'
    simpa only [he,eventVector] using hn
  · intro k hk3 hk5 c
    rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with rfl | rfl | rfl
    · exact hP (.inr ⟨0,c⟩)
    · exact hP (.inr ⟨1,c⟩)
    · exact hP (.inr ⟨2,c⟩)

lemma exists_successfulSlabs [Nonempty (Plane Q E)]
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hp : 0 ≤ inclusionProbability Q E)
    (hload : F.slabLoadBound (inclusionProbability Q E) ≤ 1/16) :
    ∃ P : SlabVariable F → Plane Q E, F.SuccessfulSlabs O P := by
  obtain ⟨P,hP⟩ := F.exists_eventPlanes S O hO hp hload
  exact ⟨P,F.successful_of_eventPlanes O P hP⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI

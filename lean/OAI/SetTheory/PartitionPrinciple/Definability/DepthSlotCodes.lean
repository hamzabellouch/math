import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteIterationTraces

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def natSuccessorGraph : ZFSet.{u} :=
  natPresentation.graph natPresentation (fun n => ⟨n.down + 1⟩)

noncomputable def natAddGraph : ZFSet.{u} :=
  (natPresentation.product natPresentation).graph natPresentation
    (fun n => ⟨n.1.down + n.2.down⟩)

noncomputable def natMulGraph : ZFSet.{u} :=
  (natPresentation.product natPresentation).graph natPresentation
    (fun n => ⟨n.1.down * n.2.down⟩)

theorem pair_mem_natSuccessorGraph (a b : Nat) :
    ZFSet.pair (natSetCode a) (natSetCode b) ∈ natSuccessorGraph.{u} ↔ b = a + 1 := by
  change ZFSet.pair (natPresentation.encode ⟨a⟩) (natPresentation.encode ⟨b⟩) ∈
    natPresentation.graph natPresentation (fun n => ⟨n.down + 1⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

theorem pair_mem_natAddGraph (a b c : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode a) (natSetCode b)) (natSetCode c) ∈
      natAddGraph.{u} ↔ c = a + b := by
  change ZFSet.pair ((natPresentation.product natPresentation).encode (⟨a⟩, ⟨b⟩))
    (natPresentation.encode ⟨c⟩) ∈ (natPresentation.product natPresentation).graph
      natPresentation (fun n => ⟨n.1.down + n.2.down⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

theorem pair_mem_natMulGraph (a b c : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode a) (natSetCode b)) (natSetCode c) ∈
      natMulGraph.{u} ↔ c = a * b := by
  change ZFSet.pair ((natPresentation.product natPresentation).encode (⟨a⟩, ⟨b⟩))
    (natPresentation.encode ⟨c⟩) ∈ (natPresentation.product natPresentation).graph
      natPresentation (fun n => ⟨n.1.down * n.2.down⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

theorem natSuccessorGraph_isFunc : ZFSet.IsFunc ZFSet.omega ZFSet.omega natSuccessorGraph.{u} :=
  natPresentation.graph_isFunc natPresentation _

theorem natAddGraph_isFunc :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega natAddGraph.{u} :=
  (natPresentation.product natPresentation).graph_isFunc natPresentation _

theorem natMulGraph_isFunc :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega natMulGraph.{u} :=
  (natPresentation.product natPresentation).graph_isFunc natPresentation _

noncomputable def natAddSection (a : Nat) : ZFSet.{u} :=
  natPresentation.graph natPresentation (fun n => ⟨a + n.down⟩)

theorem natAddSection_eq (a : Nat) :
    natAddSection.{u} a = indexedRelationSection ZFSet.omega ZFSet.omega natAddGraph (natSetCode a) := by
  apply ZFSet.ext
  intro z
  rw [natAddSection, Presentation.mem_graph, mem_indexedRelationSection]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨natSetCode n.down, natPresentation.encode_mem n, natSetCode (a + n.down),
      natPresentation.encode_mem ⟨a + n.down⟩, rfl, (pair_mem_natAddGraph a n.down _).2 rfl⟩
  · rintro ⟨x, hx, y, hy, rfl, entry⟩
    obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode y).1 hy
    have eq := (pair_mem_natAddGraph a b c).1 entry
    exact ⟨⟨b⟩, by simp only [natPresentation, eq]⟩

theorem natIterate_successor (a b : Nat) :
    natIterate (fun n : ULift.{u} Nat => ⟨n.down + 1⟩) ⟨a⟩ b = ⟨a + b⟩ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [natIterate, ih, Nat.add_succ]

theorem natIterate_add (a b : Nat) :
    natIterate (fun n : ULift.{u} Nat => ⟨a + n.down⟩) ⟨0⟩ b = ⟨a * b⟩ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [natIterate, ih, Nat.mul_succ, Nat.add_comm]

def depthSlotIndex (n j : Nat) : Nat := 3 * n + j

theorem depthSlotIndex_lt_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j < depthSlotIndex m k ↔ n < m ∨ (n = m ∧ j < k) := by
  unfold depthSlotIndex
  omega

theorem depthSlotIndex_eq_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j = depthSlotIndex m k ↔ n = m ∧ j = k := by
  unfold depthSlotIndex
  omega

theorem depthSlotIndex_le_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j ≤ depthSlotIndex m k ↔ n < m ∨ (n = m ∧ j ≤ k) := by
  unfold depthSlotIndex
  omega

noncomputable def depthSlotGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ j ∈ natSetCode 3, ∃ k ∈ ZFSet.omega,
    ∃ t ∈ ZFSet.omega, z = ZFSet.pair (ZFSet.pair n j) k ∧
      ZFSet.pair (ZFSet.pair (natSetCode 3) n) t ∈ natMulGraph ∧
      ZFSet.pair (ZFSet.pair t j) k ∈ natAddGraph)
    (ZFSet.prod (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega)

theorem mem_depthSlotGraph (z : ZFSet.{u}) : z ∈ depthSlotGraph ↔
    ∃ n ∈ ZFSet.omega, ∃ j ∈ natSetCode 3, ∃ k ∈ ZFSet.omega,
      ∃ t ∈ ZFSet.omega, z = ZFSet.pair (ZFSet.pair n j) k ∧
        ZFSet.pair (ZFSet.pair (natSetCode 3) n) t ∈ natMulGraph ∧
        ZFSet.pair (ZFSet.pair t j) k ∈ natAddGraph := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨n, hn, j, hj, k, hk, t, ht, rfl, mul, add⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hj⟩, hk⟩,
      n, hn, j, hj, k, hk, t, ht, rfl, mul, add⟩

theorem pair_mem_depthSlotGraph (n j k : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode n) (natSetCode j)) (natSetCode k) ∈ depthSlotGraph.{u} ↔
      j < 3 ∧ k = depthSlotIndex n j := by
  rw [mem_depthSlotGraph]
  constructor
  · rintro ⟨n', _, j', hj, k', _, t, ht, equal, mul, add⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨t, rfl⟩ := (mem_omega_iff_natSetCode t).1 ht
    have product := (pair_mem_natMulGraph 3 n t).1 mul
    have sum := (pair_mem_natAddGraph t j k).1 add
    exact ⟨(natSetCode_mem_iff j 3).1 hj, by simp only [depthSlotIndex, product] at sum ⊢; exact sum⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨natSetCode n, natSetCode_mem_omega n, natSetCode j, (natSetCode_mem_iff j 3).2 hj,
      natSetCode (depthSlotIndex n j), natSetCode_mem_omega _, natSetCode (3 * n),
      natSetCode_mem_omega _, rfl, (pair_mem_natMulGraph 3 n _).2 rfl,
      (pair_mem_natAddGraph (3 * n) j _).2 rfl⟩

theorem depthSlotGraph_eq : depthSlotGraph.{u} =
    (natPresentation.product (natInitialPresentation 3)).graph natPresentation
      (fun p => ⟨depthSlotIndex p.1.down p.2.down.val⟩) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, j, hj, k, hk, _, _, rfl, _⟩ := (mem_depthSlotGraph z).1 hz
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨j, bound, rfl⟩ := (mem_natSetCode j 3).1 hj
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    have equal := ((pair_mem_depthSlotGraph n j k).1 hz).2
    exact ((natPresentation.product (natInitialPresentation 3)).mem_graph natPresentation _ _).2
      ⟨(⟨n⟩, ⟨⟨j, bound⟩⟩), by simp only [Presentation.product, natPresentation, natInitialPresentation, equal]⟩
  · intro hz
    obtain ⟨p, rfl⟩ := ((natPresentation.product (natInitialPresentation 3)).mem_graph natPresentation _ z).1 hz
    exact (pair_mem_depthSlotGraph p.1.down p.2.down.val _).2 ⟨p.2.down.isLt, rfl⟩

theorem depthSlotGraph_function :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega depthSlotGraph.{u} := by
  rw [depthSlotGraph_eq]
  exact (natPresentation.product (natInitialPresentation 3)).graph_isFunc natPresentation _

theorem depthSlotGraph_injection :
    InjectionCode (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega depthSlotGraph.{u} := by
  rw [depthSlotGraph_eq]
  apply (natPresentation.product (natInitialPresentation 3)).graph_injection natPresentation _
  intro p q equal
  have h := (depthSlotIndex_eq_iff p.2.down.isLt q.2.down.isLt).1 (congrArg ULift.down equal)
  exact Prod.ext (ULift.ext _ _ h.1) (ULift.ext _ _ (Fin.ext h.2))

end PartitionPilot.Forcing

end OAI

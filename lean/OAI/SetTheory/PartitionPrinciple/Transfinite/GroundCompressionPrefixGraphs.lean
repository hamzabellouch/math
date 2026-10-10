import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionStampBounds

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def compressionPrefixValue (base limit : ZFSet.{u})
    (prior : ZFSet.{u} → ZFSet.{u}) (stages : Nat → ZFSet.{u}) (final s : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if s ∈ base ∨ s = base then prior s else
    if s = limit then final else
      if witnessed : ∃ n, s = compressionStamp base n then stages witnessed.choose else ∅

variable {base limit : ZFSet.{u}}
variable (prior : ZFSet.{u} → ZFSet.{u}) (stages : Nat → ZFSet.{u}) (final : ZFSet.{u})

theorem compressionPrefixValue_old {s : ZFSet.{u}} (old : s ∈ base ∨ s = base) :
    compressionPrefixValue base limit prior stages final s = prior s := by
  classical
  simp only [compressionPrefixValue, ite_eq_left old]

theorem compressionPrefixValue_stamp {stamps : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) (n : Nat) :
    compressionPrefixValue base limit prior stages final (compressionStamp base n) = stages n := by
  classical
  have notOld : ¬(compressionStamp base n ∈ base ∨ compressionStamp base n = base) :=
    fun h => h.elim (compressionStamp_not_old base n).1 (compressionStamp_not_old base n).2
  have witnessed : ∃ k, compressionStamp base n = compressionStamp base k := ⟨n, rfl⟩
  simp only [compressionPrefixValue, ite_eq_right notOld,
    ite_eq_right (times.stamp_ne_limit n), dite_eq_left witnessed]
  exact congrArg stages ((compressionStamp_injective base witnessed.choose_spec).symm)

theorem compressionPrefixValue_limit {stamps : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) :
    compressionPrefixValue base limit prior stages final limit = final := by
  classical
  have notOld : ¬(limit ∈ base ∨ limit = base) := by
    rintro (member | equal)
    · exact ZFSet.mem_asymm member times.base_mem_limit
    · have member := times.base_mem_limit
      rw [equal] at member
      exact ZFSet.mem_irrefl base member
  simp only [compressionPrefixValue, ite_eq_right notOld, ite_true]

theorem compressionPrefixValue_eq_prior_below {stamps t s : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (old : t ∈ base ∨ t = base) (before : s ∈ t) :
    compressionPrefixValue base limit prior stages final s = prior s := by
  apply compressionPrefixValue_old prior stages final
  apply Or.inl
  rcases old with member | equal
  · exact (ordinalSetProperty_member times.ordinal times.base_mem_limit).1 t member s before
  · exact equal ▸ before

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionPrefixValue_mem {stamps s : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (priorGround : ∀ t, t ∈ base ∨ t = base → prior t ∈ M.sets)
    (stageGround : ∀ n, stages n ∈ M.sets) (finalGround : final ∈ M.sets)
    (cutoff : s ∈ insert limit limit) :
    compressionPrefixValue base limit prior stages final s ∈ M.sets := by
  rcases ZFSet.mem_insert_iff.1 cutoff with equal | before
  · rw [equal, compressionPrefixValue_limit prior stages final times]
    exact finalGround
  · rcases (times.mem_limit_iff s).1 before with member | equal | ⟨n, equal⟩
    · rw [compressionPrefixValue_old prior stages final (Or.inl member)]
      exact priorGround s (Or.inl member)
    · rw [compressionPrefixValue_old prior stages final (Or.inr equal)]
      exact priorGround s (Or.inr equal)
    · rw [equal, compressionPrefixValue_stamp prior stages final times n]
      exact stageGround n

end TransitiveGround

end

open SetFormula
universe u

structure GroundChronologyFields (M : TransitiveGround.{u}) (T : ZFSet.{u}) where
  time_ground : T ∈ M.sets
  bound : ZFSet.{u}
  bound_ground : bound ∈ M.sets
  graph : Fin 5 → ZFSet.{u}
  graph_ground : ∀ j, graph j ∈ M.sets
  function : ∀ j, ZFSet.IsFunc T bound (graph j)

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem graphFunction (j : Fin 5) : FunctionGraphOn T (fields.graph j) :=
  ⟨fields.bound, fields.function j⟩

noncomputable def value (j : Fin 5) (s : ZFSet.{u}) : ZFSet.{u} :=
  (fields.graphFunction j).totalValue s

theorem value_entry (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.pair s (fields.value j s) ∈ fields.graph j :=
  (fields.graphFunction j).totalValue_entry hs

theorem value_eq_of_entry (j : Fin 5) {s x : ZFSet.{u}}
    (entry : ZFSet.pair s x ∈ fields.graph j) : fields.value j s = x :=
  (fields.graphFunction j).totalValue_eq_of_entry entry

theorem value_ground (j : Fin 5) (s : ZFSet.{u}) : fields.value j s ∈ M.sets :=
  (fields.graphFunction j).totalValue_ground M (fields.graph_ground j) s

theorem value_mem_bound (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    fields.value j s ∈ fields.bound :=
  (ZFSet.pair_mem_prod.1 ((fields.function j).1 (fields.value_entry j hs))).2

noncomputable def codeFields : Fin 7 → ZFSet.{u} :=
  Fin.cases T (Fin.cases fields.bound fields.graph)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 6 fields.codeFields

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    fields.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 6 fields.codeFields
    (Fin.cases fields.time_ground (Fin.cases fields.bound_ground fields.graph_ground))

theorem code_eq_iff (other : GroundChronologyFields M T) :
    fields.code = other.code ↔ fields.bound = other.bound ∧ fields.graph = other.graph := by
  constructor
  · intro equal
    have same := nonemptyTupleCode_injective 6 equal
    exact ⟨congrFun same 1, funext (fun j => congrFun same j.succ.succ)⟩
  · rintro ⟨bound, graph⟩
    apply congrArg (nonemptyTupleCode 6)
    funext i
    exact Fin.cases rfl (Fin.cases bound (fun j => congrFun graph j)) i

end GroundChronologyFields

noncomputable def compressionPrefixGraph (base limit old stages stamps final : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair limit final) (graphRestriction (insert base base) old ∪
    relationCompose limit ZFSet.omega (ZFSet.sUnion (ZFSet.sUnion stages))
      (relationConverse ZFSet.omega limit stamps) stages)

theorem compressionPrefixGraph_entries {base limit old stages stamps final s y : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) :
    ZFSet.pair s y ∈ compressionPrefixGraph base limit old stages stamps final ↔
      (s = limit ∧ y = final) ∨
        ((s ∈ base ∨ s = base) ∧ ZFSet.pair s y ∈ old) ∨
          ∃ n, s = compressionStamp base n ∧ ZFSet.pair (natSetCode n) y ∈ stages := by
  rw [compressionPrefixGraph, ZFSet.mem_insert_iff, ZFSet.mem_union,
    ZFSet.pair_inj, pair_mem_graphRestriction, pair_mem_relationCompose]
  constructor
  · rintro (terminal | ⟨entry, old⟩ | ⟨_, _, k, hk, reverse, entry⟩)
    · exact Or.inl terminal
    · exact Or.inr (Or.inl ⟨(ZFSet.mem_insert_iff.1 old).symm, entry⟩)
    · obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
      exact Or.inr (Or.inr ⟨n,
        (times.entries n s).1 ((pair_mem_relationConverse _ _ _ _ _).1 reverse).2.2, entry⟩)
  · rintro (terminal | ⟨old, entry⟩ | ⟨n,rfl,entry⟩)
    · exact Or.inl terminal
    · exact Or.inr (Or.inl ⟨entry, ZFSet.mem_insert_iff.2 old.symm⟩)
    · exact Or.inr (Or.inr ⟨times.stamp_mem_limit n, pair_second_mem_doubleUnion entry,
        natSetCode n, natSetCode_mem_omega n,
        (pair_mem_relationConverse _ _ _ _ _).2 ⟨natSetCode_mem_omega n,
          times.stamp_mem_limit n, (times.entries n _).2 rfl⟩, entry⟩)

theorem compressionPrefixGraph_exact {base limit old stages stamps final : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (prior : ZFSet.{u} → ZFSet.{u}) (finite : Nat → ZFSet.{u})
    (oldEntries : ∀ s, s ∈ base ∨ s = base → ∀ y, ZFSet.pair s y ∈ old ↔ y = prior s)
    (finiteEntries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stages ↔ y = finite n)
    (s y : ZFSet.{u}) :
    ZFSet.pair s y ∈ compressionPrefixGraph base limit old stages stamps final ↔
      s ∈ insert limit limit ∧ y = compressionPrefixValue base limit prior finite final s := by
  rw [compressionPrefixGraph_entries times]
  constructor
  · rintro (⟨rfl,equal⟩ | ⟨before,entry⟩ | ⟨n,rfl,entry⟩)
    · exact ⟨ZFSet.mem_insert _ _, equal.trans (compressionPrefixValue_limit prior finite final times).symm⟩
    · exact ⟨ZFSet.mem_insert_of_mem _ ((times.mem_limit_iff s).2
        (before.elim Or.inl (fun h => Or.inr (Or.inl h)))),
        ((oldEntries s before y).1 entry).trans
          (compressionPrefixValue_old prior finite final before).symm⟩
    · exact ⟨ZFSet.mem_insert_of_mem _ (times.stamp_mem_limit n),
        ((finiteEntries n y).1 entry).trans
          (compressionPrefixValue_stamp prior finite final times n).symm⟩
  · rintro ⟨hs,equal⟩
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · exact Or.inl ⟨rfl,equal.trans (compressionPrefixValue_limit prior finite final times)⟩
    · rcases (times.mem_limit_iff s).1 hs with before | same | ⟨n,rfl⟩
      · exact Or.inr (Or.inl ⟨Or.inl before, (oldEntries s (Or.inl before) y).2
          (equal.trans (compressionPrefixValue_old prior finite final (Or.inl before)))⟩)
      · exact Or.inr (Or.inl ⟨Or.inr same, (oldEntries s (Or.inr same) y).2
          (equal.trans (compressionPrefixValue_old prior finite final (Or.inr same)))⟩)
      · exact Or.inr (Or.inr ⟨n,rfl,(finiteEntries n y).2
          (equal.trans (compressionPrefixValue_stamp prior finite final times n))⟩)

theorem compressionPrefixGraph_function {base limit old stages stamps final : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit)
    (prior : ZFSet.{u} → ZFSet.{u}) (finite : Nat → ZFSet.{u})
    (oldEntries : ∀ s, s ∈ base ∨ s = base → ∀ y, ZFSet.pair s y ∈ old ↔ y = prior s)
    (finiteEntries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stages ↔ y = finite n) :
    FunctionGraphOn (insert limit limit) (compressionPrefixGraph base limit old stages stamps final) := by
  let graph := compressionPrefixGraph base limit old stages stamps final
  have entries := compressionPrefixGraph_exact (final := final) times prior finite oldEntries finiteEntries
  refine ⟨ZFSet.sUnion (ZFSet.sUnion graph), ?_, ?_⟩
  · intro z hz
    have shape : ∃ s y, z = ZFSet.pair s y := by
      rcases ZFSet.mem_insert_iff.1 hz with rfl | member
      · exact ⟨limit,final,rfl⟩
      · rcases ZFSet.mem_union.1 member with left | right
        · obtain ⟨s,_,y,rfl,_⟩ := mem_graphRestriction.1 left
          exact ⟨s,y,rfl⟩
        · obtain ⟨s,_,_,_,y,_,rfl,_,_⟩ := (mem_relationCompose _ _ _ _ _ _).1 right
          exact ⟨s,y,rfl⟩
    obtain ⟨s,y,rfl⟩ := shape
    exact ZFSet.pair_mem_prod.2 ⟨((entries s y).1 hz).1,pair_second_mem_doubleUnion hz⟩
  · intro s hs
    exact ⟨compressionPrefixValue base limit prior finite final s,
      (entries s _).2 ⟨hs,rfl⟩, fun y hy => ((entries s y).1 hy).2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionPrefixGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {base limit old stages stamps final : ZFSet.{u}}
    (hOmega : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hBase : base ∈ M.sets) (hLimit : limit ∈ M.sets) (hOld : old ∈ M.sets)
    (hStages : stages ∈ M.sets) (hStamps : stamps ∈ M.sets) (hFinal : final ∈ M.sets) :
    compressionPrefixGraph base limit old stages stamps final ∈ M.sets := by
  have hBefore := M.insert_mem pairing unions hBase hBase
  have hBound := M.union_mem unions (M.union_mem unions hStages)
  exact M.insert_mem pairing unions (M.orderedPair_mem pairing hLimit hFinal)
    (M.binary_union_mem pairing unions (M.graphRestriction_mem unions separation hBefore hOld)
      (M.relationCompose_mem pairing unions powers separation hLimit hOmega hBound
        (M.relationConverse_mem pairing unions powers separation hOmega hLimit hStamps) hStages))

end TransitiveGround

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}

noncomputable def ofGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (hT : T ∈ M.sets) (graphs : Fin 5 → ZFSet.{u})
    (ground : ∀ j, graphs j ∈ M.sets) (functions : ∀ j, FunctionGraphOn T (graphs j)) :
    GroundChronologyFields M T := by
  let all := graphs 0 ∪ (graphs 1 ∪ (graphs 2 ∪ (graphs 3 ∪ graphs 4)))
  have subset (j : Fin 5) : graphs j ⊆ all := by
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inl hz)) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))))) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))))))) ?_ j
    intro j
    have equal : j = 0 := Fin.eq_zero j
    subst j
    exact fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz)))))))
  refine ⟨hT, ZFSet.sUnion (ZFSet.sUnion all), M.union_mem unions (M.union_mem unions
    (M.binary_union_mem pairing unions (ground 0) (M.binary_union_mem pairing unions (ground 1)
      (M.binary_union_mem pairing unions (ground 2) (M.binary_union_mem pairing unions (ground 3) (ground 4)))))),
    graphs,ground,?_⟩
  intro j
  exact ⟨fun z hz => by
    obtain ⟨x,hx,y,_,rfl⟩ := ZFSet.mem_prod.1 ((functions j).to_isFunc.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx,pair_second_mem_doubleUnion (subset j hz)⟩,
    (functions j).to_isFunc.2⟩

theorem ofGraphs_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (hT : T ∈ M.sets) (graphs : Fin 5 → ZFSet.{u})
    (ground : ∀ j, graphs j ∈ M.sets) (functions : ∀ j, FunctionGraphOn T (graphs j)) :
    (ofGraphs pairing unions hT graphs ground functions).graph = graphs := rfl

end GroundChronologyFields

end PartitionPilot.Forcing

end OAI

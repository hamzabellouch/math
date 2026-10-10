import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologicalBasis

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

noncomputable def heightColumnFiber (S C Q h c : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (ZFSet.prod {c} Q) S (relationConverse S (ZFSet.prod C Q) h)

noncomputable def heightColumnGraph (S C Q h c : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q)

theorem mem_heightColumnFiber (S C Q h c i : ZFSet.{u}) :
    i ∈ heightColumnFiber S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ ∃ q ∈ Q, ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnFiber, mem_relationImage]
  constructor
  · rintro ⟨hi, v, hv, vi⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 hv
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    have rel := (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).1 vi
    exact ⟨hi, (ZFSet.pair_mem_prod.1 rel.2.1).1, q, hq, rel.2.2⟩
  · rintro ⟨hi, hc, q, hq, iq⟩
    exact ⟨hi, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩,
      (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).2
        ⟨hi, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq⟩⟩

theorem pair_mem_heightColumnGraph (S C Q h c i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ heightColumnGraph S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ q ∈ Q ∧ ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, hq, v, hv, iv, vq⟩
    obtain ⟨a, ha, b, _, eq⟩ := (mem_productSecond {c} Q (ZFSet.pair v q)).1 vq
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, (ZFSet.pair_mem_prod.1 hv).1, hq, iv⟩
  · rintro ⟨hi, hc, hq, iq⟩
    exact ⟨hi, hq, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq,
      (mem_productSecond {c} Q _).2 ⟨c, ZFSet.mem_singleton.2 rfl, q, hq, rfl⟩⟩

theorem heightColumnGraph_injection {S C Q h : ZFSet.{u}}
    (height : InjectionCode S (ZFSet.prod C Q) h) (c : ZFSet.{u}) :
    InjectionCode (heightColumnFiber S C Q h c) Q (heightColumnGraph S C Q h c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have shape : z ∈ ZFSet.prod S Q := (ZFSet.mem_sep.1
      (show z ∈ relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q) from hz)).1
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 shape
    obtain ⟨_, hc, _, iq⟩ := (pair_mem_heightColumnGraph S C Q h c i q).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_heightColumnFiber S C Q h c i).2 ⟨hi, hc, q, hq, iq⟩, hq⟩
  · intro i hi
    obtain ⟨hiS, hc, q, hq, iq⟩ := (mem_heightColumnFiber S C Q h c i).1 hi
    refine ⟨q, (pair_mem_heightColumnGraph S C Q h c i q).2 ⟨hiS, hc, hq, iq⟩, ?_⟩
    intro r ir
    have irh := (pair_mem_heightColumnGraph S C Q h c i r).1 ir
    obtain ⟨v, _, unique⟩ := height.function.2 i hiS
    exact (ZFSet.pair_inj.1 ((unique _ irh.2.2.2).trans (unique _ iq).symm)).2
  · intro i j q iq jq
    exact height.injective i j (ZFSet.pair c q)
      ((pair_mem_heightColumnGraph S C Q h c i q).1 iq).2.2.2
      ((pair_mem_heightColumnGraph S C Q h c j q).1 jq).2.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumnFiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnFiber S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationImage_mem separation
    (M.prod_mem pairing unions powers separation singleton hQ) hS
    (M.relationConverse_mem pairing unions powers separation hS
      (M.prod_mem pairing unions powers separation hC hQ) hh)

theorem heightColumnGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnGraph S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationCompose_mem pairing unions powers separation hS
    (M.prod_mem pairing unions powers separation hC hQ) hQ hh
    (M.productSecond_mem pairing unions powers separation singleton hQ)

theorem groundEmbeddable_heightColumnFiber
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c N : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) (hN : N ∈ M.sets)
    (height : InjectionCode S (ZFSet.prod C Q) h) (small : M.groundEmbeddable Q N) :
    M.groundEmbeddable (heightColumnFiber S C Q h c) N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨relationCompose (heightColumnFiber S C Q h c) Q N (heightColumnGraph S C Q h c) f,
    M.relationCompose_mem pairing unions powers separation
      (M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh hc) hQ hN
      (M.heightColumnGraph_mem pairing unions powers separation hS hC hQ hh hc) hf,
    (heightColumnGraph_injection height c).compose code⟩

end TransitiveGround

end



section

open SetRealization
universe u

theorem ordinalSetProperty_mem_compare {T i j : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (hi : i ∈ T) (hj : j ∈ T) :
    i ∈ j ∨ i = j ∨ j ∈ i := by
  obtain ⟨a, rfl⟩ := (ordinalSetProperty_iff i).1 (ordinalSetProperty_member ordinal hi)
  obtain ⟨b, rfl⟩ := (ordinalSetProperty_iff j).1 (ordinalSetProperty_member ordinal hj)
  rcases lt_trichotomy a b with less | eq | greater
  · exact Or.inl ((mem_ordinalCode_iff a b).2 less)
  · exact Or.inr (Or.inl (congrArg ordinalCode eq))
  · exact Or.inr (Or.inr ((mem_ordinalCode_iff b a).2 greater))

theorem ordinalSubset_has_least {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {S : Set ZFSet.{u}} (subset : ∀ i ∈ S, i ∈ T) (inhabited : S.Nonempty) :
    ∃ i ∈ S, ∀ j ∈ S, i = j ∨ i ∈ j := by
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases ordinalSetProperty_mem_compare ordinal (subset i hi) (subset j hj) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim (minimal j hj h)

noncomputable def ordinalIndexTail (S i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun j => i = j ∨ i ∈ j) S

theorem mem_ordinalIndexTail (S i j : ZFSet.{u}) :
    j ∈ ordinalIndexTail S i ↔ j ∈ S ∧ (i = j ∨ i ∈ j) := ZFSet.mem_sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem ordinalIndexTail_mem (separation : SeparationSchema M.sets)
    {S i : ZFSet.{u}} (hS : S ∈ M.sets) (hi : i ∈ M.sets) :
    ordinalIndexTail S i ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (.disj (.equal 1 0) (.mem 1 0))
    (extend i Fin.elim0) (Fin.cases hi (fun j => Fin.elim0 j)) hS
  simpa only [BoundedFormula.truth_disj, BoundedFormula.Truth, extend, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, ordinalIndexTail] using selected

theorem groundCountable_descending_heights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S T C Q h : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (subset : S ⊆ T)
    (ordinal : ordinalSetProperty T) (height : InjectionCode S (ZFSet.prod C Q) h)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (antitone : ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d r,
      ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d r) ∈ h →
        d = c ∨ d ∈ c) :
    M.groundEmbeddable S ZFSet.omega := by
  classical
  have hOmega := M.omega_mem separation infinite
  have tails : ∀ c, ∀ i ∈ S, ∀ q, ZFSet.pair i (ZFSet.pair c q) ∈ h →
      M.groundEmbeddable (ordinalIndexTail S i) ZFSet.omega := by
    intro c
    induction c using ZFSet.inductionOn with
    | h c ih =>
      intro i hi q iq
      have hc := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iq)).2).1
      have groundTail := M.ordinalIndexTail_mem separation hS (M.transitive hS hi)
      have groundFiber := M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh
        (M.transitive hC hc)
      have smallFiber := M.groundEmbeddable_heightColumnFiber pairing unions powers separation
        hS hC hQ hh (M.transitive hC hc) hOmega height smallQ
      have columnBelow (k : ZFSet.{u}) (hk : k ∈ S) (later : i = k ∨ i ∈ k)
          (d r : ZFSet.{u}) (kr : ZFSet.pair k (ZFSet.pair d r) ∈ h) : d = c ∨ d ∈ c := by
        rcases later with rfl | later
        · obtain ⟨_, _, unique⟩ := height.function.2 i hi
          exact Or.inl (ZFSet.pair_inj.1 ((unique _ kr).trans (unique _ iq).symm)).1
        · exact antitone i hi k hk later c q d r iq kr
      let lower : Set ZFSet.{u} := {j | j ∈ S ∧ (i = j ∨ i ∈ j) ∧
        ∃ d r, d ∈ c ∧ ZFSet.pair j (ZFSet.pair d r) ∈ h}
      by_cases inhabited : lower.Nonempty
      · obtain ⟨j, hj, minimal⟩ := ordinalSubset_has_least ordinal
          (fun k hk => subset hk.1) inhabited
        obtain ⟨hjS, _, d, r, dc, jr⟩ := hj
        have smallLater := ih d dc j hjS r jr
        have smallUnion := M.groundCountable_binary_union pairing unions powers separation
          infinite choice groundFiber (M.ordinalIndexTail_mem separation hS (M.transitive hS hjS))
          smallFiber smallLater
        apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallUnion
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact ZFSet.mem_union.2 (Or.inl
            ((mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩))
        · have klower : k ∈ lower := ⟨hkS, later, e, s, less, kv⟩
          exact ZFSet.mem_union.2 (Or.inr
            ((mem_ordinalIndexTail S j k).2 ⟨hkS, minimal k klower⟩))
      · apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallFiber
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact (mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩
        · exact False.elim (inhabited ⟨k, hkS, later, e, s, less, kv⟩)
  by_cases inhabited : (S.toSet).Nonempty
  · obtain ⟨i, hi, minimal⟩ := ordinalSubset_has_least ordinal (fun _ hx => subset hx) inhabited
    obtain ⟨v, iv, _⟩ := height.function.2 i hi
    obtain ⟨c, _, q, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iv)).2
    exact M.groundEmbeddable_restrict separation hS hOmega
      (fun j hj => (mem_ordinalIndexTail S i j).2 ⟨hj, minimal j hj⟩) (tails c i hi q iv)
  · have empty : S = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨S, hS⟩

end TransitiveGround






def EssentialHeightDescent (E birth height qlt : ZFSet.{u}) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ i j c q d v,
    ZFSet.pair x i ∈ birth → ZFSet.pair y j ∈ birth → i ∈ j →
    ZFSet.pair x (ZFSet.pair c q) ∈ height → ZFSet.pair y (ZFSet.pair d v) ∈ height →
      d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt)

theorem relationCompose_function_of_subset {A B D C f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A B f) (second : ZFSet.IsFunc D C g) (subset : B ⊆ D) :
    ZFSet.IsFunc A C (relationCompose A B C f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨y, xy, uniqueY⟩ := first.2 x hx
  have hy := (ZFSet.pair_mem_prod.1 (first.1 xy)).2
  obtain ⟨z, yz, uniqueZ⟩ := second.2 y (subset hy)
  have hz := (ZFSet.pair_mem_prod.1 (second.1 yz)).2
  refine ⟨z, (pair_mem_relationCompose A B C f g x z).2 ⟨hx, hz, y, hy, xy, yz⟩, ?_⟩
  intro w hw
  obtain ⟨_, _, y', _, xy', y'w⟩ := (pair_mem_relationCompose A B C f g x w).1 hw
  exact uniqueZ w (uniqueY y' xy' ▸ y'w)

theorem essentialHeightComposite_strict {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt)
    {i j c q d v : ZFSet.{u}} (earlier : i ∈ j)
    (first : ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
    (second : ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height) :
    d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt) := by
  obtain ⟨_, _, x, hx, ix, xheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, y, hy, jy, yheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
  have xi := (pair_mem_relationConverse E S birth x i).1 (representatives ix)
  have yj := (pair_mem_relationConverse E S birth y j).1 (representatives jy)
  exact descent x hx y hy i j c q d v xi.2.2 yj.2.2 earlier xheight yheight

theorem essentialHeightComposite_antitone {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt) :
    ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d v,
      ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
      ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
        d = c ∨ d ∈ c := by
  intro i _ j _ earlier c q d v first second
  exact (essentialHeightComposite_strict representatives descent earlier first second).elim
    Or.inr (fun h => Or.inl h.1)

theorem essentialHeightComposite_injection {L S T E C Q birth reps height qlt : ZFSet.{u}}
    (stages : S ⊆ T) (ordinal : ordinalSetProperty T)
    (representatives : ZFSet.IsFunc S E reps)
    (chosenBirths : reps ⊆ relationConverse E S birth)
    (points : E ⊆ L) (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent E birth height qlt) :
    InjectionCode S (ZFSet.prod C Q) (relationCompose S E (ZFSet.prod C Q) reps height) := by
  have function := relationCompose_function_of_subset representatives heights points
  refine ⟨function, ?_⟩
  intro i j z first second
  have iShape := ZFSet.pair_mem_prod.1 (function.1 first)
  have jShape := ZFSet.pair_mem_prod.1 (function.1 second)
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 iShape.2
  have notEarlier (a b : ZFSet.{u})
      (aHeight : ZFSet.pair a (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
      (bHeight : ZFSet.pair b (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height) : a ∉ b := by
    intro earlier
    rcases essentialHeightComposite_strict chosenBirths descent earlier aHeight bHeight with h | h
    · exact ZFSet.mem_irrefl c h
    · exact irreflexive q hq h.2
  have eqI := ordinalSetProperty_eq_code_rank i (ordinalSetProperty_member ordinal (stages iShape.1))
  have eqJ := ordinalSetProperty_eq_code_rank j (ordinalSetProperty_member ordinal (stages jShape.1))
  rcases lt_trichotomy (ZFSet.rank i) (ZFSet.rank j) with earlier | equal | later
  · have ij : i ∈ j := by rw [eqI, eqJ, mem_ordinalCode_iff]; exact earlier
    exact False.elim (notEarlier i j first second ij)
  · exact eqI.trans ((congrArg ordinalCode equal).trans eqJ.symm)
  · have ji : j ∈ i := by rw [eqJ, eqI, mem_ordinalCode_iff]; exact later
    exact False.elim (notEarlier j i second first ji)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_essentialBirthHeights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    ∃ h ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (ZFSet.prod C Q) h ∧
      (∀ i ∈ essentialBirthIndices F T r birth, ∀ j ∈ essentialBirthIndices F T r birth,
        i ∈ j → ∀ c q d v,
          ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d v) ∈ h →
            d = c ∨ d ∈ c) ∧
      ∀ i z, ZFSet.pair i z ∈ h → ∃ x ∈ birthEssentialSet F T r birth,
        ZFSet.pair x i ∈ birth ∧ ZFSet.pair x z ∈ height := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS := M.essentialBirthIndices_mem separation hF hT hr hBirth
  obtain ⟨reps, hReps, function, chosen, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  let h := relationCompose S E (ZFSet.prod C Q) reps height
  have ground : h ∈ M.sets := M.relationCompose_mem pairing unions powers separation hS hE
    (M.prod_mem pairing unions powers separation hC hQ) hReps hHeight
  have subset : S ⊆ T := fun _ hi => (mem_essentialBirthIndices F T r birth _).1 hi |>.1
  have points : E ⊆ L := fun _ hx => positive (birthEssentialSet_subset F T r birth hx)
  refine ⟨h, ground, essentialHeightComposite_injection subset ordinal function chosen points heights
    irreflexive descent, essentialHeightComposite_antitone chosen descent, ?_⟩
  intro i z hiz
  obtain ⟨_, _, x, hx, ix, xz⟩ := (pair_mem_relationCompose S E (ZFSet.prod C Q) reps height i z).1 hiz
  exact ⟨x, hx, ((pair_mem_relationConverse E S birth x i).1 (chosen ix)).2.2, xz⟩

theorem essentialBirthIndices_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega := by
  obtain ⟨h, hh, injection, antitone, _⟩ := M.exists_essentialBirthHeights pairing unions powers
    separation choice hF hT hr hBirth hC hQ hHeight positive ordinal heights irreflexive descent
  exact M.groundCountable_descending_heights pairing unions powers separation infinite choice
    (M.essentialBirthIndices_mem separation hF hT hr hBirth) hC hQ hh
    (fun _ hi => ((mem_essentialBirthIndices F T r birth _).1 hi).1)
    ordinal injection smallQ antitone

end TransitiveGround

end



open SetFormula
universe u

noncomputable def naturalFamilyShift (family : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose ZFSet.omega ZFSet.omega family.sUnion.sUnion natSuccessorGraph family

theorem naturalFamilyShift_entries (family : ZFSet.{u}) (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ naturalFamilyShift family ↔
      ZFSet.pair (natSetCode (n + 1)) y ∈ family := by
  rw [naturalFamilyShift, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, k, hk, next, entry⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
    exact (pair_mem_natSuccessorGraph n k).1 next ▸ entry
  · intro entry
    exact ⟨natSetCode_mem_omega n, pair_second_mem_doubleUnion entry,
      natSetCode (n + 1), natSetCode_mem_omega (n + 1),
      (pair_mem_natSuccessorGraph n (n + 1)).2 rfl, entry⟩

theorem naturalFamilyShift_function {family : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega family) :
    FunctionGraphOn ZFSet.omega (naturalFamilyShift family) := by
  have bounded : ZFSet.IsFunc ZFSet.omega family.sUnion.sUnion family := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.to_isFunc.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, pair_second_mem_doubleUnion hz⟩
  exact ⟨_, relationCompose_function_of_subset natSuccessorGraph_isFunc bounded (fun _ h => h)⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem naturalFamilyShift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {family : ZFSet.{u}} (hFamily : family ∈ M.sets) : naturalFamilyShift family ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation (M.omega_mem separation infinite)
    (M.omega_mem separation infinite) (M.union_mem unions (M.union_mem unions hFamily))
    (M.natSuccessorGraph_mem pairing unions powers separation infinite) hFamily

end TransitiveGround


end PartitionPilot.Forcing

end OAI

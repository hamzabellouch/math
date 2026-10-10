import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs
import OAI.SetTheory.PartitionPrinciple.Forcing.NameRenameSteps

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) : Name s :=
  assemble
    (fun a : {a : T × P // ForcesMem a.2 ⟨a.1.val, valid a.1.val a.1.property⟩ U} =>
      image ⟨a.val.1.val, valid a.val.1.val a.val.1.property⟩)
    (fun a => a.val.2)

theorem entry_activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (σ : Name s) (p : P) :
    Entry σ (activeImage T valid U image) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧ image w = σ := by
  rw [activeImage, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.val, valid a.val.1.val a.val.1.property⟩, a.val.1.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨w, hw, forced, equal⟩
    exact ⟨⟨(⟨w.val, hw⟩, p), forced⟩, equal, rfl⟩

theorem activeImage_subset (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (F : ZFSet.{u})
    (images : ∀ w : Name s, w.val ∈ T → (image w).val ∈ F) :
    (activeImage T valid U image).val ⊆ ZFSet.prod F s.carrier := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (activeImage T valid U image) hz
  obtain ⟨w, hw, _, rfl⟩ := (entry_activeImage T valid U image σ p).1 hz
  exact ZFSet.pair_mem_prod.2 ⟨images w hw, s.encode_mem p⟩

theorem activeImage_congr (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image other : Name s → Name s)
    (equal : ∀ w : Name s, w.val ∈ T → image w = other w) :
    activeImage T valid U image = activeImage T valid U other := by
  apply Name.ext
  intro σ p
  rw [entry_activeImage, entry_activeImage]
  constructor
  · rintro ⟨w, hw, forced, entry⟩
    exact ⟨w, hw, forced, (equal w hw).symm.trans entry⟩
  · rintro ⟨w, hw, forced, entry⟩
    exact ⟨w, hw, forced, (equal w hw).trans entry⟩

theorem mem_eval_activeImage (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (hU : U ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names) (x : ZFSet.{u}) :
    x ∈ eval {p | H.mem p} (activeImage T valid U image) ↔
      ∃ w : Name s, w.val ∈ T ∧ eval {p | H.mem p} w ∈ eval {p | H.mem p} U ∧
        eval {p | H.mem p} (image w) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, equal⟩
    obtain ⟨w, hw, forced, rfl⟩ := (entry_activeImage T valid U image σ p).1 entry
    exact ⟨w, hw, forcesMem_sound D H generic (terms w hw) hU hp forced, equal⟩
  · rintro ⟨w, hw, active, equal⟩
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (terms w hw) hU).1 active
    exact ⟨image w, p, (entry_activeImage T valid U image (image w) p).2
      ⟨w, hw, forced, rfl⟩, hp, equal⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (g : G) (U : Name s) (image other : Name s → Name s)
    (equivariant : ∀ w : Name s, w.val ∈ T →
      a.act s g (image w) = other (a.act s g w)) :
    a.act s g (activeImage T valid U image) =
      activeImage T valid (a.act s g U) other := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (activeImage T valid U image)) p ↔ _
  rw [entry_rename, entry_activeImage]
  constructor
  · rintro ⟨ν, q, entry, equal, rfl⟩
    obtain ⟨w, hw, forced, rfl⟩ := (entry_activeImage T valid U image ν q).1 entry
    exact ⟨a.act s g w, closed g w hw, a.forcesMem_act s g forced,
      (equivariant w hw).symm.trans equal⟩
  · rintro ⟨w, hw, forced, equal⟩
    have oldMember := closed g⁻¹ w hw
    have oldForced : ForcesMem ((a.iso g).symm p) (a.act s g⁻¹ w) U := by
      apply (a.forcesMem_act_iff s g ((a.iso g).symm p) (a.act s g⁻¹ w) U).1
      simpa only [OrderIso.apply_symm_apply, a.act_inv_right] using forced
    refine ⟨image (a.act s g⁻¹ w), (a.iso g).symm p,
      (entry_activeImage T valid U image _ _).2 ⟨a.act s g⁻¹ w, oldMember, oldForced, rfl⟩,
      ?_, (a.iso g).apply_symm_apply p⟩
    change a.act s g (image (a.act s g⁻¹ w)) = σ
    rw [equivariant _ oldMember, a.act_inv_right]
    exact equal

theorem activeImage_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (U : Name s) (image : Name s → Name s) (K : Subgroup G)
    (activity : K ≤ a.stabilizer s U)
    (equivariant : ∀ g ∈ K, ∀ w : Name s, w.val ∈ T →
      a.act s g (image w) = image (a.act s g w)) :
    K ≤ a.stabilizer s (activeImage T valid U image) := by
  intro g hg
  change a.act s g _ = _
  rw [act_activeImage a T valid closed g U image image (equivariant g hg), activity hg]

theorem activeImage_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (U : Name s) (image : Name s → Name s) (K : Subgroup G) (member : F.mem K)
    (activity : K ≤ a.stabilizer s U)
    (equivariant : ∀ g ∈ K, ∀ w : Name s, w.val ∈ T →
      a.act s g (image w) = image (a.act s g w))
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F (image w)) :
    HereditarilySymmetric a s F (activeImage T valid U image) := by
  refine HereditarilySymmetric.mk
    (F.upward member (activeImage_support a T valid closed U image K activity equivariant)) ?_
  intro σ p entry
  obtain ⟨w, hw, _, rfl⟩ := (entry_activeImage T valid U image σ p).1 entry
  exact children w hw

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def activeNameImageEntryFormula : SetFormula 6 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 0 7)
    (.conj (orderedPairFormula 3 1 0)
      (.conj (pairMembershipFormula 2 1 6)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 0 ![2, 5])))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem realize_activeNameImageEntryFormula {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets activeNameImageEntryFormula
      (extend x (extend T (extend U.val (extend graph
        (extend s.carrier (extend s.conditionOrder Fin.elim0)))))) ↔
      x ∈ (Name.activeImage T valid U image).val := by
  let env := extend x (extend T (extend U.val (extend graph
    (extend s.carrier (extend s.conditionOrder Fin.elim0)))))
  change Realize M.sets activeNameImageEntryFormula env ↔ _
  rw [activeNameImageEntryFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, body⟩
    obtain ⟨z, hz, body⟩ := (realize_ex M.sets _ _).1 body
    obtain ⟨q, hq, member, condition, code, imageEntry, forced⟩ :=
      (realize_ex M.sets _ _).1 body
    change w ∈ T at member
    change q ∈ s.carrier at condition
    obtain ⟨p, rfl⟩ := (s.mem_carrier q).1 condition
    let term : Name s := ⟨w, valid w member⟩
    have equal := (M.realize_orderedPairFormula pairing 3 1 0 _ hx hz hq).1 code
    have graphEntry := (M.realize_pairMembershipFormula pairing 2 1 6 _ hw hz hgraph).1 imageEntry
    have imageEqual := ((entries term z).1 graphEntry).2
    let names : Assignment (M.nameDomain s) 2 := extend ⟨term, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).1 forced
    change x = ZFSet.pair z (s.encode p) at equal
    rw [equal, imageEqual]
    exact (Name.entry_activeImage T valid U image (image term) p).2
      ⟨term, member, atom, rfl⟩
  · intro member
    obtain ⟨z, p, rfl⟩ := Name.entries_cover (Name.activeImage T valid U image) member
    obtain ⟨w, hwT, forced, rfl⟩ := (Name.entry_activeImage T valid U image z p).1 member
    have hw := M.transitive hT hwT
    have hp := M.transitive carrier (s.encode_mem p)
    have graphEntry := (entries w (image w).val).2 ⟨hwT, rfl⟩
    have hz := M.transitive (M.union_mem unions (M.union_mem unions hgraph))
      (pair_second_mem_doubleUnion graphEntry)
    refine ⟨w.val, hw, ?_⟩
    rw [realize_ex]
    refine ⟨(image w).val, hz, ?_⟩
    rw [realize_ex]
    refine ⟨s.encode p, hp, hwT, s.encode_mem p, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 1 0 _ hx hz hp).2 rfl
    · exact (M.realize_pairMembershipFormula pairing 2 1 6 _ hw hz hgraph).2 graphEntry
    · let names : Assignment (M.nameDomain s) 2 := extend ⟨w, hw⟩ (extend ⟨U, hU⟩ Fin.elim0)
      exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
        carrier order 0 1 (.mem 0 1) ![7, 8] 0 ![2, 5] _ rfl rfl p names rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))).2 forced

include pairing unions powers separation collection carrier order in
theorem activeImage_eq_selection {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val) :
    (Name.activeImage T valid U image).val =
      ZFSet.sep (fun x => Realize M.sets activeNameImageEntryFormula
        (extend x (extend T (extend U.val (extend graph
          (extend s.carrier (extend s.conditionOrder Fin.elim0)))))))
        (ZFSet.prod (functionGraphRange T graph) s.carrier) := by
  have rangeGround := M.functionGraphRange_mem unions separation hT hgraph
  have boundGround := M.prod_mem pairing unions powers separation rangeGround carrier
  have bound := Name.activeImage_subset T valid U image (functionGraphRange T graph)
    (fun w hw => (mem_functionGraphRange T graph _).2
      ⟨w.val, hw, (entries w (image w).val).2 ⟨hw, rfl⟩⟩)
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    exact ⟨bound member,
      (M.realize_activeNameImageEntryFormula s pairing unions powers separation collection
        carrier order hT valid U hU image graph hgraph entries x
        (M.transitive boundGround (bound member))).2 member⟩
  · rintro ⟨hx, formula⟩
    exact (M.realize_activeNameImageEntryFormula s pairing unions powers separation collection
      carrier order hT valid U hU image graph hgraph entries x
      (M.transitive boundGround hx)).1 formula

include pairing unions powers separation collection carrier order in
theorem activeImage_mem {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U : Name s) (hU : U.val ∈ M.sets)
    (image : Name s → Name s) (graph : ZFSet.{u}) (hgraph : graph ∈ M.sets)
    (entries : ∀ (w : Name s) z, ZFSet.pair w.val z ∈ graph ↔
      w.val ∈ T ∧ z = (image w).val) :
    (Name.activeImage T valid U image).val ∈ M.sets := by
  rw [M.activeImage_eq_selection s pairing unions powers separation collection carrier order
    hT valid U hU image graph hgraph entries]
  exact M.separation_mem separation activeNameImageEntryFormula _
    (Fin.cases hT (Fin.cases hU (Fin.cases hgraph (Fin.cases carrier
      (Fin.cases order (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation
      (M.functionGraphRange_mem unions separation hT hgraph) carrier)

end TransitiveGround
end PartitionPilot.Forcing

end OAI

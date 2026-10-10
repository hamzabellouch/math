import OAI.SetTheory.PartitionPrinciple.Definability.OrbitImageFormulas

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem orbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) : a.orbitCodes s (M.nameDomain s) W ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers group hW
  apply M.definable_image_mem separation collection orbitImageFormula (orbitParameters a s t W)
    (Fin.cases hW (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i))))) hB
  · intro y hy
    obtain ⟨g, σ, hσ, _, rfl⟩ := (a.mem_orbitCodes s (M.nameDomain s) W y).1 hy
    exact M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ
  · intro y hy
    rw [a.mem_orbitCodes]
    constructor
    · rintro ⟨g, σ, hσ, hσW, eq⟩
      have hb := pairBound (t.encode g) (t.encode_mem g) σ.val hσW
      exact ⟨ZFSet.pair (t.encode g) σ.val, hb,
        (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps W _ y
          (M.transitive hB hb) hy).2 ⟨g, ⟨σ, hσ⟩, hσW, rfl, eq⟩⟩
    · rintro ⟨z, hz, rel⟩
      obtain ⟨g, σ, hσW, _, eq⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
        carrier group maps W z y (M.transitive hB hz) hy).1 rel
      exact ⟨g, σ.val, σ.property, hσW, eq⟩
  · intro z hz y hy w hw rely relw
    obtain ⟨g, σ, _, shape, eqy⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z y (M.transitive hB hz) hy).1 rely
    obtain ⟨h, τ, _, shape', eqw⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z w (M.transitive hB hz) hw).1 relw
    have parts := ZFSet.pair_inj.1 (shape.symm.trans shape')
    have gh := t.injective parts.1
    have names : σ.val = τ.val := Subtype.ext parts.2
    rw [eqy, eqw, gh, names]

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def mixtureTermCodes (τ : Name s) : ZFSet.{u} :=
  a.orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ)

theorem mixtureTermCodes_mem (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) :
    M.mixtureTermCodes a s τ ∈ M.sets :=
  M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps _
    (M.immediateChildCodes_mem s pairing unions powers separation carrier τ ground)

theorem mixtureTermCodes_valid (τ : Name s) :
    ∀ y ∈ M.mixtureTermCodes a s τ, IsName s y := by
  intro y member
  obtain ⟨g, σ, _, _, rfl⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) y).1 member
  exact (a.act s g σ).property

theorem mixtureTermCodes_closed (τ : Name s) (g : G) (σ : Name s)
    (member : σ.val ∈ M.mixtureTermCodes a s τ) :
    (a.act s g σ).val ∈ M.mixtureTermCodes a s τ :=
  (a.act_mem_orbitCodes_iff s (M.nameDomain s) (Name.immediateChildCodes τ) g σ).2 member

theorem mixtureTermCodes_hs (F : NormalSubgroupFamily G) (τ : Name s)
    (hs : HereditarilySymmetric a s F τ) (ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : HereditarilySymmetric a s F ψ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved]
  exact (hs.member entry).translated g

theorem mixtureTermCodes_rank (τ ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : Name.nameRank ψ < Name.nameRank τ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved, a.nameRank_act]
  exact Name.entry_nameRank_lt entry

theorem mix_subset_mixtureTermCodes (τ : Name s) (ground : τ.val ∈ M.sets)
    (K : Subgroup G) (p : P) :
    (a.mix s K p τ).val ⊆ ZFSet.prod (M.mixtureTermCodes a s τ) s.carrier := by
  intro z member
  obtain ⟨σ, q, rfl⟩ := Name.entries_cover (a.mix s K p τ) member
  obtain ⟨g, _, ν, r, entry, rfl, _, _⟩ := (a.entry_mix s K p τ σ q).1 member
  refine ZFSet.pair_mem_prod.2 ⟨?_, s.encode_mem q⟩
  exact (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) _).2
    ⟨g, ν, (M.nameDomain s).children ground entry,
      (Name.mem_immediateChildCodes τ ν.val).2 ⟨ν, r, entry, rfl⟩, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI

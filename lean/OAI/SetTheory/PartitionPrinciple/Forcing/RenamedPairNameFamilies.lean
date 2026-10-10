import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompleteProjectionAtomicTruth
import OAI.SetTheory.PartitionPrinciple.Forcing.PairFamilyEvaluation

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem exists_uniformRename_between (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets) :
    ∃ G ∈ M.sets,
      G = s.graph t f ∪ identityFunctionGraph
        (ZFSet.sep (fun x => x ∉ s.carrier) (s.carrier ∪ t.carrier)) ∧
      ∀ (σ : Name s) (τ : Name t), σ.val ∈ M.sets → τ.val ∈ M.sets →
        (Realize M.sets uniformRenameFormula
          (extend σ.val (extend τ.val (extend (s.carrier ∪ t.carrier) (extend G Fin.elim0)))) ↔
          Name.rename t f σ = τ) := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  refine ⟨G, hG, rfl, ?_⟩
  intro σ τ hσ hτ
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) σ
  have targetCode := Name.rename_val_of_encode u et (t.encode_intoSet U subT) τ
  have graph : u.graph u h = G := u.graph_decodeFunction u G full
  have exactFormula := M.realize_uniformRenameFormula u pairing unions powers separation collection hU h
    (graph ▸ hG) (Name.rename u es σ) (Name.rename u et τ)
    (sourceCode ▸ hσ) (targetCode ▸ hτ)
  change Realize M.sets uniformRenameFormula
    (extend (Name.rename u es σ).val (extend (Name.rename u et τ).val
      (extend U (extend (u.graph u h) Fin.elim0)))) ↔ _ at exactFormula
  rw [sourceCode, targetCode, graph] at exactFormula
  refine exactFormula.trans ?_
  have equation : Name.rename u h (Name.rename u es σ) =
      Name.rename u et (Name.rename t f σ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k σ)
    funext p
    exact commute p
  rw [equation]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [Name.rename_val_of_encode u et (t.encode_intoSet U subT)] using codes
  · intro equal
    exact congrArg (Name.rename u et) equal

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

noncomputable def renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) : ZFSet.{u} :=
  familyCodeGraph (fun x : T => x.val)
    (fun x => (rename t f ⟨x.val, valid x.val x.property⟩).val)

noncomputable def renamedFamily (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) : ZFSet.{u} :=
  functionGraphRange T (renameFamilyGraph t f T valid)

theorem mem_renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (z : ZFSet.{u}) :
    z ∈ renameFamilyGraph t f T valid ↔
      ∃ σ : Name s, σ.val ∈ T ∧ z = ZFSet.pair σ.val (rename t f σ).val := by
  rw [renameFamilyGraph, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, valid x.val x.property⟩, x.property, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ.val, hσ⟩, rfl⟩

theorem pair_mem_renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (σ : Name s) (y : ZFSet.{u}) :
    ZFSet.pair σ.val y ∈ renameFamilyGraph t f T valid ↔
      σ.val ∈ T ∧ y = (rename t f σ).val := by
  rw [mem_renameFamilyGraph]
  constructor
  · rintro ⟨τ, hτ, eq⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 eq
    have same : σ = τ := Subtype.ext keys
    exact ⟨same.symm ▸ hτ, by simpa only [same] using values⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩

theorem renameFamilyGraph_function (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    ZFSet.IsFunc T (renamedFamily t f T valid) (renameFamilyGraph t f T valid) := by
  apply functionGraphRange_function
  have keys : ZFSet.range (fun x : T => x.val) = T := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range]
    exact ⟨fun ⟨y, eq⟩ => eq ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simpa only [keys, renameFamilyGraph] using familyCodeGraph_function (fun x : T => x.val)
    (fun x => (rename t f ⟨x.val, valid x.val x.property⟩).val) Subtype.val_injective

theorem mem_renamedFamily (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (y : ZFSet.{u}) :
    y ∈ renamedFamily t f T valid ↔ ∃ σ : Name s, σ.val ∈ T ∧ y = (rename t f σ).val := by
  rw [renamedFamily, mem_functionGraphRange]
  constructor
  · rintro ⟨x, hx, entry⟩
    let σ : Name s := ⟨x, valid x hx⟩
    exact ⟨σ, hx, ((pair_mem_renameFamilyGraph t f T valid σ y).1 entry).2⟩
  · rintro ⟨σ, hσ, equal⟩
    exact ⟨σ.val, hσ, (pair_mem_renameFamilyGraph t f T valid σ y).2 ⟨hσ, equal⟩⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

def renamedNameFamilyPairFormula : SetFormula 5 :=
  .ex (.conj (domainApplication uniformNameFormula (extend 3 Fin.elim0) 0)
    (.conj (binaryApplication uniformRenameFormula (extend 4 (extend 5 Fin.elim0)) 1 0)
      (orderedPairFormula 2 1 0)))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} (s : Presentation P) (t : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem renameFamilyGraph_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renameFamilyGraph t f T valid ∈ M.sets := by
  obtain ⟨G, hG, _, recognizes⟩ := M.exists_uniformRename_between s t
    pairing unions powers separation collection hs ht f hf
  let U := s.carrier ∪ t.carrier
  let params := extend t.carrier (extend U (extend G Fin.elim0))
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have meaning (σ : Name s) (hσ : σ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets renamedNameFamilyPairFormula (extend σ.val (extend z params)) ↔
        z = ZFSet.pair σ.val (Name.rename t f σ).val := by
    rw [renamedNameFamilyPairFormula, realize_ex]
    constructor
    · rintro ⟨v, hv, named, renamed, pair⟩
      rw [realize_domainApplication, map_extend, map_empty] at named
      have validV : IsName t v :=
        (M.realize_uniformNameFormula t pairing unions powers separation collection ht v hv).1 named
      rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
      have eq := (recognizes σ ⟨v, validV⟩ hσ hv).1 renamed
      have pairEq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).1 pair
      exact (congrArg Subtype.val eq).symm ▸ pairEq
    · intro equal
      have hv := M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ hσ
      refine ⟨(Name.rename t f σ).val, hv, ?_, ?_, ?_⟩
      · rw [realize_domainApplication, map_extend, map_empty]
        exact (M.realize_uniformNameFormula t pairing unions powers separation collection ht _ hv).2
          (Name.rename t f σ).property
      · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
        exact (recognizes σ (Name.rename t f σ) hσ hv).2 rfl
      · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).2 equal
  apply M.definable_image_mem separation collection renamedNameFamilyPairFormula params
    (Fin.cases ht (Fin.cases hU (Fin.cases hG (fun i => Fin.elim0 i)))) hT
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (Name.mem_renameFamilyGraph t f T valid z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hT hσ)
      (M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ (M.transitive hT hσ))
  · intro z hz
    rw [Name.mem_renameFamilyGraph]
    constructor
    · rintro ⟨σ, hσ, eq⟩
      exact ⟨σ.val, hσ, (meaning σ (M.transitive hT hσ) z hz).2 eq⟩
    · rintro ⟨x, hx, rel⟩
      exact ⟨⟨x, valid x hx⟩, hx, (meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 rel⟩
  · intro x hx y hy z hz first second
    exact ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) y hy).1 first).trans
      ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 second).symm

theorem renamedFamily_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renamedFamily t f T valid ∈ M.sets :=
  M.functionGraphRange_mem unions separation hT
    (M.renameFamilyGraph_mem s t pairing unions powers separation collection hs ht f hf T hT valid)

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def termActionEntryFormula : SetFormula 5 :=
  .ex (.ex (.conj (.mem 1 4) (.conj (.mem 0 4)
    (.conj (orderedPairFormula 2 1 0) (reindex ![3, 1, 0, 5, 6] nameActionFormula)))))

def termActionSetFormula : SetFormula 5 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 4 => j.succ.succ)) termActionEntryFormula)

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include pairing unions powers separation collection carrier group maps hT closed

theorem realize_termActionEntryFormula (g : G) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets termActionEntryFormula ![z, t.encode g, T, s.carrier, a.conditionMapFamily s t] ↔
      z ∈ Name.renameFamilyGraph s (a.iso g) T valid := by
  let env : Fin 5 → ZFSet.{u} := ![z, t.encode g, T, s.carrier, a.conditionMapFamily s t]
  have args (x y : ZFSet.{u}) :
      (fun j : Fin 5 => (extend y (extend x env)) (![3, 1, 0, 5, 6] j)) =
        ![t.encode g, x, y, s.carrier, a.conditionMapFamily s t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun k => Fin.elim0 k))))) j
  change Realize M.sets termActionEntryFormula env ↔ _
  simp only [termActionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hxm, y, hym, hx, hy, paired, acted⟩
    let w : Name s := ⟨x, valid x hx⟩
    let v : Name s := ⟨y, valid y hy⟩
    have equal := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).1 paired
    change z = ZFSet.pair x y at equal
    rw [realize_reindex, args] at acted
    have action := (M.realize_nameActionFormula a s t pairing unions powers separation collection
      carrier group maps g w v hxm hym).1 acted
    exact equal.symm ▸ (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w y).2
      ⟨hx, congrArg Subtype.val action.symm⟩
  · intro entry
    obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T valid z).1 entry
    have hwm := M.transitive hT hw
    have actedT := closed g w hw
    have actedGround := M.transitive hT actedT
    refine ⟨w.val, hwm, (a.act s g w).val, actedGround, hw, actedT,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hwm actedGround).2 rfl, ?_⟩
    rw [realize_reindex, args]
    exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
      carrier group maps g w (a.act s g w) hwm actedGround).2 rfl

theorem realize_termActionSetFormula (g : G) (F : ZFSet.{u}) (hF : F ∈ M.sets) :
    Realize M.sets termActionSetFormula ![F, t.encode g, T, s.carrier, a.conditionMapFamily s t] ↔
      F = Name.renameFamilyGraph s (a.iso g) T valid := by
  have graph := M.renameFamilyGraph_mem s s pairing unions powers separation collection carrier carrier
    (a.iso g) (M.conditionMap_graph_mem a s t maps g) T hT valid
  apply M.realize_exactSetFormula 0 _ _ hF (fun _ h => M.transitive graph h)
  intro z hz
  rw [realize_reindex, map_extend]
  exact M.realize_termActionEntryFormula a s t T valid pairing unions powers separation collection
    carrier group maps hT closed g z hz

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u
variable {G P Q L : Type u} [Group G] [PartialOrder P] [PartialOrder Q] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (e : PosetAction G Q) (t : Presentation Q)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid' : ∀ z ∈ T, IsName t z)
variable (graphs : ∀ g, Name.renameFamilyGraph t (e.iso g) T valid' =
  Name.renameFamilyGraph s (a.iso g) T valid)
include graphs

theorem support_of_term_graphs (u : Name s) (v : Name t) (member : u.val ∈ T)
    (same : v.val = u.val) {K : Subgroup G} (supported : K ≤ a.stabilizer s u) :
    K ≤ e.stabilizer t v := by
  intro g hg
  have fixed : a.act s g u = u := supported hg
  have entry : ZFSet.pair u.val u.val ∈ Name.renameFamilyGraph s (a.iso g) T valid :=
    (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u u.val).2
      ⟨member, (congrArg Subtype.val fixed).symm⟩
  rw [← graphs g] at entry
  have target : ZFSet.pair v.val v.val ∈ Name.renameFamilyGraph t (e.iso g) T valid' := by
    simpa only [same] using entry
  have value := ((Name.pair_mem_renameFamilyGraph t (e.iso g) T valid' v v.val).1 target).2
  exact Subtype.ext value.symm

theorem positionSupport_of_term_graphs (b : Presentation L) (d : PosetAction G L)
    (S mu X tuples : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u) :
    ∀ f ∈ S, ∀ v : Name t, ZFSet.pair f v.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ e.stabilizer t v := by
  intro f hf v entry bound
  have member := range f v.val entry
  let u : Name s := ⟨v.val, valid v.val member⟩
  exact a.support_of_term_graphs s e t T valid valid' graphs u v member rfl
    (support f hf u entry bound)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem renamedFamily_valid (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    ∀ y ∈ renamedFamily t f T valid, IsName t y := by
  intro y hy
  obtain ⟨σ, _, rfl⟩ := (mem_renamedFamily t f T valid y).1 hy
  exact (rename t f σ).property

theorem presentationFamily_injection (t : Presentation P)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    InjectionCode T (renamedFamily t id T valid) (renameFamilyGraph t id T valid) := by
  refine ⟨renameFamilyGraph_function t id T valid, ?_⟩
  intro x y z first second
  obtain ⟨σ, _, shapeσ⟩ := (mem_renameFamilyGraph t id T valid (ZFSet.pair x z)).1 first
  obtain ⟨τ, _, shapeτ⟩ := (mem_renameFamilyGraph t id T valid (ZFSet.pair y z)).1 second
  obtain ⟨rfl, eqσ⟩ := ZFSet.pair_inj.1 shapeσ
  obtain ⟨rfl, eqτ⟩ := ZFSet.pair_inj.1 shapeτ
  have images : presentationEquiv s t σ = presentationEquiv s t τ :=
    Subtype.ext (eqσ.symm.trans eqτ)
  exact congrArg Subtype.val ((presentationEquiv s t).injective images)

theorem rename_familySet (t : Presentation Q) (f : P → Q) (one : P)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    rename t f (familySet one T valid) =
      familySet (f one) (renamedFamily t f T valid) (renamedFamily_valid t f T valid) := by
  apply Name.ext
  intro τ q
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨σ, p, entry, rfl, rfl⟩
    obtain ⟨hσ, rfl⟩ := (entry_familySet one T valid σ p).1 entry
    exact ⟨(mem_renamedFamily t f T valid _).2 ⟨σ, hσ, rfl⟩, rfl⟩
  · rintro ⟨hτ, rfl⟩
    obtain ⟨σ, hσ, equal⟩ := (mem_renamedFamily t f T valid τ.val).1 hτ
    exact ⟨σ, one, (entry_familySet one T valid σ one).2 ⟨hσ, rfl⟩,
      Subtype.ext equal.symm, rfl⟩

theorem eval_renamedFamily (t : Presentation P) (T : ZFSet.{u})
    (valid : ∀ x ∈ T, IsName s x) (H : Set P) (x : ZFSet.{u}) :
    (∃ τ : Name t, τ.val ∈ renamedFamily t id T valid ∧ eval H τ = x) ↔
      ∃ σ : Name s, σ.val ∈ T ∧ eval H σ = x := by
  constructor
  · rintro ⟨τ, hτ, equal⟩
    obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
    have names : τ = presentationEquiv s t σ := Subtype.ext codes
    exact ⟨σ, hσ, by rw [names, eval_presentationEquiv] at equal; exact equal⟩
  · rintro ⟨σ, hσ, equal⟩
    exact ⟨presentationEquiv s t σ, (mem_renamedFamily t id T valid _).2 ⟨σ, hσ, rfl⟩,
      (eval_presentationEquiv s t H σ).trans equal⟩

variable {G : Type v} [Group G] [PartialOrder P]

theorem renamedFamily_closed (a : PosetAction G P) (t : Presentation P)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x)
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T) :
    ∀ g (τ : Name t), τ.val ∈ renamedFamily t id T valid →
      (a.act t g τ).val ∈ renamedFamily t id T valid := by
  intro g τ hτ
  obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
  have names : τ = presentationEquiv s t σ := Subtype.ext codes
  rw [names, a.act_presentationEquiv]
  exact (mem_renamedFamily t id T valid _).2 ⟨a.act s g σ, closed g σ hσ, rfl⟩

theorem renamedFamily_hs (a : PosetAction G P) (t : Presentation P)
    (F : NormalSubgroupFamily G) (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    ∀ τ : Name t, τ.val ∈ renamedFamily t id T valid → HereditarilySymmetric a t F τ := by
  intro τ hτ
  obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
  have names : τ = presentationEquiv s t σ := Subtype.ext codes
  exact names.symm ▸ (children σ hσ).presentationEquiv t

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def termActionFamilyEntryFormula : SetFormula 5 :=
  .ex (.ex (.conj (.mem 1 3) (.conj (orderedPairFormula 2 1 0)
    (reindex ![0, 1, 4, 5, 6] termActionSetFormula))))

end SetFormula
namespace PosetAction
variable {G P : Type u} [Group G] [PartialOrder P]

noncomputable def termActionFamily (a : PosetAction G P) (s : Presentation P)
    (t : Presentation G) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : ZFSet.{u} :=
  familyCodeGraph t.encode (fun g => Name.renameFamilyGraph s (a.iso g) T valid)

theorem pair_mem_termActionFamily (a : PosetAction G P) (s : Presentation P)
    (t : Presentation G) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ a.termActionFamily s t T valid ↔
      F = Name.renameFamilyGraph s (a.iso g) T valid :=
  pair_mem_familyCodeGraph _ _ t.injective g F

theorem termActionFamily_function (a : PosetAction G P) (s : Presentation P)
    (t : Presentation G) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) :
    FunctionGraphOn t.carrier (a.termActionFamily s t T valid) := by
  have equal : ZFSet.range t.encode = t.carrier := by
    apply ZFSet.ext
    intro x
    exact ZFSet.mem_range.trans (t.mem_carrier x).symm
  simpa only [equal, termActionFamily] using familyCodeGraph_function t.encode
    (fun g => Name.renameFamilyGraph s (a.iso g) T valid) t.injective

end PosetAction
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include pairing unions powers separation collection carrier group maps hT closed

theorem termActionFamily_mem : a.termActionFamily s t T valid ∈ M.sets := by
  let values := fun g => Name.renameFamilyGraph s (a.iso g) T valid
  have graphGround (g : G) := M.renameFamilyGraph_mem s s pairing unions powers separation collection
    carrier carrier (a.iso g) (M.conditionMap_graph_mem a s t maps g) T hT valid
  have graphBound (g : G) : values g ∈ M.groundRelations T T := by
    refine (M.mem_groundRelations T T _).2 ⟨graphGround g, ?_⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T valid z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hw, closed g w hw⟩
  let params : Fin 4 → ZFSet.{u} := ![t.carrier, T, s.carrier, a.conditionMapFamily s t]
  have paramsGround : ∀ j, params j ∈ M.sets := Fin.cases group (Fin.cases hT
    (Fin.cases carrier (Fin.cases maps (fun j => Fin.elim0 j))))
  have args (z raw F : ZFSet.{u}) :
      (fun j : Fin 5 => (extend F (extend raw (extend z params))) (![0, 1, 4, 5, 6] j)) =
      ![F, raw, T, s.carrier, a.conditionMapFamily s t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun k => Fin.elim0 k))))) j
  have meaning (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets termActionFamilyEntryFormula (extend z params) ↔
      z ∈ a.termActionFamily s t T valid := by
    simp only [termActionFamilyEntryFormula, realize_ex]
    constructor
    · rintro ⟨raw, hr, F, hF, actor, paired, coded⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier raw).1 actor
      have pairEq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hr hF).1 paired
      change z = ZFSet.pair (t.encode g) F at pairEq
      rw [realize_reindex, args] at coded
      have equal := (M.realize_termActionSetFormula a s t T valid pairing unions powers separation
        collection carrier group maps hT closed g F hF).1 coded
      exact (mem_familyCodeGraph _ _ z).2 ⟨g, by simpa only [equal] using pairEq.symm⟩
    · intro member
      obtain ⟨g, rfl⟩ := (mem_familyCodeGraph _ _ z).1 member
      have hg := M.transitive group (t.encode_mem g)
      refine ⟨t.encode g, hg, values g, graphGround g, t.encode_mem g,
        (M.realize_orderedPairFormula pairing 2 1 0 _ hz hg (graphGround g)).2 rfl, ?_⟩
      rw [realize_reindex, args]
      exact (M.realize_termActionSetFormula a s t T valid pairing unions powers separation
        collection carrier group maps hT closed g (values g) (graphGround g)).2 rfl
  let B := ZFSet.prod t.carrier (M.groundRelations T T)
  have hB := M.prod_mem pairing unions powers separation group
    (M.groundRelations_mem pairing unions powers separation hT hT)
  have subset : a.termActionFamily s t T valid ⊆ B := by
    intro z hz
    obtain ⟨g, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨t.encode_mem g, graphBound g⟩
  have equal : ZFSet.sep (fun z => Realize M.sets termActionFamilyEntryFormula
      (extend z params)) B = a.termActionFamily s t T valid := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (meaning z (M.transitive hB h.1)).1 h.2,
      fun h => ⟨subset h, (meaning z (M.transitive hB (subset h))).2 h⟩⟩
  exact equal ▸ M.separation_mem separation termActionFamilyEntryFormula params paramsGround hB

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem renamedFamily_orderedPairNameFamily (t : Presentation Q) (f : P → Q) (one : P)
    (X Y : ZFSet.{u}) (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z) :
    renamedFamily t f (orderedPairNameFamily (s.encode one) X Y)
      (orderedPairNameFamily_valid one validX validY) =
      orderedPairNameFamily (t.encode (f one))
        (renamedFamily t f X validX) (renamedFamily t f Y validY) := by
  apply ZFSet.ext
  intro z
  rw [mem_renamedFamily, mem_orderedPairNameFamily]
  constructor
  · rintro ⟨σ, hσ, equal⟩
    obtain ⟨x, hx, y, hy, codes⟩ := (mem_orderedPairNameFamily _ X Y σ.val).1 hσ
    let ρ : Name s := ⟨x, validX x hx⟩
    let ν : Name s := ⟨y, validY y hy⟩
    have same : σ = orderedPair one ρ ν :=
      Subtype.ext (codes.trans (orderedPair_code one ρ ν).symm)
    refine ⟨(rename t f ρ).val, (mem_renamedFamily t f X validX _).2 ⟨ρ, hx, rfl⟩,
      (rename t f ν).val, (mem_renamedFamily t f Y validY _).2 ⟨ν, hy, rfl⟩, ?_⟩
    rw [same, rename_orderedPair, orderedPair_code] at equal
    exact equal
  · rintro ⟨x, hx, y, hy, equal⟩
    obtain ⟨ρ, hρ, rfl⟩ := (mem_renamedFamily t f X validX x).1 hx
    obtain ⟨ν, hν, rfl⟩ := (mem_renamedFamily t f Y validY y).1 hy
    refine ⟨orderedPair one ρ ν,
      (mem_orderedPairNameFamily _ X Y _).2 ⟨ρ.val, hρ, ν.val, hν, orderedPair_code one ρ ν⟩, ?_⟩
    rw [rename_orderedPair, orderedPair_code]
    exact equal

theorem renamedFamily_iteratedPairNameFamily (t : Presentation Q) (f : P → Q) (one : P)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (n : Nat) :
    renamedFamily t f (iteratedPairNameFamily (s.encode one) T n)
      (iteratedPairNameFamily_valid one valid n) =
      iteratedPairNameFamily (t.encode (f one)) (renamedFamily t f T valid) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change renamedFamily t f (orderedPairNameFamily (s.encode one)
      (iteratedPairNameFamily (s.encode one) T n) T)
      (orderedPairNameFamily_valid one (iteratedPairNameFamily_valid one valid n) valid) = _
    rw [renamedFamily_orderedPairNameFamily t f one _ _
      (iteratedPairNameFamily_valid one valid n) valid, ih]
    rfl

end PartitionPilot.Forcing.Name

end OAI

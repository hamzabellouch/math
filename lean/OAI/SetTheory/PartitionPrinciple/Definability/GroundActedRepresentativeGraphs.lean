import OAI.SetTheory.PartitionPrinciple.Forcing.RenamedPairNameFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (N : ZFSet.{u}) (valid : ∀ x ∈ N, IsName s x)

noncomputable def actedEnumerationGraph (g : G) (I names : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I N N names (renameFamilyGraph s (a.iso g) N valid)

noncomputable def actedRepresentativeGraph (g : G) (B f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose b.carrier B N (relationConverse B b.carrier (b.graph b (d.iso g)))
    (actedEnumerationGraph a s N valid g B f)

theorem renameFamilyGraph_act_function (g : G)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N) :
    ZFSet.IsFunc N N (renameFamilyGraph s (a.iso g) N valid) := by
  refine ⟨?_, (renameFamilyGraph_function s (a.iso g) N valid).2⟩
  intro z hz
  obtain ⟨tau, ht, rfl⟩ := (mem_renameFamilyGraph s (a.iso g) N valid z).1 hz
  exact ZFSet.pair_mem_prod.2 ⟨ht, closed tau ht⟩

theorem pair_mem_actedEnumerationGraph (g : G) {I names : ZFSet.{u}}
    (function : ZFSet.IsFunc I N names)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N)
    (i y : ZFSet.{u}) :
    ZFSet.pair i y ∈ actedEnumerationGraph a s N valid g I names ↔
      ∃ tau : Name s, ZFSet.pair i tau.val ∈ names ∧ y = (a.act s g tau).val := by
  rw [actedEnumerationGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, x, hx, ix, xy⟩
    let tau : Name s := ⟨x, valid x hx⟩
    exact ⟨tau, ix, ((pair_mem_renameFamilyGraph s (a.iso g) N valid tau y).1 xy).2⟩
  · rintro ⟨tau, entry, rfl⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact ⟨bounds.1, closed tau bounds.2, tau.val, bounds.2, entry,
      (pair_mem_renameFamilyGraph s (a.iso g) N valid tau _).2 ⟨bounds.2, rfl⟩⟩

theorem actedEnumerationGraph_entry (g : G) {I names : ZFSet.{u}}
    (function : ZFSet.IsFunc I N names)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N)
    (i : ZFSet.{u}) (tau : Name s) :
    ZFSet.pair i (a.act s g tau).val ∈ actedEnumerationGraph a s N valid g I names ↔
      ZFSet.pair i tau.val ∈ names := by
  rw [pair_mem_actedEnumerationGraph a s N valid g function closed]
  constructor
  · rintro ⟨sigma, entry, eq⟩
    have same : tau = sigma := (a.nameEquiv s g).injective (Subtype.ext eq)
    exact same.symm ▸ entry
  · intro entry
    exact ⟨tau, entry, rfl⟩

theorem actedEnumerationGraph_function (g : G) {I names : ZFSet.{u}}
    (function : ZFSet.IsFunc I N names)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N) :
    ZFSet.IsFunc I N (actedEnumerationGraph a s N valid g I names) :=
  relationCompose_function_of_subset function
    (renameFamilyGraph_act_function a s N valid g closed) (fun _ h => h)

theorem pair_mem_actedRepresentativeGraph (g : G) {B f : ZFSet.{u}}
    (basis : B ⊆ b.carrier) (function : ZFSet.IsFunc B N f)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N)
    (v : L) (y : ZFSet.{u}) :
    ZFSet.pair (b.encode (d.iso g v)) y ∈ actedRepresentativeGraph a s b d N valid g B f ↔
      ∃ tau : Name s, ZFSet.pair (b.encode v) tau.val ∈ f ∧ y = (a.act s g tau).val := by
  rw [actedRepresentativeGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, x, hx, inverse, mapped⟩
    have node := ((pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) x _).1 inverse).2.2
    obtain ⟨w, rfl⟩ := (b.mem_carrier x).1 (basis hx)
    have same := (d.iso g).injective ((b.pair_mem_graph b (d.iso g) w _).1 node)
    subst w
    exact (pair_mem_actedEnumerationGraph a s N valid g function closed _ y).1 mapped
  · rintro ⟨tau, entry, rfl⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    refine ⟨b.encode_mem _, closed tau bounds.2, b.encode v, bounds.1, ?_, ?_⟩
    · exact (pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) _ _).2
        ⟨bounds.1, b.encode_mem _, (b.pair_mem_graph b (d.iso g) v _).2 rfl⟩
    · exact (pair_mem_actedEnumerationGraph a s N valid g function closed _ _).2 ⟨tau, entry, rfl⟩

theorem actedRepresentativeGraph_entry (g : G) {B f : ZFSet.{u}}
    (basis : B ⊆ b.carrier) (function : ZFSet.IsFunc B N f)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N)
    (v : L) (tau : Name s) :
    ZFSet.pair (b.encode (d.iso g v)) (a.act s g tau).val ∈
      actedRepresentativeGraph a s b d N valid g B f ↔ ZFSet.pair (b.encode v) tau.val ∈ f := by
  rw [pair_mem_actedRepresentativeGraph a s b d N valid g basis function closed]
  constructor
  · rintro ⟨sigma, entry, eq⟩
    have same : tau = sigma := (a.nameEquiv s g).injective (Subtype.ext eq)
    exact same.symm ▸ entry
  · intro entry
    exact ⟨tau, entry, rfl⟩

theorem actedRepresentativeGraph_function (g : G) {B f : ZFSet.{u}}
    (function : ZFSet.IsFunc B N f)
    (closed : ∀ tau : Name s, tau.val ∈ N → (a.act s g tau).val ∈ N) :
    ZFSet.IsFunc (relationImage B b.carrier (b.graph b (d.iso g))) N
      (actedRepresentativeGraph a s b d N valid g B f) := by
  let inverse := relationConverse B b.carrier (b.graph b (d.iso g))
  let mapped := actedEnumerationGraph a s N valid g B f
  have mappedFunction := actedEnumerationGraph_function a s N valid g function closed
  have injective := b.graph_injection b (d.iso g) (d.iso g).injective
  have uniqueInverse : ∀ x v w, ZFSet.pair x v ∈ inverse → ZFSet.pair x w ∈ inverse → v = w := by
    intro x v w first second
    exact injective.injective v w x
      ((pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) v x).1 first).2.2
      ((pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) w x).1 second).2.2
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, v, hv, tau, ht, rfl, xv, _⟩ :=
      (mem_relationCompose b.carrier B N inverse mapped z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨(mem_relationImage B b.carrier (b.graph b (d.iso g)) x).2
      ⟨hx, v, hv, ((pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) v x).1 xv).2.2⟩, ht⟩
  · intro x hx
    obtain ⟨hxNodes, v, hv, vx⟩ := (mem_relationImage B b.carrier (b.graph b (d.iso g)) x).1 hx
    have xv : ZFSet.pair x v ∈ inverse :=
      (pair_mem_relationConverse B b.carrier (b.graph b (d.iso g)) v x).2 ⟨hv, hxNodes, vx⟩
    obtain ⟨tau, vt, unique⟩ := mappedFunction.2 v hv
    have ht := (ZFSet.pair_mem_prod.1 (mappedFunction.1 vt)).2
    refine ⟨tau, (pair_mem_relationCompose b.carrier B N inverse mapped x tau).2
      ⟨hxNodes, ht, v, hv, xv, vt⟩, ?_⟩
    intro other entry
    obtain ⟨_, _, w, _, xw, wt⟩ :=
      (pair_mem_relationCompose b.carrier B N inverse mapped x other).1 entry
    exact unique other (uniqueInverse x w v xw xv ▸ wt)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (t : Presentation G)
variable (N : ZFSet.{u}) (valid : ∀ x ∈ N, IsName s x)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem actedEnumerationGraph_mem
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hN : N ∈ M.sets) (g : G) {I names : ZFSet.{u}}
    (hI : I ∈ M.sets) (hNames : names ∈ M.sets) :
    Name.actedEnumerationGraph a s N valid g I names ∈ M.sets := by
  have nameGraph := M.renameFamilyGraph_mem s s pairing unions powers separation collection
    carrier carrier (a.iso g) (M.conditionMap_graph_mem a s t maps g) N hN valid
  exact M.relationCompose_mem pairing unions powers separation hI hN hN hNames nameGraph

theorem actedRepresentativeGraph_mem
    (carrier : s.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hN : N ∈ M.sets) (g : G) {B f : ZFSet.{u}}
    (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    Name.actedRepresentativeGraph a s b d N valid g B f ∈ M.sets := by
  have named := M.actedEnumerationGraph_mem a s t N valid pairing unions powers separation
    collection carrier maps hN g hB hf
  have inverse := M.relationConverse_mem pairing unions powers separation hB nodes
    (M.conditionMap_graph_mem d b t nodeMaps g)
  exact M.relationCompose_mem pairing unions powers separation nodes hB hN inverse named

end PartitionPilot.Forcing.TransitiveGround

end

end OAI

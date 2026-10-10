import OAI.SetTheory.PartitionPrinciple.Definability.TaggedSumPresentations

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

def tileStarVertexCarrier (Q E R : ZFSet.{u}) : ZFSet.{u} := taggedSumCarrier Q (ZFSet.prod E R)
def tileStarEdgeCarrier (E R S : ZFSet.{u}) : ZFSet.{u} := taggedSumCarrier (ZFSet.prod E R) (ZFSet.prod E S)
def tileStarDartCarrier (E R S : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod (tileStarEdgeCarrier E R S) (natSetCode 2)

def signedPresentation {A : Type u} (s : Presentation A) : Presentation (A × Bool) where
  carrier := ZFSet.prod s.carrier (natSetCode 2)
  encode p := ZFSet.pair (s.encode p.1) (externalSignCode p.2)
  injective := by
    intro p q equal
    have parts := ZFSet.pair_inj.1 equal
    exact Prod.ext (s.injective parts.1) (externalSignCode_injective parts.2)
  mem_carrier z := by
    constructor
    · intro hz
      obtain ⟨a, ha, b, hb, equal⟩ := ZFSet.mem_prod.1 hz
      obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
      obtain ⟨b, rfl⟩ := (mem_natTwo_iff_externalSignCode b).1 hb
      exact ⟨(a, b), equal.symm⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ZFSet.pair_mem_prod.2 ⟨s.encode_mem a, (mem_natTwo_iff_externalSignCode _).2 ⟨b, rfl⟩⟩

variable {J S R : Type u} [Group J]
variable (e : Presentation (External J S)) (s : Presentation S) (r : Presentation R)
variable (q : Presentation (Vertex J S))

noncomputable def tileStarVertexPresentation : Presentation (TileStars.Vertex J S R) := taggedSumPresentation q (e.product r)
noncomputable def tileStarEdgePresentation : Presentation (TileStars.Edge J S R) := taggedSumPresentation (e.product r) (e.product s)
noncomputable def tileStarDartPresentation : Presentation (TileStars.Dart J S R) := signedPresentation (tileStarEdgePresentation e s r)

theorem tileStarPresentations_carriers :
    (tileStarVertexPresentation e r q).carrier = tileStarVertexCarrier q.carrier e.carrier r.carrier ∧
      (tileStarEdgePresentation e s r).carrier = tileStarEdgeCarrier e.carrier r.carrier s.carrier ∧
      (tileStarDartPresentation e s r).carrier = tileStarDartCarrier e.carrier r.carrier s.carrier := ⟨rfl, rfl, rfl⟩

theorem tileStarVertexPresentation_encode (v : TileStars.Vertex J S R) :
    (tileStarVertexPresentation e r q).encode v = match v with
      | .inl c => ZFSet.pair (natSetCode 0) (q.encode c)
      | .inr c => ZFSet.pair (natSetCode 1) (ZFSet.pair (e.encode c.1) (r.encode c.2)) := by
  cases v <;> rfl

theorem tileStarDartPresentation_encode (d : TileStars.Dart J S R) :
    (tileStarDartPresentation e s r).encode d =
      ZFSet.pair (match d.1 with
        | .inl c => ZFSet.pair (natSetCode 0) (ZFSet.pair (e.encode c.1) (r.encode c.2))
        | .inr c => ZFSet.pair (natSetCode 1) (ZFSet.pair (e.encode c.1) (s.encode c.2))) (externalSignCode d.2) := by
  rcases d with ⟨edge, b⟩
  cases edge <;> rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tileStarCarriers_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q E R S : ZFSet.{u}} (hQ : Q ∈ M.sets) (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) :
    tileStarVertexCarrier Q E R ∈ M.sets ∧ tileStarEdgeCarrier E R S ∈ M.sets ∧ tileStarDartCarrier E R S ∈ M.sets := by
  have center := M.prod_mem pairing unions powers separation hE hR
  have edge := M.taggedSumCarrier_mem pairing unions powers separation center (M.prod_mem pairing unions powers separation hE hS)
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have two : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions one one
  exact ⟨M.taggedSumCarrier_mem pairing unions powers separation hQ center, edge,
    M.prod_mem pairing unions powers separation edge two⟩

end TransitiveGround

end

open SetFormula
universe u

def TileStarSourceEntry (E R S Q Edges C request generators multiplication d v : ZFSet.{u}) : Prop :=
  ∃ e ∈ Edges,
    (∃ w ∈ E, ∃ r ∈ R, e = ZFSet.pair (natSetCode 0) (ZFSet.pair w r) ∧
      ((d = ZFSet.pair e (natSetCode 1) ∧ ∃ q ∈ Q, ZFSet.pair w q ∈ C ∧ v = ZFSet.pair (natSetCode 0) q) ∨
       (d = ZFSet.pair e (natSetCode 0) ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r)))) ∨
    (∃ w ∈ E, ∃ s ∈ S, e = ZFSet.pair (natSetCode 1) (ZFSet.pair w s) ∧
      ((d = ZFSet.pair e (natSetCode 1) ∧ ∃ r ∈ R, ZFSet.pair s r ∈ request ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r)) ∨
       (d = ZFSet.pair e (natSetCode 0) ∧ ∃ k ∈ E, ∃ a ∈ E, ∃ q ∈ Q,
         ZFSet.pair s k ∈ generators ∧ ZFSet.pair (ZFSet.pair w k) a ∈ multiplication ∧
         ZFSet.pair a q ∈ C ∧ v = ZFSet.pair (natSetCode 0) q)))

def TileStarReverseEntry (Edges d v : ZFSet.{u}) : Prop :=
  ∃ e ∈ Edges,
    (d = ZFSet.pair e (natSetCode 0) ∧ v = ZFSet.pair e (natSetCode 1)) ∨
    (d = ZFSet.pair e (natSetCode 1) ∧ v = ZFSet.pair e (natSetCode 0))

noncomputable def tileStarSourceGraph (E R S Q C request generators multiplication : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ d ∈ tileStarDartCarrier E R S, ∃ v ∈ tileStarVertexCarrier Q E R,
    z = ZFSet.pair d v ∧ TileStarSourceEntry E R S Q (tileStarEdgeCarrier E R S) C request generators multiplication d v)
    (ZFSet.prod (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R))

noncomputable def tileStarReverseGraph (E R S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ d ∈ tileStarDartCarrier E R S, ∃ v ∈ tileStarDartCarrier E R S,
    z = ZFSet.pair d v ∧ TileStarReverseEntry (tileStarEdgeCarrier E R S) d v)
    (ZFSet.prod (tileStarDartCarrier E R S) (tileStarDartCarrier E R S))

noncomputable def tileStarTargetGraph (E R S Q C request generators multiplication : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (tileStarDartCarrier E R S) (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R)
    (tileStarReverseGraph E R S) (tileStarSourceGraph E R S Q C request generators multiplication)

noncomputable def dartIncidenceGraph (source target : ZFSet.{u}) : ZFSet.{u} := source ∪ target
noncomputable def dartAdjacencyGraph (D V source target : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose V D V (relationConverse D V source) target

theorem pair_mem_tileStarSourceGraph (E R S Q C request generators multiplication d v : ZFSet.{u}) :
    ZFSet.pair d v ∈ tileStarSourceGraph E R S Q C request generators multiplication ↔
      d ∈ tileStarDartCarrier E R S ∧ v ∈ tileStarVertexCarrier Q E R ∧
        TileStarSourceEntry E R S Q (tileStarEdgeCarrier E R S) C request generators multiplication d v := by
  rw [tileStarSourceGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, d', hd, v', hv, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hd, hv, entry⟩
  · rintro ⟨hd, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, d, hd, v, hv, rfl, entry⟩

theorem pair_mem_tileStarReverseGraph (E R S d v : ZFSet.{u}) :
    ZFSet.pair d v ∈ tileStarReverseGraph E R S ↔
      d ∈ tileStarDartCarrier E R S ∧ v ∈ tileStarDartCarrier E R S ∧
        TileStarReverseEntry (tileStarEdgeCarrier E R S) d v := by
  rw [tileStarReverseGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, d', hd, v', hv, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hd, hv, entry⟩
  · rintro ⟨hd, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, d, hd, v, hv, rfl, entry⟩

namespace BoundedFormula

def tileStarSourceFormula {n} (E R S Q Edges C request generators multiplication d v zero one : Fin n) : BoundedFormula n :=
  (exMem Edges (disj (exMem E.succ (exMem R.succ.succ (.conj (orderedRightTripleFormula 2 zero.succ.succ.succ 1 0) (disj (.conj (orderedPairFormula d.succ.succ.succ 2 one.succ.succ.succ) (exMem Q.succ.succ.succ (.conj (pairMembershipFormula 2 0 C.succ.succ.succ.succ) (orderedPairFormula v.succ.succ.succ.succ zero.succ.succ.succ.succ 0)))) (.conj (orderedPairFormula d.succ.succ.succ 2 zero.succ.succ.succ) (orderedRightTripleFormula v.succ.succ.succ one.succ.succ.succ 1 0)))))) (exMem E.succ (exMem S.succ.succ (.conj (orderedRightTripleFormula 2 one.succ.succ.succ 1 0) (disj (.conj (orderedPairFormula d.succ.succ.succ 2 one.succ.succ.succ) (exMem R.succ.succ.succ (.conj (pairMembershipFormula 1 0 request.succ.succ.succ.succ) (orderedRightTripleFormula v.succ.succ.succ.succ one.succ.succ.succ.succ 2 0)))) (.conj (orderedPairFormula d.succ.succ.succ 2 zero.succ.succ.succ) (exMem E.succ.succ.succ (exMem E.succ.succ.succ.succ (exMem Q.succ.succ.succ.succ.succ (.conj (pairMembershipFormula 3 2 generators.succ.succ.succ.succ.succ.succ) (.conj (tripleMembershipFormula 4 2 1 multiplication.succ.succ.succ.succ.succ.succ) (.conj (pairMembershipFormula 1 0 C.succ.succ.succ.succ.succ.succ) (orderedPairFormula v.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ 0))))))))))))))

theorem truth_tileStarSourceFormula {n} (E R S Q Edges C request generators multiplication d v zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarSourceFormula E R S Q Edges C request generators multiplication d v zero one) env ↔
      TileStarSourceEntry (env E) (env R) (env S) (env Q) (env Edges) (env C)
        (env request) (env generators) (env multiplication) (env d) (env v) := by
  simp only [tileStarSourceFormula, Truth, truth_disj, truth_exMem, truth_orderedPairFormula,
    truth_orderedRightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  unfold TileStarSourceEntry
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [hz, ho]
  rfl

def tileStarReverseFormula {n} (Edges d v zero one : Fin n) : BoundedFormula n :=
  (exMem Edges (disj (.conj (orderedPairFormula d.succ 0 zero.succ) (orderedPairFormula v.succ 0 one.succ)) (.conj (orderedPairFormula d.succ 0 one.succ) (orderedPairFormula v.succ 0 zero.succ))))

theorem truth_tileStarReverseFormula {n} (Edges d v zero one : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarReverseFormula Edges d v zero one) env ↔ TileStarReverseEntry (env Edges) (env d) (env v) := by
  simp only [tileStarReverseFormula, Truth, truth_disj, truth_exMem, truth_orderedPairFormula]
  unfold TileStarReverseEntry
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [hz, ho]

def tileStarSourceEntryFormula {n} (z D V E R S Q Edges C request generators multiplication zero one : Fin n) : BoundedFormula n :=
  exMem D (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tileStarSourceFormula E.succ.succ R.succ.succ S.succ.succ Q.succ.succ Edges.succ.succ C.succ.succ request.succ.succ generators.succ.succ multiplication.succ.succ 1 0 zero.succ.succ one.succ.succ)))

theorem truth_tileStarSourceEntryFormula {n} (z D V E R S Q Edges C request generators multiplication zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarSourceEntryFormula z D V E R S Q Edges C request generators multiplication zero one) env ↔
      ∃ d ∈ env D, ∃ v ∈ env V, env z = ZFSet.pair d v ∧
        TileStarSourceEntry (env E) (env R) (env S) (env Q) (env Edges) (env C) (env request) (env generators) (env multiplication) d v := by
  simp only [tileStarSourceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_tileStarSourceFormula E.succ.succ R.succ.succ S.succ.succ Q.succ.succ Edges.succ.succ C.succ.succ request.succ.succ generators.succ.succ multiplication.succ.succ 1 0
    zero.succ.succ one.succ.succ _ hz ho)

def tileStarReverseEntryFormula {n} (z D V Edges zero one : Fin n) : BoundedFormula n :=
  exMem D (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tileStarReverseFormula Edges.succ.succ 1 0 zero.succ.succ one.succ.succ)))

theorem truth_tileStarReverseEntryFormula {n} (z D V Edges zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarReverseEntryFormula z D V Edges zero one) env ↔
      ∃ d ∈ env D, ∃ v ∈ env V, env z = ZFSet.pair d v ∧
        TileStarReverseEntry (env Edges) d v := by
  simp only [tileStarReverseEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_tileStarReverseFormula Edges.succ.succ 1 0
    zero.succ.succ one.succ.succ _ hz ho)

end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem tileStarSourceGraph_mem {E R S Q C request generators multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hrequest : request ∈ M.sets) (hgenerators : generators ∈ M.sets) (hmultiplication : multiplication ∈ M.sets) :
    tileStarSourceGraph E R S Q C request generators multiplication ∈ M.sets := by
  have hzero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have hone : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hzero hzero
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hQ hE hR hS
  have hD := carriers.2.2
  have hV := carriers.1
  have hEdges := carriers.2.1
  let params := extend (tileStarDartCarrier E R S) (extend (tileStarVertexCarrier Q E R) (extend (E) (extend (R) (extend (S) (extend (Q) (extend (tileStarEdgeCarrier E R S) (extend (C) (extend (request) (extend (generators) (extend (multiplication) (extend (natSetCode 0) (extend (natSetCode 1) (Fin.elim0)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13) params
    (Fin.cases hD (Fin.cases hV (Fin.cases hE (Fin.cases hR (Fin.cases hS (Fin.cases hQ (Fin.cases hEdges (Fin.cases hC (Fin.cases hrequest (Fin.cases hgenerators (Fin.cases hmultiplication (Fin.cases hzero (Fin.cases hone (fun i => Fin.elim0 i)))))))))))))) (M.prod_mem pairing unions powers separation hD hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13) (extend z params))
      (ZFSet.prod (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R)) = tileStarSourceGraph E R S Q C request generators multiplication := by
    apply ZFSet.ext
    intro z
    rw [tileStarSourceGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 _ rfl rfl)
  exact equal ▸ selected

include pairing unions powers separation in
theorem tileStarReverseGraph_mem {E R S : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) :
    tileStarReverseGraph E R S ∈ M.sets := by
  have hzero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have hone : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hzero hzero
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hE hE hR hS
  have hD := carriers.2.2
  have hV := carriers.2.2
  have hEdges := carriers.2.1
  let params := extend (tileStarDartCarrier E R S) (extend (tileStarDartCarrier E R S) (extend (tileStarEdgeCarrier E R S) (extend (natSetCode 0) (extend (natSetCode 1) (Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.tileStarReverseEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hD (Fin.cases hV (Fin.cases hEdges (Fin.cases hzero (Fin.cases hone (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hD hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.tileStarReverseEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (tileStarDartCarrier E R S) (tileStarDartCarrier E R S)) = tileStarReverseGraph E R S := by
    apply ZFSet.ext
    intro z
    rw [tileStarReverseGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_tileStarReverseEntryFormula 0 1 2 3 4 5 _ rfl rfl)
  exact equal ▸ selected

include pairing unions powers separation in
theorem tileStarTargetGraph_mem {E R S Q C request generators multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) (hQ : Q ∈ M.sets)
    (hC : C ∈ M.sets) (hrequest : request ∈ M.sets) (hgenerators : generators ∈ M.sets)
    (hmultiplication : multiplication ∈ M.sets) :
    tileStarTargetGraph E R S Q C request generators multiplication ∈ M.sets := by
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hQ hE hR hS
  exact M.relationCompose_mem pairing unions powers separation carriers.2.2 carriers.2.2 carriers.1
    (M.tileStarReverseGraph_mem pairing unions powers separation hE hR hS)
    (M.tileStarSourceGraph_mem pairing unions powers separation hE hR hS hQ hC hrequest hgenerators hmultiplication)

include pairing unions in
theorem dartIncidenceGraph_mem {source target : ZFSet.{u}}
    (hs : source ∈ M.sets) (ht : target ∈ M.sets) : dartIncidenceGraph source target ∈ M.sets :=
  M.binary_union_mem pairing unions hs ht

include pairing unions powers separation in
theorem dartAdjacencyGraph_mem {D V source target : ZFSet.{u}}
    (hD : D ∈ M.sets) (hV : V ∈ M.sets) (hs : source ∈ M.sets) (ht : target ∈ M.sets) :
    dartAdjacencyGraph D V source target ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hV hD hV
    (M.relationConverse_mem pairing unions powers separation hD hV hs) ht

end TransitiveGround

end PartitionPilot.Forcing

end OAI

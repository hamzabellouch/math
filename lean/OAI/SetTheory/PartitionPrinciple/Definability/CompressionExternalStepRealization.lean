import OAI.SetTheory.PartitionPrinciple.Geometry.ExternalTileVertexPresentation
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionStarIncidence

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

def ExternalFlatVertexWordCode
    (E S generators m zero first second q i w v : ZFSet.{u}) : Prop :=
  (i = zero ∧ v = w) ∨ ∃ s ∈ S, ∃ k ∈ E,
    ((i = first ∧ s = ZFSet.pair q zero) ∨ (i = second ∧ s = ZFSet.pair q first)) ∧
      ZFSet.pair s k ∈ generators ∧ ZFSet.pair (ZFSet.pair w k) v ∈ m

noncomputable def externalFlatPlacements (E Requests U V S generators m : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w ∈ E, ∃ a ∈ V, ∃ b ∈ ZFSet.prod E U,
    ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ v ∈ E,
      z = ZFSet.pair (ZFSet.pair w a) b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
        ExternalFlatVertexWordCode E S generators m (natSetCode 0) (natSetCode 1) (natSetCode 2) q i w v)
    (ZFSet.prod (ZFSet.prod E V) (ZFSet.prod E U))

theorem triple_mem_externalFlatPlacements (E Requests U V S generators m w a b : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair w a) b ∈ externalFlatPlacements E Requests U V S generators m ↔
      w ∈ E ∧ a ∈ V ∧ b ∈ ZFSet.prod E U ∧
        ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ v ∈ E,
          a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
            ExternalFlatVertexWordCode E S generators m (natSetCode 0) (natSetCode 1) (natSetCode 2) q i w v := by
  rw [externalFlatPlacements, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w', hw, a', ha, b', hb, q, hq, i, hi, x, hx, v, hv, equal, left, right, word⟩
    obtain ⟨wa, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 wa
    exact ⟨hw, ha, hb, q, hq, i, hi, x, hx, v, hv, left, right, word⟩
  · rintro ⟨hw, ha, hb, q, hq, i, hi, x, hx, v, hv, left, right, word⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hw, ha⟩, hb⟩,
      w, hw, a, ha, b, hb, q, hq, i, hi, x, hx, v, hv, rfl, left, right, word⟩

namespace BoundedFormula

def externalFlatVertexWordFormula {n} (E S generators m zero first second q i w v : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i zero) (.equal v w))
    (exMem S (exMem E.succ
      (.conj (disj (.conj (.equal i.succ.succ first.succ.succ)
          (orderedPairFormula 1 q.succ.succ zero.succ.succ))
        (.conj (.equal i.succ.succ second.succ.succ) (orderedPairFormula 1 q.succ.succ first.succ.succ)))
        (.conj (pairMembershipFormula 1 0 generators.succ.succ)
          (tripleMembershipFormula w.succ.succ 0 v.succ.succ m.succ.succ)))))

theorem truth_externalFlatVertexWordFormula {n}
    (E S generators m zero first second q i w v : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatVertexWordFormula E S generators m zero first second q i w v) env ↔
      ExternalFlatVertexWordCode (env E) (env S) (env generators) (env m) (env zero) (env first) (env second)
        (env q) (env i) (env w) (env v) := by
  simp only [externalFlatVertexWordFormula, Truth, truth_exMem, truth_disj, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalFlatVertexWordCode]
  rfl

def externalFlatPlacementEntryFormula {n}
    (z E Requests Tags U V L S generators m zero first second : Fin n) : BoundedFormula n :=
  exMem E (exMem V.succ (exMem L.succ.succ (exMem Requests.succ.succ.succ
    (exMem Tags.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem E.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ.succ 6 5 4)
          (.conj (orderedTripleFormula 5 3 2 1)
            (.conj (orderedPairFormula 4 0 1)
              (externalFlatVertexWordFormula E.succ.succ.succ.succ.succ.succ.succ
                S.succ.succ.succ.succ.succ.succ.succ generators.succ.succ.succ.succ.succ.succ.succ
                m.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ
                first.succ.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ.succ
                3 2 6 0))))))))))

theorem truth_externalFlatPlacementEntryFormula {n}
    (z E Requests Tags U V L S generators m zero first second : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatPlacementEntryFormula z E Requests Tags U V L S generators m zero first second) env ↔
      ∃ w ∈ env E, ∃ a ∈ env V, ∃ b ∈ env L, ∃ q ∈ env Requests, ∃ i ∈ env Tags,
        ∃ x ∈ env U, ∃ v ∈ env E,
          env z = ZFSet.pair (ZFSet.pair w a) b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
            ExternalFlatVertexWordCode (env E) (env S) (env generators) (env m) (env zero) (env first) (env second)
              q i w v := by
  simp only [externalFlatPlacementEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_externalFlatVertexWordFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalFlatPlacements_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E Requests U V S generators m : ZFSet.{u}}
    (hE : E ∈ M.sets) (hRequests : Requests ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets)
    (hS : S ∈ M.sets) (hGenerators : generators ∈ M.sets) (hm : m ∈ M.sets) :
    externalFlatPlacements E Requests U V S generators m ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  have hTags : externalRequestTags ∈ M.sets :=
    M.insert_mem pairing unions hZero (M.insert_mem pairing unions hFirst single)
  have hL := M.prod_mem pairing unions powers separation hE hU
  let params := extend E (extend Requests (extend externalRequestTags (extend U (extend V
    (extend (ZFSet.prod E U) (extend S (extend generators (extend m (extend (natSetCode 0)
      (extend (natSetCode 1) (extend (natSetCode 2) Fin.elim0)))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalFlatPlacementEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) params
    (Fin.cases hE (Fin.cases hRequests (Fin.cases hTags (Fin.cases hU (Fin.cases hV (Fin.cases hL
      (Fin.cases hS (Fin.cases hGenerators (Fin.cases hm (Fin.cases hZero
        (Fin.cases hFirst (Fin.cases hSecond (fun i => Fin.elim0 i)))))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hE hV) hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalFlatPlacementEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) (extend z params))
      (ZFSet.prod (ZFSet.prod E V) (ZFSet.prod E U)) = externalFlatPlacements E Requests U V S generators m := by
    apply ZFSet.ext
    intro z
    rw [externalFlatPlacements, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalFlatPlacementEntryFormula
      0 1 2 3 4 5 6 7 8 9 10 11 12 _)
  exact equal ▸ selected

end TransitiveGround





def ExternalFlatCoordinateCode (E U G old m A a b : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ k ∈ E, ∃ v ∈ E, ∃ j ∈ G, ∃ x ∈ U, ∃ y ∈ U,
    ZFSet.pair j k ∈ old ∧ ZFSet.pair (ZFSet.pair w k) v ∈ m ∧
      ZFSet.pair (ZFSet.pair j x) y ∈ A ∧ a = ZFSet.pair v x ∧ b = ZFSet.pair w y

def ExternalFlatTileStepCode (E V placements overlaps a b : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ x ∈ V, ∃ y ∈ V,
    ZFSet.pair (ZFSet.pair w x) a ∈ placements ∧
      ZFSet.pair (ZFSet.pair w y) b ∈ placements ∧ ZFSet.pair x y ∈ overlaps

def ExternalFlatStepCode (E U G V old m A placements overlaps a b : ZFSet.{u}) : Prop :=
  (ExternalFlatCoordinateCode E U G old m A a b ∨ ExternalFlatTileStepCode E V placements overlaps a b) ∨
  (ExternalFlatCoordinateCode E U G old m A b a ∨ ExternalFlatTileStepCode E V placements overlaps b a)

theorem ExternalFlatStepCode.symm {E U G V old m A placements overlaps a b : ZFSet.{u}}
    (step : ExternalFlatStepCode E U G V old m A placements overlaps a b) :
    ExternalFlatStepCode E U G V old m A placements overlaps b a := Or.symm step

noncomputable def externalFlatStepGraph (E U G V old m A placements overlaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ ZFSet.prod E U, ∃ b ∈ ZFSet.prod E U, z = ZFSet.pair a b ∧
    ExternalFlatStepCode E U G V old m A placements overlaps a b)
    (ZFSet.prod (ZFSet.prod E U) (ZFSet.prod E U))

theorem pair_mem_externalFlatStepGraph (E U G V old m A placements overlaps a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ externalFlatStepGraph E U G V old m A placements overlaps ↔
      a ∈ ZFSet.prod E U ∧ b ∈ ZFSet.prod E U ∧
        ExternalFlatStepCode E U G V old m A placements overlaps a b := by
  rw [externalFlatStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a', ha, b', hb, equal, step⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, step⟩
  · rintro ⟨ha, hb, step⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, rfl, step⟩

theorem externalFlatStepGraph_subset (E U G V old m A placements overlaps : ZFSet.{u}) :
    externalFlatStepGraph E U G V old m A placements overlaps ⊆
      ZFSet.prod (ZFSet.prod E U) (ZFSet.prod E U) :=
  fun _ member => (ZFSet.mem_sep.1 member).1

theorem externalFlatStepGraph_symmetric {E U G V old m A placements overlaps a b : ZFSet.{u}}
    (entry : ZFSet.pair a b ∈ externalFlatStepGraph E U G V old m A placements overlaps) :
    ZFSet.pair b a ∈ externalFlatStepGraph E U G V old m A placements overlaps := by
  obtain ⟨ha, hb, step⟩ := (pair_mem_externalFlatStepGraph _ _ _ _ _ _ _ _ _ _ _).1 entry
  exact (pair_mem_externalFlatStepGraph _ _ _ _ _ _ _ _ _ _ _).2 ⟨hb, ha, step.symm⟩

namespace BoundedFormula

def externalFlatCoordinateFormula {n} (E U G old m A a b : Fin n) : BoundedFormula n :=
  exMem E (exMem E.succ (exMem E.succ.succ (exMem G.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (.conj (pairMembershipFormula 2 4 old.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 5 4 3 m.succ.succ.succ.succ.succ.succ)
          (.conj (tripleMembershipFormula 2 1 0 A.succ.succ.succ.succ.succ.succ)
            (.conj (orderedPairFormula a.succ.succ.succ.succ.succ.succ 3 1)
              (orderedPairFormula b.succ.succ.succ.succ.succ.succ 5 0))))))))))

def externalFlatTileStepFormula {n} (E V placements overlaps a b : Fin n) : BoundedFormula n :=
  exMem E (exMem V.succ (exMem V.succ.succ
    (.conj (tripleMembershipFormula 2 1 a.succ.succ.succ placements.succ.succ.succ)
      (.conj (tripleMembershipFormula 2 0 b.succ.succ.succ placements.succ.succ.succ)
        (pairMembershipFormula 1 0 overlaps.succ.succ.succ)))))

theorem truth_externalFlatCoordinateFormula {n} (E U G old m A a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatCoordinateFormula E U G old m A a b) env ↔
      ExternalFlatCoordinateCode (env E) (env U) (env G) (env old) (env m) (env A) (env a) (env b) := by
  simp only [externalFlatCoordinateFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalFlatCoordinateCode]
  rfl

theorem truth_externalFlatTileStepFormula {n} (E V placements overlaps a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatTileStepFormula E V placements overlaps a b) env ↔
      ExternalFlatTileStepCode (env E) (env V) (env placements) (env overlaps) (env a) (env b) := by
  simp only [externalFlatTileStepFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, ExternalFlatTileStepCode]
  rfl

def externalFlatStepFormula {n} (E U G V old m A placements overlaps a b : Fin n) : BoundedFormula n :=
  disj (disj (externalFlatCoordinateFormula E U G old m A a b) (externalFlatTileStepFormula E V placements overlaps a b))
    (disj (externalFlatCoordinateFormula E U G old m A b a) (externalFlatTileStepFormula E V placements overlaps b a))

theorem truth_externalFlatStepFormula {n}
    (E U G V old m A placements overlaps a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatStepFormula E U G V old m A placements overlaps a b) env ↔
      ExternalFlatStepCode (env E) (env U) (env G) (env V) (env old) (env m) (env A)
        (env placements) (env overlaps) (env a) (env b) := by
  simp only [externalFlatStepFormula, truth_disj, truth_externalFlatCoordinateFormula,
    truth_externalFlatTileStepFormula, ExternalFlatStepCode]

def externalFlatStepEntryFormula {n} (z L E U G V old m A placements overlaps : Fin n) : BoundedFormula n :=
  exMem L (exMem L.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (externalFlatStepFormula E.succ.succ U.succ.succ G.succ.succ V.succ.succ old.succ.succ
      m.succ.succ A.succ.succ placements.succ.succ overlaps.succ.succ 1 0)))

theorem truth_externalFlatStepEntryFormula {n}
    (z L E U G V old m A placements overlaps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatStepEntryFormula z L E U G V old m A placements overlaps) env ↔
      ∃ a ∈ env L, ∃ b ∈ env L, env z = ZFSet.pair a b ∧
        ExternalFlatStepCode (env E) (env U) (env G) (env V) (env old) (env m) (env A)
          (env placements) (env overlaps) a b := by
  simp only [externalFlatStepEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_externalFlatStepFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalFlatStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E U G V old m A placements overlaps : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hG : G ∈ M.sets) (hV : V ∈ M.sets)
    (hOld : old ∈ M.sets) (hm : m ∈ M.sets) (hA : A ∈ M.sets)
    (hPlacements : placements ∈ M.sets) (hOverlaps : overlaps ∈ M.sets) :
    externalFlatStepGraph E U G V old m A placements overlaps ∈ M.sets := by
  have hL := M.prod_mem pairing unions powers separation hE hU
  let params := extend (ZFSet.prod E U) (extend E (extend U (extend G (extend V (extend old
    (extend m (extend A (extend placements (extend overlaps Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hL (Fin.cases hE (Fin.cases hU (Fin.cases hG (Fin.cases hV (Fin.cases hOld
      (Fin.cases hm (Fin.cases hA (Fin.cases hPlacements (Fin.cases hOverlaps (fun i => Fin.elim0 i)))))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod (ZFSet.prod E U) (ZFSet.prod E U)) = externalFlatStepGraph E U G V old m A placements overlaps := by
    apply ZFSet.ext
    intro z
    rw [externalFlatStepGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalFlatStepEntryFormula 0 1 2 3 4 5 6 7 8 9 10 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (g : Presentation J)
variable (v : Presentation (Sigma fun r => Option (f.Child r) × A))
variable {oldGraph mulGraph actGraph placements overlaps : ZFSet.{u}}
variable (oldEntries : ∀ j w, ZFSet.pair (g.encode j) (s.encode w) ∈ oldGraph ↔ old J f.Letters j = w)
variable (mulEntries : ∀ w k l, ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode l) ∈ mulGraph ↔ w * k = l)
variable (actEntries : ∀ j x y, ZFSet.pair (ZFSet.pair (g.encode j) (t.encode x)) (t.encode y) ∈ actGraph ↔ (a.iso j).toFun x = y)
variable (placed : ∀ w u z, ZFSet.pair (ZFSet.pair (s.encode w) (v.encode u)) ((s.product t).encode z) ∈ placements ↔
  z = (f.flatWord w u.1 u.2.1, u.2.2))
variable (overlapSource : ∀ u w, ZFSet.pair (v.encode u) (v.encode w) ∈ overlaps → u.1 = w.1)
variable (overlapEntries : ∀ r i j x y,
  ZFSet.pair (v.encode ⟨r, i, x⟩) (v.encode ⟨r, j, y⟩) ∈ overlaps ↔
    (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y)

include oldEntries mulEntries actEntries in
theorem externalFlatCoordinate_to_step (x y : f.FlatLabel (J := J))
    (code : ExternalFlatCoordinateCode s.carrier t.carrier g.carrier oldGraph mulGraph actGraph
      ((s.product t).encode x) ((s.product t).encode y)) : f.FlatStep a x y := by
  obtain ⟨w, hw, k, hk, l, hl, j, hj, b, hb, c, hc, oldEntry, mulEntry, actEntry, left, right⟩ := code
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
  obtain ⟨l, rfl⟩ := (s.mem_carrier l).1 hl
  obtain ⟨j, rfl⟩ := (g.mem_carrier j).1 hj
  obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
  obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
  have hx : x = (l, b) := (s.product t).injective left
  have hy : y = (w, c) := (s.product t).injective right
  rw [hx, hy, ← (mulEntries w k l).1 mulEntry, ← (oldEntries j k).1 oldEntry,
    ← (actEntries j b c).1 actEntry]
  exact .coordinate w j b

include placed overlapSource overlapEntries in
theorem externalFlatTileStep_to_step (x y : f.FlatLabel (J := J))
    (code : ExternalFlatTileStepCode s.carrier v.carrier placements overlaps
      ((s.product t).encode x) ((s.product t).encode y)) : f.FlatStep a x y := by
  obtain ⟨w, hw, u, hu, z, hz, left, right, equal⟩ := code
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  obtain ⟨⟨r, i, b⟩, rfl⟩ := (v.mem_carrier u).1 hu
  obtain ⟨⟨r', j, c⟩, rfl⟩ := (v.mem_carrier z).1 hz
  have same : r = r' := overlapSource ⟨r, i, b⟩ ⟨r', j, c⟩ equal
  cases same
  rw [(placed w ⟨r, i, b⟩ x).1 left, (placed w ⟨r, j, c⟩ y).1 right]
  exact .tile w r i j b c ((overlapEntries r i j b c).1 equal)

include oldEntries mulEntries actEntries placed overlapSource overlapEntries in
theorem pair_mem_externalFlatStepGraph_iff (x y : f.FlatLabel (J := J)) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      externalFlatStepGraph s.carrier t.carrier g.carrier v.carrier oldGraph mulGraph actGraph placements overlaps ↔
        f.FlatStep a x y := by
  rw [pair_mem_externalFlatStepGraph]
  constructor
  · rintro ⟨_, _, h⟩
    rcases h with (coordinate | tile) | (coordinate | tile)
    · exact externalFlatCoordinate_to_step f a s t g oldEntries mulEntries actEntries x y coordinate
    · exact externalFlatTileStep_to_step f a s t v placed overlapSource overlapEntries x y tile
    · exact (externalFlatCoordinate_to_step f a s t g oldEntries mulEntries actEntries y x coordinate).symm
    · exact (externalFlatTileStep_to_step f a s t v placed overlapSource overlapEntries y x tile).symm
  · intro h
    refine ⟨(s.product t).encode_mem x, (s.product t).encode_mem y, ?_⟩
    induction h with
    | coordinate w j b =>
      apply Or.inl
      apply Or.inl
      exact ⟨s.encode w, s.encode_mem w, s.encode (old J f.Letters j), s.encode_mem _,
        s.encode (w * old J f.Letters j), s.encode_mem _, g.encode j, g.encode_mem j,
        t.encode b, t.encode_mem b, t.encode ((a.iso j).toFun b), t.encode_mem _,
        (oldEntries j _).2 rfl, (mulEntries w _ _).2 rfl, (actEntries j b _).2 rfl, rfl, rfl⟩
    | tile w r i j b c equal =>
      apply Or.inl
      apply Or.inr
      exact ⟨s.encode w, s.encode_mem w, v.encode ⟨r, i, b⟩, v.encode_mem _,
        v.encode ⟨r, j, c⟩, v.encode_mem _, (placed w ⟨r, i, b⟩ _).2 rfl,
        (placed w ⟨r, j, c⟩ _).2 rfl, (overlapEntries r i j b c).2 equal⟩
    | symm h ih => exact ih.symm

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalVertices (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalTileVertices (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRectangles P G r μ A) (completion.algebra.union.fields 0)

noncomputable def externalOverlaps (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalRequestOverlapGraph (externalRequestCarrier I P (externalRectangles P G r μ A))
    P G (externalRectangles P G r μ A) completion.externalMaps
    (completion.algebra.union.fields 0) (completion.algebra.union.fields 1) (completion.algebra.union.fields 12)

noncomputable def externalPlacements (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  externalFlatPlacements (M.externalGroupCarrier G S m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalVertices P r μ A) S
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)

noncomputable def externalFlatSteps (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  externalFlatStepGraph (M.externalGroupCarrier G S m one) (completion.algebra.union.fields 0) G
    (completion.externalVertices P r μ A) (M.externalOldInclusion G S m one)
    (M.externalGroupMultiplication G S m one) (completion.algebra.union.fields 12)
    (completion.externalPlacements P r μ A) (completion.externalOverlaps P r μ A)

noncomputable def externalFlatEquivalence (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  M.finitePathClosure
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatSteps P r μ A)

noncomputable def externalPointCarrier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatEquivalence P r μ A)

noncomputable def externalPointClassifier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatEquivalence P r μ A)

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)

include data

theorem flat_relations_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    completion.externalVertices P r μ A ∈ M.sets ∧ completion.externalOverlaps P r μ A ∈ M.sets ∧
      completion.externalPlacements P r μ A ∈ M.sets ∧ completion.externalFlatSteps P r μ A ∈ M.sets := by
  have vertices := M.externalTileVertices_mem pairing unions powers separation
    data.words.requests_ground data.words.rectangles_ground (completion.algebra.union.ground 0)
  have overlaps := M.externalRequestOverlapGraph_mem pairing unions powers separation
    data.words.requests_ground hP hG data.words.rectangles_ground data.words.maps_ground
    (completion.algebra.union.ground 0) (completion.algebra.union.ground 1) (completion.algebra.union.ground 12)
  have placements := M.externalFlatPlacements_mem pairing unions powers separation
    data.group.carrier_mem data.words.requests_ground (completion.algebra.union.ground 0) vertices
    data.words.letters_ground data.generators_ground data.group.multiplication_mem
  exact ⟨vertices, overlaps, placements, M.externalFlatStepGraph_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0) hG vertices data.old_inclusion_ground
    data.group.multiplication_mem (completion.algebra.union.ground 12) placements overlaps⟩

theorem point_quotient_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    let L := ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)
    completion.externalFlatEquivalence P r μ A ∈ M.sets ∧
      EquivalenceRelationCode L (completion.externalFlatEquivalence P r μ A) ∧
      completion.externalPointCarrier P r μ A ∈ M.sets ∧ completion.externalPointClassifier P r μ A ∈ M.sets ∧
      ZFSet.IsFunc L (completion.externalPointCarrier P r μ A) (completion.externalPointClassifier P r μ A) ∧
      (∀ C ∈ completion.externalPointCarrier P r μ A, ∃ x ∈ L,
        ZFSet.pair x C ∈ completion.externalPointClassifier P r μ A) ∧
      (∀ x y C D, ZFSet.pair x C ∈ completion.externalPointClassifier P r μ A →
        ZFSet.pair y D ∈ completion.externalPointClassifier P r μ A →
          (C = D ↔ ZFSet.pair x y ∈ completion.externalFlatEquivalence P r μ A)) := by
  dsimp only
  let L := ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.algebra.union.fields 0)
  let p := SetMembers.presentation L
  let relation : SetMembers L → SetMembers L → Prop := fun x y =>
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ completion.externalFlatSteps P r μ A
  have hL : L ∈ M.sets := M.prod_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0)
  exact M.finitePathQuotient_spec pairing unions separation infinite p relation (fun _ _ => Iff.rfl) hL powers
    (data.flat_relations_ground pairing unions powers separation hP hG).2.2.2
    (fun _ _ step => externalFlatStepGraph_symmetric step)

end GroundExternalGeometryInputs
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

local notation "f" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "Rects" => externalRectangles P0 G r0 μ0 A0
local notation "Requests" => externalRequestCarrier I P0 Rects
local notation "vcode" => completion.externalFamilyVertexCode group oldAction compression

theorem externalFamily_overlapCode_iff (r : ExternalRequestIndex I P0 Rects)
    (i j : Option ((f).Child r)) (x y : SetMembers U) :
    ExternalRequestOverlapCode P0 G Rects completion.externalMaps (⋃₀ ⋃₀ completion.externalMaps) ru au
      (natSetCode 0) (natSetCode 1) (natSetCode 2) (externalRequestIndexCode r)
      (vcode r i) (SetMembers.raw x) (vcode r j) (SetMembers.raw y) ↔
      ((f).flatVertex r i).toFun x = ((f).flatVertex r j).toFun y := by
  rcases r with task | (point | rect)
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩ <;> rcases j with _ | ⟨⟨⟨⟩⟩⟩
    all_goals simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
      externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
      completion.externalOverlapForward_compression, natSetCode_injective.eq_iff]
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inl task) none x y).symm
    · simpa using (completion.externalFamily_compression_overlap group oldAction compression task x y).symm
    · simpa only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, true_and, or_false, false_or, eq_comm] using
        (completion.externalFamily_compression_overlap group oldAction compression task y x).symm
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inl task) (some ⟨()⟩) x y).symm
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩ <;> rcases j with _ | ⟨⟨⟨⟩⟩⟩
    all_goals simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
      externalFamilyVertexCode_root, externalFamilyVertexCode_separation,
      completion.externalOverlapForward_separation, natSetCode_injective.eq_iff]
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inl point)) none x y).symm
    · simpa using (completion.externalFamily_separation_overlap group oldAction compression point x y).symm
    · simpa only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, true_and, or_false, false_or, eq_comm] using
        (completion.externalFamily_separation_overlap group oldAction compression point y x).symm
    · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inl point)) (some ⟨()⟩) x y).symm
  · rcases i with _ | ⟨⟨a⟩⟩ <;> rcases j with _ | ⟨⟨b⟩⟩
    · simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) none x y).symm
    · cases b <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, ite_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa using (completion.externalFamily_rectangle_first_overlap group oldAction compression rect x y).symm
      · simpa using (completion.externalFamily_rectangle_second_overlap group oldAction compression rect x y).symm
    · cases a <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_root, externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, ite_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa [eq_comm] using (completion.externalFamily_rectangle_first_overlap group oldAction compression rect y x).symm
      · simpa [eq_comm] using (completion.externalFamily_rectangle_second_overlap group oldAction compression rect y x).symm
    · cases a <;> cases b <;> simp only [ExternalRequestOverlapCode, externalRequestIndexCode,
        externalFamilyVertexCode_rectangle, Bool.false_eq_true, ite_false, ite_true,
        completion.externalOverlapForward_rectangle, natSetCode_injective.eq_iff]
      · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) (some ⟨false⟩) x y).symm
      · simpa using (completion.externalFamily_rectangle_children_overlap group oldAction compression rect x y).symm
      · simpa [eq_comm] using (completion.externalFamily_rectangle_children_overlap group oldAction compression rect y x).symm
      · simpa using (completion.externalFamily_diagonal_iff group oldAction compression (.inr (.inr rect)) (some ⟨true⟩) x y).symm

theorem externalFamilyVertexCode_mem_tags (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((f).Child r)) : vcode r i ∈ externalRequestTags := by
  have range := (completion.externalFamilyVertexCode_range group oldAction compression r _).2 ⟨i, rfl⟩
  rcases range with equal | equal | ⟨_, equal⟩ <;> rw [equal] <;> simp [externalRequestTags]

theorem externalOverlaps_same_request
    (x y : Sigma fun r : ExternalRequestIndex I P0 Rects => Option ((f).Child r) × SetMembers U)
    (entry : ZFSet.pair
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode x)
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode y) ∈
        completion.externalOverlaps P0 r0 μ0 A0) : x.1 = y.1 := by
  obtain ⟨_, _, q, _, i, _, a, _, j, _, b, _, left, right, _⟩ :=
    (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).1 entry
  exact externalRequestIndexCode_injective I P0 Rects
    (((ZFSet.pair_inj.1 (ZFSet.pair_inj.1 left).1).1).trans
      ((ZFSet.pair_inj.1 (ZFSet.pair_inj.1 right).1).1).symm)

theorem externalOverlaps_entry_iff (r : ExternalRequestIndex I P0 Rects)
    (i j : Option ((f).Child r)) (x y : SetMembers U) :
    ZFSet.pair
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, i, x⟩)
      ((completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, j, y⟩) ∈
        completion.externalOverlaps P0 r0 μ0 A0 ↔
      ((f).flatVertex r i).toFun x = ((f).flatVertex r j).toFun y := by
  rw [← completion.externalFamily_overlapCode_iff group oldAction compression]
  constructor
  · intro entry
    obtain ⟨_, _, q, _, i', _, a, _, j', _, b, _, left, right, code⟩ :=
      (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).1 entry
    obtain ⟨leftPair, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 leftPair
    obtain ⟨rightPair, rfl⟩ := ZFSet.pair_inj.1 right
    obtain ⟨_, rfl⟩ := ZFSet.pair_inj.1 rightPair
    exact code
  · intro code
    exact (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).2
      ⟨(completion.externalFamilyTileVertexPresentation group oldAction compression).encode_mem ⟨r, i, x⟩,
        (completion.externalFamilyTileVertexPresentation group oldAction compression).encode_mem ⟨r, j, y⟩,
        externalRequestIndexCode r, (externalRequestPresentation I P0 Rects).encode_mem r,
        vcode r i, completion.externalFamilyVertexCode_mem_tags group oldAction compression r i,
        SetMembers.raw x, SetMembers.raw_mem x,
        vcode r j, completion.externalFamilyVertexCode_mem_tags group oldAction compression r j,
        SetMembers.raw y, SetMembers.raw_mem y, rfl, rfl, code⟩

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
local notation "family" => completion.externalFamily group oldAction compression
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction compression
local notation "vertices" => completion.externalFamilyTileVertexPresentation group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "Rects" => externalRectangles P0 G r0 μ0 A0
local notation "S" => externalChildLetters I P0 Rects
local notation "E" => M.externalGroupCarrier G S m one
local notation "vcode" => completion.externalFamilyVertexCode group oldAction compression

theorem externalFamily_vertex_letter (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((family).Child r)) (s : ZFSet.{u}) :
    ((vcode r i = natSetCode 1 ∧ s = ZFSet.pair (externalRequestIndexCode r) (natSetCode 0)) ∨
      (vcode r i = natSetCode 2 ∧ s = ZFSet.pair (externalRequestIndexCode r) (natSetCode 1))) ↔
      ∃ child : (family).Child r, i = some child ∧ s = (letters).encode ⟨r, child⟩ := by
  rcases r with task | (point | rect)
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · constructor
      · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
        · exact ⟨⟨()⟩, rfl, equal⟩
        · have bad : (1 : Nat) = 2 := natSetCode_injective equal
          omega
      · rintro ⟨⟨⟨⟩⟩, _, equal⟩
        exact Or.inl ⟨rfl, equal⟩
  · rcases i with _ | ⟨⟨⟨⟩⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · constructor
      · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
        · exact ⟨⟨()⟩, rfl, equal⟩
        · have bad : (1 : Nat) = 2 := natSetCode_injective equal
          omega
      · rintro ⟨⟨⟨⟩⟩, _, equal⟩
        exact Or.inl ⟨rfl, equal⟩
  · rcases i with _ | ⟨⟨b⟩⟩
    · simp [externalFamilyVertexCode_root, natSetCode_injective.eq_iff]
    · cases b
      · constructor
        · rintro (⟨_, equal⟩ | ⟨equal, _⟩)
          · exact ⟨⟨false⟩, rfl, equal⟩
          · have bad : (1 : Nat) = 2 := natSetCode_injective equal
            omega
        · rintro ⟨child, equal, code⟩
          have same := Option.some.inj equal
          subst child
          exact Or.inl ⟨rfl, code⟩
      · constructor
        · rintro (⟨equal, _⟩ | ⟨_, equal⟩)
          · have bad : (2 : Nat) = 1 := natSetCode_injective equal
            omega
          · exact ⟨⟨true⟩, rfl, equal⟩
        · rintro ⟨child, equal, code⟩
          have same := Option.some.inj equal
          subst child
          exact Or.inr ⟨rfl, code⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets)
variable (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction compression
  pairing unions powers separation infinite hG hLetters
include pairing unions powers separation infinite hG hLetters

theorem externalFlatVertexWordCode_iff (r : ExternalRequestIndex I P0 Rects)
    (i : Option ((family).Child r)) :
    letI := group.toGroup
    ∀ w v : External (SetMembers G) (family).Letters,
    ExternalFlatVertexWordCode E S (M.externalChildGenerators G S m one)
      (M.externalGroupMultiplication G S m one) (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (externalRequestIndexCode r) (vcode r i) ((sGroup).encode w) ((sGroup).encode v) ↔
        v = (family).flatWord w r i := by
  let := group.toGroup
  intro w v
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have generators := completion.externalFamilyGroupPresentation_generators group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction compression
    pairing unions powers separation infinite hG hLetters
  constructor
  · rintro (⟨root, equal⟩ | ⟨letter, _, k, hk, childFields, gen, mul⟩)
    · have vertex : i = none := completion.externalFamilyVertexCode_injective group oldAction compression r root
      subst i
      exact (sGroup).injective equal
    · obtain ⟨child, rfl, rfl⟩ := (completion.externalFamily_vertex_letter group oldAction compression r i letter).1 childFields
      obtain ⟨g, rfl⟩ := ((sGroup).mem_carrier k).1 (carrier.symm ▸ hk)
      rw [generators] at gen
      have generatorEq := ((letters).pair_mem_graph (sGroup) _ ⟨r, child⟩ g).1 gen
      rw [multiplication] at mul
      have product := (((sGroup).product (sGroup)).pair_mem_graph (sGroup) (fun p => p.1 * p.2) (w, g) v).1 mul
      exact product.symm.trans (congrArg (fun g => w * g) generatorEq.symm)
  · intro equal
    subst v
    cases i with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some child =>
      let g := generator (SetMembers G) (family).Letters ⟨r, child⟩
      refine Or.inr ⟨(letters).encode ⟨r, child⟩, (letters).encode_mem ⟨r, child⟩,
        (sGroup).encode g, carrier ▸ (sGroup).encode_mem g,
        (completion.externalFamily_vertex_letter group oldAction compression r (some child) _).2 ⟨child, rfl, rfl⟩, ?_, ?_⟩
      · rw [generators]
        exact ((letters).pair_mem_graph (sGroup) _ ⟨r, child⟩ g).2 rfl
      · rw [multiplication]
        exact (((sGroup).product (sGroup)).pair_mem_graph (sGroup) (fun p => p.1 * p.2) (w, g) (w * g)).2 rfl

theorem externalPlacements_entry_iff :
    letI := group.toGroup
    ∀ (w : External (SetMembers G) (family).Letters)
      (v : Sigma fun r : ExternalRequestIndex I P0 Rects => Option ((family).Child r) × SetMembers U)
      (z : External (SetMembers G) (family).Letters × SetMembers U),
    ZFSet.pair (ZFSet.pair ((sGroup).encode w) ((vertices).encode v))
      (((sGroup).product (SetMembers.presentation U)).encode z) ∈ completion.externalPlacements P0 r0 μ0 A0 ↔
        z = ((family).flatWord w v.1 v.2.1, v.2.2) := by
  let := group.toGroup
  intro w v z
  rcases v with ⟨r, i, x⟩
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  constructor
  · intro entry
    obtain ⟨_, _, _, q, _, j, _, y, _, k, _, left, right, word⟩ :=
      (triple_mem_externalFlatPlacements _ _ _ _ _ _ _ _ _ _).1 entry
    obtain ⟨leftPair, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 leftPair
    obtain ⟨rfl, point⟩ := ZFSet.pair_inj.1 right
    exact Prod.ext
      ((completion.externalFlatVertexWordCode_iff group oldAction compression
        pairing unions powers separation infinite hG hLetters r i w z.1).1 word)
      (SetMembers.raw_injective U point)
  · intro equal
    subst z
    apply (triple_mem_externalFlatPlacements _ _ _ _ _ _ _ _ _ _).2
    refine ⟨carrier ▸ (sGroup).encode_mem w, (vertices).encode_mem ⟨r, i, x⟩,
      ZFSet.pair_mem_prod.2 ⟨carrier ▸ (sGroup).encode_mem _, SetMembers.raw_mem x⟩,
      externalRequestIndexCode r, (externalRequestPresentation I P0 Rects).encode_mem r,
      vcode r i, completion.externalFamilyVertexCode_mem_tags group oldAction compression r i,
      SetMembers.raw x, SetMembers.raw_mem x,
      (sGroup).encode ((family).flatWord w r i), carrier ▸ (sGroup).encode_mem _, rfl, rfl, ?_⟩
    exact (completion.externalFlatVertexWordCode_iff group oldAction compression
      pairing unions powers separation infinite hG hLetters r i w _).2 rfl

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets)
variable (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction compression
  pairing unions powers separation infinite hG hLetters

include pairing unions powers separation infinite hG hLetters in
theorem externalFlatSteps_iff :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    ∀ x y : (family).FlatLabel (J := SetMembers G),
    ZFSet.pair (((sGroup).product (SetMembers.presentation U)).encode x)
      (((sGroup).product (SetMembers.presentation U)).encode y) ∈ completion.externalFlatSteps P0 r0 μ0 A0 ↔
      (family).FlatStep a x y := by
  let := group.toGroup
  dsimp only
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let t := SetMembers.presentation U
  let g := SetMembers.presentation G
  let v := completion.externalFamilyTileVertexPresentation group oldAction compression
  have carrier := completion.externalFamilyGroupPresentation_carrier group oldAction compression
    pairing unions powers separation infinite hG hLetters
  have oldEntries : ∀ j w, ZFSet.pair (g.encode j) (s.encode w) ∈ M.externalOldInclusion G
      (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one ↔
      old (SetMembers G) (family).Letters j = w := by
    intro j w
    rw [completion.externalFamilyGroupPresentation_old group oldAction compression
      pairing unions powers separation infinite hG hLetters]
    exact g.pair_mem_graph s _ j w
  have mulEntries : ∀ w k l, ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode l) ∈
      M.externalGroupMultiplication G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one ↔
      w * k = l := by
    intro w k l
    rw [completion.externalFamilyGroupPresentation_multiplication group oldAction compression
      pairing unions powers separation infinite hG hLetters]
    exact (s.product s).pair_mem_graph s _ (w, k) l
  have actEntries : ∀ j x y, ZFSet.pair (ZFSet.pair (g.encode j) (t.encode x)) (t.encode y) ∈
      completion.algebra.union.fields 12 ↔ (a.iso j).toFun x = y :=
    fun j x y => (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet j x y).symm
  intro x y
  have result := pair_mem_externalFlatStepGraph_iff (family) a s t g v oldEntries mulEntries actEntries
    (completion.externalPlacements_entry_iff group oldAction compression pairing unions powers separation infinite hG hLetters)
    (completion.externalOverlaps_same_request group oldAction compression)
    (completion.externalOverlaps_entry_iff group oldAction compression) x y
  change ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
    externalFlatStepGraph s.carrier U G (completion.externalVertices P0 r0 μ0 A0) _ _ _ _ _ ↔ _ at result
  rw [carrier] at result
  exact result

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI

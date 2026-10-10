import OAI.SetTheory.PartitionPrinciple.Definability.ExternalColumnCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightSelection

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def transportedTileCoordinates (V E I B D action heights : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ w ∈ E, ∃ i ∈ I, ∃ x ∈ B, ∃ q ∈ D,
    ∃ y ∈ B, ∃ h ∈ ZFSet.sUnion (ZFSet.sUnion heights), z = ZFSet.pair (ZFSet.pair v x) q ∧
      v = ZFSet.pair (natSetCode 1) (ZFSet.pair w i) ∧ ZFSet.pair i h ∈ heights ∧
      ZFSet.pair (ZFSet.pair w y) x ∈ action ∧ ZFSet.pair y q ∈ h)
    (ZFSet.prod (ZFSet.prod V B) D)

theorem pair_mem_transportedTileCoordinates (V E I B D action heights v x q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v x) q ∈ transportedTileCoordinates V E I B D action heights ↔
      v ∈ V ∧ x ∈ B ∧ q ∈ D ∧ ∃ w ∈ E, ∃ i ∈ I, ∃ y ∈ B, ∃ h ∈ ZFSet.sUnion (ZFSet.sUnion heights),
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w i) ∧ ZFSet.pair i h ∈ heights ∧
        ZFSet.pair (ZFSet.pair w y) x ∈ action ∧ ZFSet.pair y q ∈ h := by
  rw [transportedTileCoordinates, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, w, hw, i, hi, x', hx, q', hq, y, hy, h, hh, equal, body⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hx, hq, w, hw, i, hi, y, hy, h, hh, body⟩
  · rintro ⟨hv, hx, hq, w, hw, i, hi, y, hy, h, hh, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hx⟩, hq⟩,
      v, hv, w, hw, i, hi, x, hx, q, hq, y, hy, h, hh, rfl, body⟩

theorem transportedTileCoordinates_partial {V E I B D action heights : ZFSet.{u}}
    (family : FunctionGraphOn I heights)
    (localUnique : ∀ i h y a b, ZFSet.pair i h ∈ heights →
      ZFSet.pair y a ∈ h → ZFSet.pair y b ∈ h → a = b)
    (actionInjective : ∀ w ∈ E, ∀ y ∈ B, ∀ z ∈ B, ∀ x,
      ZFSet.pair (ZFSet.pair w y) x ∈ action →
      ZFSet.pair (ZFSet.pair w z) x ∈ action → y = z) :
    PartialFunctionCode (ZFSet.prod V B) D (transportedTileCoordinates V E I B D action heights) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro p a b first second
  have hp := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 first).1).1
  obtain ⟨v, _, x, _, rfl⟩ := ZFSet.mem_prod.1 hp
  obtain ⟨_, _, _, w, hw, i, hi, y, hy, h, _, shape, field, acting, value⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, _, w', _, i', _, y', hy', h', _, shape', field', acting', value'⟩ :=
    (pair_mem_transportedTileCoordinates _ _ _ _ _ _ _ _ _ _).1 second
  have wi := ZFSet.pair_inj.1 ((ZFSet.pair_inj.1 (shape.symm.trans shape')).2)
  obtain ⟨rfl, rfl⟩ := wi
  have sameH : h = h' := (family.value_eq_of_entry ⟨i, hi⟩ field).symm.trans
    (family.value_eq_of_entry ⟨i, hi⟩ field')
  subst h'
  have sameY := actionInjective w hw y hy y' hy' x acting acting'
  subst y'
  exact localUnique i h y a b field value value'

noncomputable def externalOwnerHeightGraph (P B V C D old owner depths columns coordinates : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ ZFSet.sep (fun z => ∃ x ∈ B, ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
    z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧
      ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
      ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) (ZFSet.prod B (ZFSet.prod C D))

theorem pair_mem_externalOwnerHeightGraph (P B V C D old owner depths columns coordinates x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      ZFSet.pair x y ∈ old ∨ (x ∈ B ∧ x ∉ P ∧ ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
        y = ZFSet.pair a q ∧ ZFSet.pair x v ∈ owner ∧ ZFSet.pair v n ∈ depths ∧
          ZFSet.pair n a ∈ columns ∧ ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) := by
  rw [externalOwnerHeightGraph, ZFSet.mem_union]
  apply or_congr Iff.rfl
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, v, hv, n, hn, a, ha, q, hq, equal, fresh, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩
  · rintro ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.pair_mem_prod.2 ⟨ha, hq⟩⟩,
      x, hx, v, hv, n, hn, a, ha, q, hq, rfl, fresh, body⟩

theorem externalOwnerHeightGraph_old {P B V C D old owner depths columns coordinates x y : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x y ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      ZFSet.pair x y ∈ old := by
  rw [pair_mem_externalOwnerHeightGraph]
  exact ⟨fun h => h.elim id (fun h => False.elim (h.2.1 hx)), Or.inl⟩

theorem externalOwnerHeightGraph_function {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (subset : P ⊆ B) (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (ownerFunction : ZFSet.IsFunc B V owner) (depthFunction : ZFSet.IsFunc V ZFSet.omega depths)
    (columnFunction : ZFSet.IsFunc ZFSet.omega C columns)
    (coordinatePartial : PartialFunctionCode (ZFSet.prod V B) D coordinates)
    (coordinateTotal : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ q ∈ D, ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) :
    ZFSet.IsFunc B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) := by
  have oldUnique := functionCode_partial oldFunction
  have ownerUnique := functionCode_partial ownerFunction
  have depthUnique := functionCode_partial depthFunction
  have columnUnique := functionCode_partial columnFunction
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases (ZFSet.mem_union.1 hz) with oldEntry | freshEntry
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨subset hx, hy⟩
    · exact (ZFSet.mem_sep.1 freshEntry).1
  · intro x hx
    by_cases oldX : x ∈ P
    · obtain ⟨y, entry, unique⟩ := oldFunction.2 x oldX
      exact ⟨y, (externalOwnerHeightGraph_old oldX).2 entry,
        fun z hz => unique z ((externalOwnerHeightGraph_old oldX).1 hz)⟩
    · obtain ⟨v, owned, _⟩ := ownerFunction.2 x hx
      have hv := (ZFSet.pair_mem_prod.1 (ownerFunction.1 owned)).2
      obtain ⟨n, atDepth, _⟩ := depthFunction.2 v hv
      have hn := (ZFSet.pair_mem_prod.1 (depthFunction.1 atDepth)).2
      obtain ⟨a, atColumn, _⟩ := columnFunction.2 n hn
      have ha := (ZFSet.pair_mem_prod.1 (columnFunction.1 atColumn)).2
      obtain ⟨q, hq, coord⟩ := coordinateTotal x hx oldX v owned
      refine ⟨ZFSet.pair a q, (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).2
        (Or.inr ⟨hx, oldX, v, hv, n, hn, a, ha, q, hq, rfl, owned, atDepth, atColumn, coord⟩), ?_⟩
      intro y entry
      rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with oldEntry | fresh
      · exact False.elim (oldX (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1)
      · obtain ⟨_, _, v', _, n', _, a', _, q', _, rfl, owned', depth', column', coord'⟩ := fresh
        have sameV := ownerUnique.unique x v' v owned' owned
        subst v'
        have sameN := depthUnique.unique v n' n depth' atDepth
        subst n'
        have sameA := columnUnique.unique n a' a column' atColumn
        have sameQ := coordinatePartial.unique (ZFSet.pair v x) q' q coord' coord
        exact congrArg₂ ZFSet.pair sameA sameQ

end

section
open SetFormula
universe u
namespace BoundedFormula

def transportedTileCoordinateFormula {n} (z V E I B D action heights bound one : Fin n) : BoundedFormula n :=
  exMem V (exMem E.succ (exMem I.succ.succ (exMem B.succ.succ.succ
    (exMem D.succ.succ.succ.succ (exMem B.succ.succ.succ.succ.succ
      (exMem bound.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ.succ 6 3 2)
          (.conj (orderedRightTripleFormula 6 one.succ.succ.succ.succ.succ.succ.succ 5 4)
            (.conj (pairMembershipFormula 4 0 heights.succ.succ.succ.succ.succ.succ.succ)
              (.conj (tripleMembershipFormula 5 1 3 action.succ.succ.succ.succ.succ.succ.succ)
                (pairMembershipFormula 1 2 0)))))))))))

theorem truth_transportedTileCoordinateFormula {n} (z V E I B D action heights bound one : Fin n)
    (env : Fin n → ZFSet.{u}) (boundEq : env bound = ZFSet.sUnion (ZFSet.sUnion (env heights)))
    (oneEq : env one = natSetCode 1) :
    Truth (transportedTileCoordinateFormula z V E I B D action heights bound one) env ↔
      env z ∈ transportedTileCoordinates (env V) (env E) (env I) (env B) (env D) (env action) (env heights) := by
  simp only [transportedTileCoordinateFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [boundEq, oneEq, transportedTileCoordinates, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, _, _, _, _, x, hx, q, hq, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hx⟩, hq⟩

def ownerHeightFreshFormula {n} (z P B V C D owner depths columns coordinates omega : Fin n) : BoundedFormula n :=
  exMem B (exMem V.succ (exMem omega.succ.succ (exMem C.succ.succ.succ
    (exMem D.succ.succ.succ.succ
      (.conj (orderedRightTripleFormula z.succ.succ.succ.succ.succ 4 1 0)
        (.conj (.neg (.mem 4 P.succ.succ.succ.succ.succ))
          (.conj (pairMembershipFormula 4 3 owner.succ.succ.succ.succ.succ)
            (.conj (pairMembershipFormula 3 2 depths.succ.succ.succ.succ.succ)
              (.conj (pairMembershipFormula 2 1 columns.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 3 4 0 coordinates.succ.succ.succ.succ.succ))))))))))

theorem truth_ownerHeightFreshFormula {n} (z P B V C D owner depths columns coordinates omega : Fin n)
    (env : Fin n → ZFSet.{u}) (omegaEq : env omega = ZFSet.omega) :
    Truth (ownerHeightFreshFormula z P B V C D owner depths columns coordinates omega) env ↔
      ∃ x ∈ env B, ∃ v ∈ env V, ∃ n ∈ ZFSet.omega, ∃ a ∈ env C, ∃ q ∈ env D,
        env z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ env P ∧ ZFSet.pair x v ∈ env owner ∧
          ZFSet.pair v n ∈ env depths ∧ ZFSet.pair n a ∈ env columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ env coordinates := by
  simp only [ownerHeightFreshFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [omegaEq]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem transportedTileCoordinates_mem {V E I B D action heights : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hD : D ∈ M.sets) (hAction : action ∈ M.sets) (hHeights : heights ∈ M.sets) :
    transportedTileCoordinates V E I B D action heights ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hHeights)
  have hZero := M.empty_mem ⟨B, hB⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend V (extend E (extend I (extend B (extend D (extend action
    (extend heights (extend (ZFSet.sUnion (ZFSet.sUnion heights)) (extend (natSetCode 1) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.transportedTileCoordinateFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hB (Fin.cases hD
      (Fin.cases hAction (Fin.cases hHeights (Fin.cases hBound (Fin.cases hOne (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hB) hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.transportedTileCoordinateFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod V B) D) = transportedTileCoordinates V E I B D action heights := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_transportedTileCoordinateFormula _ _ _ _ _ _ _ _ _ _ _ rfl rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

theorem externalOwnerHeightGraph_mem {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hV : V ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hOwner : owner ∈ M.sets) (hDepths : depths ∈ M.sets)
    (hColumns : columns ∈ M.sets) (hCoordinates : coordinates ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets) :
    externalOwnerHeightGraph P B V C D old owner depths columns coordinates ∈ M.sets := by
  let params := extend P (extend B (extend V (extend C (extend D (extend owner (extend depths
    (extend columns (extend coordinates (extend ZFSet.omega Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ownerHeightFreshFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hV (Fin.cases hC (Fin.cases hD (Fin.cases hOwner
      (Fin.cases hDepths (Fin.cases hColumns (Fin.cases hCoordinates (Fin.cases hOmega (fun i => Fin.elim0 i)))))))))))
    (M.prod_mem pairing unions powers separation hB (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ownerHeightFreshFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod B (ZFSet.prod C D)) =
      ZFSet.sep (fun z => ∃ x ∈ B, ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
        z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧
          ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) (ZFSet.prod B (ZFSet.prod C D)) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_ownerHeightFreshFormula _ _ _ _ _ _ _ _ _ _ _ _ rfl)
  exact M.binary_union_mem pairing unions hOld (equal ▸ selected)

end TransitiveGround
end

section
universe u

theorem externalOwnerHeightGraph_range_subset {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old) :
    relationImage B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) ⊆
      relationImage P (ZFSet.prod C D) old ∪ ZFSet.prod (relationImage ZFSet.omega C columns) D := by
  intro y hy
  obtain ⟨hy, x, _, entry⟩ := (mem_relationImage _ _ _ _).1 hy
  rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with retained | fresh
  · exact ZFSet.mem_union.2 (Or.inl ((mem_relationImage _ _ _ _).2
      ⟨hy, x, (ZFSet.pair_mem_prod.1 (oldFunction.1 retained)).1, retained⟩))
  · obtain ⟨_, _, _, _, n, hn, a, ha, q, hq, rfl, _, _, column, _⟩ := fresh
    exact ZFSet.mem_union.2 (Or.inr (ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage _ _ _ _).2 ⟨ha, n, hn, column⟩, hq⟩))

theorem externalOwnerHeightGraph_below_cap {P B V C D old owner depths columns coordinates base cap rD q0 : ZFSet.{u}}
    (ordinal : ordinalSetProperty C) (hq0 : q0 ∈ D)
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (code : ExternalColumnCode C (heightColumns P C D old) base columns cap)
    {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates) :
    ZFSet.pair y (ZFSet.pair cap q0) ∈ lexHeightOrder C D rD := by
  rcases (pair_mem_externalOwnerHeightGraph _ _ _ _ _ _ _ _ _ _ _ _).1 entry with retained | fresh
  · obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (oldFunction.1 retained)).2
    have below := code.old_below (mem_heightColumns_of_entry oldFunction retained) 0
    exact (pair_mem_lexHeightOrder _ _ _ _ _ _ _).2
      ⟨ha, hq, code.cap_mem, hq0, Or.inl (ordinal.2 cap code.cap_mem
        (compressionStamp base 0) (code.cap_bound 0) a below)⟩
  · obtain ⟨_, _, _, _, n, hn, a, ha, q, hq, rfl, _, _, column, _⟩ := fresh
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have below : a ∈ cap := (code.entries n a).1 column ▸ code.cap_bound n
    exact (pair_mem_lexHeightOrder _ _ _ _ _ _ _).2 ⟨ha, hq, code.cap_mem, hq0, Or.inl below⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem externalOwnerHeightGraph_range_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P B V C D old owner depths columns coordinates : ZFSet.{u}}
    (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hColumns : columns ∈ M.sets)
    (hHeight : externalOwnerHeightGraph P B V C D old owner depths columns coordinates ∈ M.sets)
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (columnSmall : M.groundEmbeddable (relationImage ZFSet.omega C columns) ZFSet.omega)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega) :
    relationImage B (ZFSet.prod C D) (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) ∈ M.sets ∧
      M.groundEmbeddable (relationImage B (ZFSet.prod C D)
        (externalOwnerHeightGraph P B V C D old owner depths columns coordinates)) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  have rangeGround := M.relationImage_mem separation hB (M.prod_mem pairing unions powers separation hC hD) hHeight
  have oldGround := M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld
  have columnsGround := M.relationImage_mem separation omega hC hColumns
  have productGround := M.prod_mem pairing unions powers separation columnsGround hD
  have productSmall := M.groundEmbeddable_product pairing unions powers separation infinite columnsGround hD columnSmall coordinateSmall
  have totalSmall := M.groundCountable_binary_union pairing unions powers separation infinite choice
    oldGround productGround oldSmall productSmall
  exact ⟨rangeGround, M.groundEmbeddable_restrict separation rangeGround omega
    (externalOwnerHeightGraph_range_subset oldFunction) totalSmall⟩

end TransitiveGround

end

section
open SetFormula
universe u

noncomputable def externalTileSlotSupports (V E I U B action vertexImages : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ v ∈ V, ∃ j ∈ natSetCode 3, ∃ x ∈ B, ∃ w ∈ E,
    ∃ r ∈ I, ∃ u ∈ U, ∃ z ∈ B,
      y = ZFSet.pair (ZFSet.pair v j) x ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
        ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) z ∈ vertexImages ∧
        ZFSet.pair (ZFSet.pair w z) x ∈ action)
    (ZFSet.prod (ZFSet.prod V (natSetCode 3)) B)

theorem pair_mem_externalTileSlotSupports (V E I U B action vertexImages v j x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v j) x ∈ externalTileSlotSupports V E I U B action vertexImages ↔
      v ∈ V ∧ j ∈ natSetCode 3 ∧ x ∈ B ∧ ∃ w ∈ E, ∃ r ∈ I, ∃ u ∈ U, ∃ z ∈ B,
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) z ∈ vertexImages ∧
          ZFSet.pair (ZFSet.pair w z) x ∈ action := by
  rw [externalTileSlotSupports, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, j', hj, x', hx, w, hw, r, hr, u, hu, z, hz, equal, body⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hj, hx, w, hw, r, hr, u, hu, z, hz, body⟩
  · rintro ⟨hv, hj, hx, w, hw, r, hr, u, hu, z, hz, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hj⟩, hx⟩,
      v, hv, j, hj, x, hx, w, hw, r, hr, u, hu, z, hz, rfl, body⟩

namespace BoundedFormula

def slotImageMembershipFormula {n} (r j u z images : Fin n) : BoundedFormula n :=
  exMem images (exMem 0 (exMem 0
    (.conj (orderedTripleFormula 0 r.succ.succ.succ j.succ.succ.succ u.succ.succ.succ)
      (orderedPairFormula 2 0 z.succ.succ.succ))))

theorem truth_slotImageMembershipFormula {n} (r j u z images : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (slotImageMembershipFormula r j u z images) env ↔
      ZFSet.pair (ZFSet.pair (ZFSet.pair (env r) (env j)) (env u)) (env z) ∈ env images := by
  simp only [slotImageMembershipFormula, truth_exMem, Truth, truth_orderedTripleFormula, truth_orderedPairFormula]
  change (∃ a ∈ env images, ∃ b ∈ a, ∃ c ∈ b,
    c = ZFSet.pair (ZFSet.pair (env r) (env j)) (env u) ∧ a = ZFSet.pair c (env z)) ↔ _
  constructor
  · rintro ⟨a, ha, _, _, c, _, rfl, rfl⟩
    exact ha
  · intro entry
    let c := ZFSet.pair (ZFSet.pair (env r) (env j)) (env u)
    exact ⟨ZFSet.pair c (env z), entry, {c}, ZFSet.mem_pair.2 (Or.inl rfl),
      c, ZFSet.mem_singleton.2 rfl, rfl, rfl⟩

def externalTileSlotSupportFormula {n} (y V E I U B action images one three : Fin n) : BoundedFormula n :=
  exMem V (exMem three.succ (exMem B.succ.succ (exMem E.succ.succ.succ
    (exMem I.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem B.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula y.succ.succ.succ.succ.succ.succ.succ 6 5 4)
          (.conj (orderedRightTripleFormula 6 one.succ.succ.succ.succ.succ.succ.succ 3 2)
            (.conj (slotImageMembershipFormula 2 5 1 0 images.succ.succ.succ.succ.succ.succ.succ)
              (tripleMembershipFormula 3 0 4 action.succ.succ.succ.succ.succ.succ.succ))))))))))

theorem truth_externalTileSlotSupportFormula {n} (y V E I U B action images one three : Fin n)
    (env : Fin n → ZFSet.{u}) (oneEq : env one = natSetCode 1) (threeEq : env three = natSetCode 3) :
    Truth (externalTileSlotSupportFormula y V E I U B action images one three) env ↔
      env y ∈ externalTileSlotSupports (env V) (env E) (env I) (env U) (env B) (env action) (env images) := by
  simp only [externalTileSlotSupportFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_slotImageMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [oneEq, threeEq, externalTileSlotSupports, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, j, hj, x, hx, _, _, _, _, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hj⟩, hx⟩

end BoundedFormula

end

section
universe u

theorem externalOwnerHeightGraph_fresh {P B V C D old owner depths columns coordinates x a q : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old) (fresh : x ∉ P) :
    ZFSet.pair x (ZFSet.pair a q) ∈ externalOwnerHeightGraph P B V C D old owner depths columns coordinates ↔
      x ∈ B ∧ a ∈ C ∧ q ∈ D ∧ ∃ v ∈ V, ∃ n ∈ ZFSet.omega,
        ZFSet.pair x v ∈ owner ∧ ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
          ZFSet.pair (ZFSet.pair v x) q ∈ coordinates := by
  rw [pair_mem_externalOwnerHeightGraph]
  constructor
  · intro entry
    rcases entry with retained | new
    · exact False.elim (fresh (ZFSet.pair_mem_prod.1 (oldFunction.1 retained)).1)
    · obtain ⟨hx, _, v, hv, n, hn, a', ha, q', hq, equal, body⟩ := new
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact ⟨hx, ha, hq, v, hv, n, hn, body⟩
  · rintro ⟨hx, ha, hq, v, hv, n, hn, body⟩
    exact Or.inr ⟨hx, fresh, v, hv, n, hn, a, ha, q, hq, rfl, body⟩

theorem ExternalColumnCode.entries_increasing {C K base columns cap n m a b : ZFSet.{u}}
    (code : ExternalColumnCode C K base columns cap)
    (hn : n ∈ ZFSet.omega) (hm : m ∈ ZFSet.omega) (before : n ∈ m)
    (first : ZFSet.pair n a ∈ columns) (second : ZFSet.pair m b ∈ columns) : a ∈ b := by
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rw [(code.entries n a).1 first, (code.entries m b).1 second]
  exact (compressionStamp_mem_iff base n m).2 ((natSetCode_mem_iff n m).1 before)

theorem externalOwnerHeightGraph_strictLex {P B V C D r old owner depths columns coordinates base cap rD : ZFSet.{u}}
    (subset : P ⊆ B) (seed : StrictLexHeightCode P C D r old rD)
    (ownerFunction : ZFSet.IsFunc B V owner) (depthFunction : ZFSet.IsFunc V ZFSet.omega depths)
    (columnCode : ExternalColumnCode C (heightColumns P C D old) base columns cap)
    (coordinatePartial : PartialFunctionCode (ZFSet.prod V B) D coordinates)
    (coordinateTotal : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ q ∈ D, ZFSet.pair (ZFSet.pair v x) q ∈ coordinates)
    (noFreshBelowOld : ∀ x ∈ B, x ∉ P → ∀ y ∈ P, ZFSet.pair x y ∉ r)
    (depthMonotone : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ v w n m,
      ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → ZFSet.pair v n ∈ depths →
      ZFSet.pair w m ∈ depths → ZFSet.pair x y ∈ r → n = m ∨ n ∈ m)
    (sameDepthOwner : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ v w n,
      ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → ZFSet.pair v n ∈ depths →
      ZFSet.pair w n ∈ depths → ZFSet.pair x y ∈ r → v = w)
    (coordinateStrict : ∀ v x y a b, ZFSet.pair x y ∈ r → x ≠ y →
      ZFSet.pair (ZFSet.pair v x) a ∈ coordinates →
      ZFSet.pair (ZFSet.pair v y) b ∈ coordinates → ZFSet.pair a b ∈ rD) :
    StrictLexHeightCode B C D r
      (externalOwnerHeightGraph P B V C D old owner depths columns coordinates) rD := by
  refine ⟨externalOwnerHeightGraph_function subset seed.function ownerFunction depthFunction
    columnCode.function coordinatePartial coordinateTotal, ?_⟩
  intro x hx y hy a q b s lower different first second
  by_cases oldX : x ∈ P
  · have oldFirst := (externalOwnerHeightGraph_old oldX).1 first
    by_cases oldY : y ∈ P
    · exact seed.strict x oldX y oldY a q b s lower different oldFirst
        ((externalOwnerHeightGraph_old oldY).1 second)
    · obtain ⟨_, _, _, _, _, n, hn, _, _, column, _⟩ :=
        (externalOwnerHeightGraph_fresh seed.function oldY).1 second
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      refine Or.inl ?_
      rw [(columnCode.entries n b).1 column]
      exact columnCode.old_below (mem_heightColumns_of_entry seed.function oldFirst) n
  · have oldY : y ∉ P := fun hyP => noFreshBelowOld x hx oldX y hyP lower
    obtain ⟨_, _, _, v, _, n, hn, ownedX, depthX, colX, coordX⟩ :=
      (externalOwnerHeightGraph_fresh seed.function oldX).1 first
    obtain ⟨_, _, _, w, _, m, hm, ownedY, depthY, colY, coordY⟩ :=
      (externalOwnerHeightGraph_fresh seed.function oldY).1 second
    rcases depthMonotone x hx oldX y hy oldY v w n m ownedX ownedY depthX depthY lower with same | before
    · subst m
      have sameOwner := sameDepthOwner x hx oldX y hy oldY v w n ownedX ownedY depthX depthY lower
      subst w
      exact Or.inr ⟨(functionCode_partial columnCode.function).unique n a b colX colY,
        coordinateStrict v x y q s lower different coordX coordY⟩
    · exact Or.inl (columnCode.entries_increasing hn hm before colX colY)

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem externalTileSlotSupports_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V E I U B action vertexImages : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hAction : action ∈ M.sets) (hImages : vertexImages ∈ M.sets) :
    externalTileSlotSupports V E I U B action vertexImages ∈ M.sets := by
  have hOne := M.natSetCode_mem separation infinite 1
  have hThree := M.natSetCode_mem separation infinite 3
  let params := extend V (extend E (extend I (extend U (extend B (extend action
    (extend vertexImages (extend (natSetCode 1) (extend (natSetCode 3) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalTileSlotSupportFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hU (Fin.cases hB
      (Fin.cases hAction (Fin.cases hImages (Fin.cases hOne (Fin.cases hThree (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hThree) hB)
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.externalTileSlotSupportFormula 0 1 2 3 4 5 6 7 8 9) (extend y params))
      (ZFSet.prod (ZFSet.prod V (natSetCode 3)) B) =
      externalTileSlotSupports V E I U B action vertexImages := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalTileSlotSupportFormula _ _ _ _ _ _ _ _ _ _ _ rfl rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI

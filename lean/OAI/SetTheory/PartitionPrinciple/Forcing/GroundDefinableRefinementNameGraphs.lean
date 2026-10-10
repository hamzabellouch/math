import OAI.SetTheory.PartitionPrinciple.Geometry.GroundDefinableIndexBounds

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementOutput (kind : Fin 3) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s) : Name s :=
  Fin.cases (refinementQuotient T valid U Rf)
    (Fin.cases (refinementQuotient T valid U Rc) (fun _ => refinementNaturalMap T valid U Rf Rc)) kind

end Name
namespace SetFormula

def refinementOutputCodeFormula (kind : Fin 3) : SetFormula 8 :=
  Fin.cases (reindex ![0, 1, 2, 3, 5, 6, 7] refinementQuotientCodeFormula)
    (Fin.cases (reindex ![0, 1, 2, 4, 5, 6, 7] refinementQuotientCodeFormula)
      (fun _ => refinementMapCodeFormula)) kind

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def refinementNameBound (T P top : ZFSet.{u}) : ZFSet.{u} :=
  M.groundRelations (M.groundRelations T P ∪
    orderedPairNameFamily top (M.groundRelations T P) (M.groundRelations T P)) P

theorem refinementNameBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T P top : ZFSet.{u}} (hT : T ∈ M.sets) (hP : P ∈ M.sets) (htop : top ∈ M.sets) :
    M.refinementNameBound T P top ∈ M.sets := by
  have hc := M.groundRelations_mem pairing unions powers separation hT hP
  exact M.groundRelations_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hc (M.orderedPairNameFamily_mem pairing unions powers separation htop hc hc)) hP

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem refinementOutput_mem_bound (kind : Fin 3) {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementOutput kind T valid U Rf Rc).val ∈ M.refinementNameBound T s.carrier (s.encode ⊤) := by
  let B := M.groundRelations T s.carrier
  let C := B ∪ orderedPairNameFamily (s.encode ⊤) B B
  have classBound (R : Name s) (hR : R.val ∈ M.sets) (w : Name s) (hw : w.val ∈ T) :
      (Name.refinementClass T valid R w).val ∈ B :=
    (M.mem_groundRelations T s.carrier _).2
      ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid R w hR
        (M.transitive hT hw), Name.refinementClass_subset T valid R w⟩
  have quotient (R : Name s) (hR : R.val ∈ M.sets) :
      (Name.refinementQuotient T valid U R).val ∈ M.groundRelations C s.carrier := by
    apply (M.mem_groundRelations C s.carrier _).2
    exact ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order hT valid U R hU hR,
      Name.activeImage_subset T valid U _ C (fun w hw => ZFSet.mem_union.2 (Or.inl (classBound R hR w hw)))⟩
  have natural : (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.groundRelations C s.carrier := by
    apply (M.mem_groundRelations C s.carrier _).2
    refine ⟨M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order hT valid U Rf Rc hU hRf hRc,
      Name.activeImage_subset T valid U _ C ?_⟩
    intro w hw
    exact ZFSet.mem_union.2 (Or.inr ((mem_orderedPairNameFamily _ B B _).2
      ⟨_, classBound Rf hRf w hw, _, classBound Rc hRc w hw, Name.orderedPair_code ⊤ _ _⟩))
  exact Fin.cases (quotient Rf hRf) (Fin.cases (quotient Rc hRc)
    (Fin.cases natural (fun j => Fin.elim0 j))) kind

theorem realize_refinementOutputCodeFormula (kind : Fin 3) {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (refinementOutputCodeFormula kind)
      (extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) ↔
      z = (Name.refinementOutput kind T valid U Rf Rc).val := by
  let env := extend z (extend T (extend U.val (extend Rf.val (extend Rc.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))
  have firstArgs : (fun j : Fin 7 => env (![0, 1, 2, 3, 5, 6, 7] j)) =
      extend z (extend T (extend U.val (extend Rf.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  have secondArgs : (fun j : Fin 7 => env (![0, 1, 2, 4, 5, 6, 7] j)) =
      extend z (extend T (extend U.val (extend Rc.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) kind
  · change Realize M.sets (reindex _ refinementQuotientCodeFormula) env ↔ _
    rw [realize_reindex, firstArgs]
    exact M.realize_refinementQuotientCodeFormula s pairing unions powers separation collection carrier order hT valid U Rf hU hRf z hz
  · change Realize M.sets (reindex _ refinementQuotientCodeFormula) env ↔ _
    rw [realize_reindex, secondArgs]
    exact M.realize_refinementQuotientCodeFormula s pairing unions powers separation collection carrier order hT valid U Rc hU hRc z hz
  · exact M.realize_refinementMapCodeFormula s pairing unions powers separation collection carrier order hT valid U Rf Rc hU hRf hRc z hz

end TransitiveGround



namespace SetFormula

def refinementIndexNameGraphFormula (kind : Fin 3) : SetFormula 9 :=
  let w := prefixIndex 9 5
  let old := suffixIndex 9 5
  exBlock 5 (.conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedPairFormula (old 0) (w 0) (w 1)).toFormula
      (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 2) (old 2)).toFormula
        (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 3) (old 3)).toFormula
          (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 4) (old 4)).toFormula
            (reindex ![w 1, old 5, w 2, w 3, w 4, old 6, old 7, old 8]
              (refinementOutputCodeFormula kind)))))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def refinementIndexNameGraph (kind : Fin 3)
    (I UF FF CF T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets (refinementIndexNameGraphFormula kind)
    (extend z ![I, UF, FF, CF, T, P, order, top]))
      (ZFSet.prod I (M.refinementNameBound T P top))

theorem refinementIndexNameGraph_mem (kind : Fin 3)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I UF FF CF T P order top : ZFSet.{u}}
    (hI : I ∈ M.sets) (hUF : UF ∈ M.sets) (hFF : FF ∈ M.sets) (hCF : CF ∈ M.sets)
    (hT : T ∈ M.sets) (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) :
    M.refinementIndexNameGraph kind I UF FF CF T P order top ∈ M.sets := by
  exact M.separation_mem separation (refinementIndexNameGraphFormula kind)
    ![I, UF, FF, CF, T, P, order, top]
    (Fin.cases hI (Fin.cases hUF (Fin.cases hFF (Fin.cases hCF (Fin.cases hT
      (Fin.cases hP (Fin.cases ho (Fin.cases ht (fun j => Fin.elim0 j)))))))))
    (M.prod_mem pairing unions powers separation hI
      (M.refinementNameBound_mem pairing unions powers separation hT hP ht))

theorem realize_refinementIndexNameGraphFormula (kind : Fin 3)
    (env : Fin 9 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexNameGraphFormula kind) env ↔
      ∃ w : Fin 5 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
        w 0 ∈ env 1 ∧ env 0 = ZFSet.pair (w 0) (w 1) ∧
        ZFSet.pair (w 0) (w 2) ∈ env 2 ∧ ZFSet.pair (w 0) (w 3) ∈ env 3 ∧
        ZFSet.pair (w 0) (w 4) ∈ env 4 ∧
        Realize M.sets (refinementOutputCodeFormula kind)
          (extend (w 1) (extend (env 5) (extend (w 2) (extend (w 3) (extend (w 4)
            (extend (env 6) (extend (env 7) (extend (env 8) Fin.elim0)))))))) := by
  rw [refinementIndexNameGraphFormula, realize_exBlock]
  apply exists_congr
  intro w
  apply and_congr_right
  intro ground
  have args : (fun j : Fin 8 => extendMany 5 w env
      (![prefixIndex 9 5 1, suffixIndex 9 5 5, prefixIndex 9 5 2,
        prefixIndex 9 5 3, prefixIndex 9 5 4, suffixIndex 9 5 6,
        suffixIndex 9 5 7, suffixIndex 9 5 8] j)) =
      extend (w 1) (extend (env 5) (extend (w 2) (extend (w 3) (extend (w 4)
        (extend (env 6) (extend (env 7) (extend (env 8) Fin.elim0))))))) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k)))))))) j
  simp only [Realize, BoundedFormula.realize_toFormula M _ _
    (extendMany_members 5 w env ground members), BoundedFormula.truth_orderedPairFormula,
    BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix,
    realize_reindex, args]

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem refinementIndexNameGraph_entry (kind : Fin 3)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {I UF FF CF T : ZFSet.{u}} (hI : I ∈ M.sets) (hUF : UF ∈ M.sets)
    (hFF : FF ∈ M.sets) (hCF : CF ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U.val ∈ M.sets) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets)
    {i : ZFSet.{u}} (hi : i ∈ I)
    (uEntry : ∀ z, ZFSet.pair i z ∈ UF ↔ z = U.val)
    (fEntry : ∀ z, ZFSet.pair i z ∈ FF ↔ z = Rf.val)
    (cEntry : ∀ z, ZFSet.pair i z ∈ CF ↔ z = Rc.val) (y : ZFSet.{u}) :
    ZFSet.pair i y ∈ M.refinementIndexNameGraph kind I UF FF CF T s.carrier s.conditionOrder (s.encode ⊤) ↔
      y = (Name.refinementOutput kind T valid U Rf Rc).val := by
  have ht := M.transitive carrier (s.encode_mem ⊤)
  have hB := M.refinementNameBound_mem pairing unions powers separation hT carrier ht
  have hidx := M.transitive hI hi
  let params : Fin 8 → ZFSet.{u} := ![I, UF, FF, CF, T, s.carrier, s.conditionOrder, s.encode ⊤]
  have hp : ∀ j, params j ∈ M.sets := Fin.cases hI (Fin.cases hUF (Fin.cases hFF
    (Fin.cases hCF (Fin.cases hT (Fin.cases carrier (Fin.cases order
      (Fin.cases ht (fun j => Fin.elim0 j))))))))
  rw [refinementIndexNameGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_, hyB⟩, recognized⟩
    have hy := M.transitive hB hyB
    have hpair := M.orderedPair_mem pairing hidx hy
    obtain ⟨w, ground, _, equal, hu, hf, hc, output⟩ :=
      (M.realize_refinementIndexNameGraphFormula kind (extend (ZFSet.pair i y) params)
        (Fin.cases hpair hp)).1 recognized
    have eq : ZFSet.pair i y = ZFSet.pair (w 0) (w 1) := equal
    obtain ⟨idx, val⟩ := ZFSet.pair_inj.1 eq
    have ue : w 2 = U.val := (uEntry _).1 (idx.symm ▸ hu)
    have fe : w 3 = Rf.val := (fEntry _).1 (idx.symm ▸ hf)
    have ce : w 4 = Rc.val := (cEntry _).1 (idx.symm ▸ hc)
    change Realize M.sets (refinementOutputCodeFormula kind)
      (extend (w 1) (extend T (extend (w 2) (extend (w 3) (extend (w 4)
        (extend s.carrier (extend s.conditionOrder (extend (s.encode ⊤) Fin.elim0)))))))) at output
    rw [← val, ue, fe, ce] at output
    exact (M.realize_refinementOutputCodeFormula s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc y hy).1 output
  · intro equal
    subst y
    have bound := M.refinementOutput_mem_bound s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc
    have hy := M.transitive hB bound
    refine ⟨⟨hi, bound⟩, ?_⟩
    apply (M.realize_refinementIndexNameGraphFormula kind (extend _ params)
      (Fin.cases (M.orderedPair_mem pairing hidx hy) hp)).2
    refine ⟨![i, (Name.refinementOutput kind T valid U Rf Rc).val, U.val, Rf.val, Rc.val],
      Fin.cases hidx (Fin.cases hy (Fin.cases hU (Fin.cases hRf (Fin.cases hRc
        (fun j => Fin.elim0 j))))), hi, rfl, (uEntry _).2 rfl, (fEntry _).2 rfl,
      (cEntry _).2 rfl, ?_⟩
    exact (M.realize_refinementOutputCodeFormula s pairing unions powers separation collection
      carrier order kind hT valid U Rf Rc hU hRf hRc _ hy).2 rfl

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

noncomputable def niceRefinementNameGraph (kind : Fin 3) (level T1 T2 : ZFSet.{u})
    (valid1 : ∀ z ∈ T1, IsName s z) : ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  let bounds := M.niceRefinementIndexBounds s b level T1 T2
  M.refinementIndexNameGraph kind I (refinementIndexFieldGraph I (bounds 3) 3)
    (refinementIndexFieldGraph I (bounds 4) 4) (refinementIndexFieldGraph I (bounds 5) 5)
    T1 s.carrier s.conditionOrder (s.encode ⊤)

variable {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
variable (system : NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2)

include system in
theorem niceRefinementIndex_field_entry (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (j : Fin 6) (z : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) z ∈
      refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
        (M.niceRefinementIndexBounds s b level T1 T2 j) j ↔
      z = (![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] : Fin 6 → ZFSet.{u}) j := by
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  let fields : Fin 6 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
  let B := M.niceRefinementIndexBounds s b level T1 T2 j
  change ZFSet.pair (nonemptyTupleCode 5 fields) z ∈ refinementIndexFieldGraph I B j ↔ z = fields j
  constructor
  · intro entry
    exact ((refinementIndexFieldGraph_entry I B fields j z).1 entry).2.2
  · intro equal
    obtain ⟨v, hv, _⟩ := (system.field_function j).2 _ member
    have value : v = fields j := ((refinementIndexFieldGraph_entry I B fields j v).1 hv).2.2
    exact equal.symm ▸ (value ▸ hv)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (hT1 : T1 ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include system pairing unions powers separation hT1 carrier order in
theorem niceRefinementNameGraph_mem (kind : Fin 3) :
    M.niceRefinementNameGraph a s b d kind level T1 T2 valid1 ∈ M.sets :=
  M.refinementIndexNameGraph_mem kind pairing unions powers separation system.index_ground
    (system.field_ground 3) (system.field_ground 4) (system.field_ground 5) hT1 carrier order
    (M.transitive carrier (s.encode_mem ⊤))

include system pairing unions powers separation collection hT1 carrier order in
theorem niceRefinementNameGraph_entry (kind : Fin 3)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
      M.niceRefinementNameGraph a s b d kind level T1 T2 valid1 ↔
      y = (Name.refinementOutput kind T1 valid1 U.val Rf.val Rc.val).val := by
  exact M.refinementIndexNameGraph_entry s kind pairing unions powers separation collection carrier order
    system.index_ground (system.field_ground 3) (system.field_ground 4) (system.field_ground 5)
    hT1 valid1 U.val Rf.val Rc.val U.property Rf.property Rc.property member
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 3)
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 4)
    (M.niceRefinementIndex_field_entry a s b d system C E U Rf Rc member 5) y

include system pairing unions powers separation collection hT1 carrier order in
theorem niceRefinementNameGraph_function (kind : Fin 3) :
    ZFSet.IsFunc (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.refinementNameBound T1 s.carrier (s.encode ⊤))
      (M.niceRefinementNameGraph a s b d kind level T1 T2 valid1) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    unfold niceRefinementNameGraph refinementIndexNameGraph at hz
    exact (ZFSet.mem_sep.1 hz).1
  intro i hi
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ := system.decoded i hi
  refine ⟨(Name.refinementOutput kind T1 valid1 U.val Rf.val Rc.val).val, ?_, ?_⟩
  · exact (M.niceRefinementNameGraph_entry a s b d system pairing unions powers separation collection
      hT1 carrier order kind C E U Rf Rc hi _).2 rfl
  · intro y hy
    exact (M.niceRefinementNameGraph_entry a s b d system pairing unions powers separation collection
      hT1 carrier order kind C E U Rf Rc hi y).1 hy

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_refinementNameBound :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => M.refinementNameBound (env 0) (env 1) (env 2)) := by
  let v := GroundSetTerm.var M (n := 3)
  let classes := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 0, v 1]
  let pairs := GroundSetTerm.app (M.definable_orderedPairNameFamily pairing unions powers separation)
    ![v 2, classes, classes]
  let children := GroundSetTerm.app (M.definable_binaryUnion pairing unions) ![classes, pairs]
  exact (GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![children, v 1]).definition

noncomputable def definable_refinementIndexNameGraph (kind : Fin 3) :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.refinementIndexNameGraph kind (env 0) (env 1) (env 2) (env 3)
        (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let names := GroundSetTerm.app (M.definable_refinementNameBound pairing unions powers separation)
    ![v 4, v 5, v 7]
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, names]
  let term := GroundSetTerm.app (M.definable_separation separation (refinementIndexNameGraphFormula kind))
    ![bound, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 8 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets (refinementIndexNameGraphFormula kind) (extend z params))
      (ZFSet.prod (env 0) (M.refinementNameBound (env 4) (env 5) (env 7))))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j

end PartitionPilot.Forcing.TransitiveGround

end OAI

import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.OrderedSections

namespace OAI

/-! ## SubsetImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- Local version of uniqueness for the default completion, using only the
forced function property on its stated domain. -/
theorem defaultRelation_unique_on (f A B D d : S.Name) (p : P)
    (hf : S.Forces ![f,A,B] p (SetLanguage.mapsTo 0 1 2)) {q : P} (hq : q ≤ p)
    (a y z : S.Name) (ha : S.atomic.MemF q a A)
    (hy : (S.defaultRelation f D d).holds q a y) (hz : (S.defaultRelation f D d).holds q a z) :
    S.atomic.EqF q y z := by
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,hs⟩ := (S.defaultRelation_iff f D d a y q).mp hy r hrq
  obtain ⟨t,hts,ht⟩ := (S.defaultRelation_iff f D d a z q).mp hz s (hsr.trans hrq)
  refine ⟨t,hts.trans hsr,?_⟩
  rcases hs with ⟨hs,hyD⟩ | ⟨hs,hy₀⟩ <;> rcases ht with ⟨ht,hzD⟩ | ⟨ht,hz₀⟩
  · exact S.mapsTo_unique hf (hts.trans (hsr.trans (hrq.trans hq)))
      (S.atomic.mem_mono (hts.trans (hsr.trans hrq)) ha) (S.app_mono hts hs) ht
  · exact (ht t le_rfl y (S.app_mono hts hs) (S.atomic.mem_mono hts hyD)).elim
  · exact (hs t hts z ht hzD).elim
  · exact S.atomic.eq_trans (S.atomic.eq_mono hts hy₀) (S.atomic.eq_symm hz₀)

def subsetImageGraph (f A D d : S.Name) : S.Name :=
  ((S.defaultRelation f D d).bounded A D).graph A D (S.tupleStabilizer ![f,A,D,d])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 2) (by
      intro g hg p a y h
      have hf : g • f = f := (S.mem_tupleStabilizer _ g).mp hg 0
      have hA : g • A = A := (S.mem_tupleStabilizer _ g).mp hg 1
      have hD : g • D = D := (S.mem_tupleStabilizer _ g).mp hg 2
      have hd : g • d = d := (S.mem_tupleStabilizer _ g).mp hg 3
      refine ⟨?_,?_,(S.defaultRelation_symmetry f D d g hf hD hd p a y).mp h.2.2⟩
      · simpa only [hA] using (S.mem_symmetry g p a A).mp h.1
      · simpa only [hD] using (S.mem_symmetry g p y D).mp h.2.1)

/-- Every single nonempty subset of a surjective image is itself a surjective
image. The one default is explicitly given; no family of defaults is chosen. -/
theorem subset_image_surjection (f A B D d : S.Name) (p : P)
    (hf : S.Forces ![f,A,B] p (SetLanguage.surjection 0 1 2))
    (hD : S.SubsetF p D B) (hd : S.atomic.MemF p d D) :
    S.Forces ![S.subsetImageGraph f A D d,A,D] p (SetLanguage.surjection 0 1 2) := by
  unfold subsetImageGraph
  apply BinaryRelation.graph_surjection
  · intro a q hq ha r hrq
    obtain ⟨s,hsr,y,hy,hR⟩ := S.defaultRelation_total f D d a (S.atomic.mem_mono hq hd) r hrq
    exact ⟨s,hsr,y,hy,S.atomic.mem_mono (hsr.trans hrq) ha,hy,hR⟩
  · intro q hq a y z hy hz
    exact S.defaultRelation_unique_on f A B D d p (S.surjection_mapsTo hf) hq a y z
      hy.1 hy.2.2 hz.2.2
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,a,ha,hay⟩ := S.surjection_onto hf hq (hD y q hq hy) r hrq
    have hsD := S.atomic.mem_mono (hsr.trans hrq) hy
    exact ⟨s,hsr,a,ha,ha,hsD,S.defaultRelation_of_app hay hsD⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceRelations -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace BinaryRelation
/-- Existential projection, with the regular forcing meaning of existence. -/
def image (R : S.BinaryRelation) : S.UnaryRelation where
  holds p y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x y
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,x,hx⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,x,hx⟩
  congr := by
    intro p y z he
    have step {y z : S.Name} (he : S.atomic.EqF p y z)
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x y) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x z := by
      intro q hq
      obtain ⟨r,hrq,x,hx⟩ := h q hq
      exact ⟨r,hrq,x,(R.congr (S.atomic.eq_refl r x) (S.atomic.eq_mono (hrq.trans hq) he)).mp hx⟩
    exact ⟨step he,step (S.atomic.eq_symm he)⟩

omit [OrderTop P] in
theorem image_move (R : S.BinaryRelation) (g : Γ)
    (hR : ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))
    (p : P) (y : S.Name) (h : R.image.holds p y) :
    R.image.holds (S.move g p) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,x,hx⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • x,hR r x y hx⟩

end BinaryRelation

/-- Parameters of the ordinal slicing of a presentation and a surjection.
There are no correctness assumptions in this structure. -/
structure SliceData (S : SymmetricSystem.{u} P Γ) where
  s : S.Name
  f : S.Name
  A : S.Name
  X : S.Name
  Y : S.Name
  O : ZFSet.{u}

namespace SliceData
variable (D : SliceData S)

def support : Subgroup Γ := S.tupleStabilizer ![D.s,D.f,D.A,D.X,D.Y]
omit [OrderTop P] in
theorem support_mem : D.support ∈ S.filter := S.tupleStabilizer_mem _
omit [OrderTop P] in
theorem fix_s {g : Γ} (hg : g ∈ D.support) : g • D.s = D.s := (S.mem_tupleStabilizer _ g).mp hg 0
omit [OrderTop P] in
theorem fix_f {g : Γ} (hg : g ∈ D.support) : g • D.f = D.f := (S.mem_tupleStabilizer _ g).mp hg 1
omit [OrderTop P] in
theorem fix_A {g : Γ} (hg : g ∈ D.support) : g • D.A = D.A := (S.mem_tupleStabilizer _ g).mp hg 2
omit [OrderTop P] in
theorem fix_X {g : Γ} (hg : g ∈ D.support) : g • D.X = D.X := (S.mem_tupleStabilizer _ g).mp hg 3
omit [OrderTop P] in
theorem fix_Y {g : Γ} (hg : g ∈ D.support) : g • D.Y = D.Y := (S.mem_tupleStabilizer _ g).mp hg 4

/-- The restriction of the presentation to the i-th Cartesian slice. -/
def slice (i : D.O) : S.BinaryRelation where
  holds p a x := S.atomic.MemF p a D.A ∧ S.atomic.MemF p x D.X ∧
    S.App p D.s (a.opair (Name.check i.val)) x
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.atomic.mem_mono h hh.2.1,S.app_mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.1⟩)),S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),(S.appRelation D.s).regular (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr ha hx := and_congr (S.atomic.mem_congr ha (S.atomic.eq_refl _ _))
    (and_congr (S.atomic.mem_congr hx (S.atomic.eq_refl _ _))
      (S.app_congr (S.atomic.eq_refl _ _) (S.eq_opair_congr ha (S.atomic.eq_refl _ _)) hx))

theorem slice_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (a x : S.Name)
    (h : (D.slice i).holds p a x) : (D.slice i).holds (S.move g p) (g • a) (g • x) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [D.fix_A hg] using (S.mem_symmetry g p a D.A).mp h.1
  · simpa only [D.fix_X hg] using (S.mem_symmetry g p x D.X).mp h.2.1
  · simpa only [D.fix_s hg,Name.smul_opair,Name.smul_check] using
      (S.app_symmetry g p D.s (a.opair (Name.check i.val)) x).mp h.2.2

def B (i : D.O) : S.Name :=
  (D.slice i).image.select D.X D.support D.support_mem (fun _ hg => D.fix_X hg)
    (fun g hg => BinaryRelation.image_move _ g (D.slice_move g hg i))

theorem fix_B (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.B i = D.B i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

theorem mem_B (i : D.O) (x : S.Name) (p : P) :
    S.atomic.MemF p x (D.B i) ↔ (D.slice i).image.holds p x := by
  rw [B,UnaryRelation.mem_select]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨S.atomic_regular.2 _ _ _ ?_,h⟩
    intro q hq
    obtain ⟨r,hrq,a,ha⟩ := h q hq
    exact ⟨r,hrq,ha.2.1⟩

theorem B_subset (i : D.O) (p : P) : S.SubsetF p (D.B i) D.X := by
  intro x q _ hx
  exact ((UnaryRelation.mem_select _ _ _ _ _ _ x q).mp hx).1

/-- An occurrence of a target value in f[B_i]. -/
def occurrence (i : D.O) : S.UnaryRelation := (S.boundedApp D.f (D.B i) D.Y).image

theorem occurrence_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (y : S.Name)
    (h : (D.occurrence i).holds p y) : (D.occurrence i).holds (S.move g p) (g • y) :=
  BinaryRelation.image_move _ g (S.boundedApp_move D.f (D.B i) D.Y g
    (D.fix_f hg) (D.fix_B g hg i) (D.fix_Y hg)) p y h

/-- The target pieces are occurrences at their least index in the fixed
wellordering of the ground ordinal. -/
def Ypart (i : D.O) : S.Name :=
  (LeastOccurrence.predicate D.O D.occurrence i).select D.Y D.support D.support_mem
    (fun _ hg => D.fix_Y hg)
    (fun g hg _ _ h => LeastOccurrence.move D.O D.occurrence D.support D.occurrence_move g hg h)

theorem fix_Ypart (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.Ypart i = D.Ypart i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

theorem mem_Ypart (i : D.O) (y : S.Name) (p : P) :
    S.atomic.MemF p y (D.Ypart i) ↔
      S.atomic.MemF p y D.Y ∧ LeastOccurrence.At D.O D.occurrence p y i :=
  UnaryRelation.mem_select _ _ _ _ _ _ y p

theorem Ypart_subset (i : D.O) (p : P) : S.SubsetF p (D.Ypart i) D.Y :=
  fun y q _ hy => ((D.mem_Ypart i y q).mp hy).1

theorem Ypart_disjoint {i j : D.O} {p : P} {y : S.Name}
    (hi : S.atomic.MemF p y (D.Ypart i)) (hj : S.atomic.MemF p y (D.Ypart j)) : i = j :=
  LeastOccurrence.unique D.O D.occurrence ((D.mem_Ypart i y p).mp hi).2
    ((D.mem_Ypart j y p).mp hj).2

def preimage (i : D.O) : S.UnaryRelation := (S.boundedApp D.f (D.B i) (D.Ypart i)).inverse.image

theorem preimage_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (x : S.Name)
    (h : (D.preimage i).holds p x) : (D.preimage i).holds (S.move g p) (g • x) :=
  BinaryRelation.image_move _ g (fun p y x h => S.boundedApp_move D.f (D.B i) (D.Ypart i) g
    (D.fix_f hg) (D.fix_B g hg i) (D.fix_Ypart g hg i) p x y h) p x h

/-- The source pieces are B_i intersected with the preimages of Y_i. -/
def Spart (i : D.O) : S.Name :=
  (D.preimage i).select (D.B i) D.support D.support_mem (fun g hg => D.fix_B g hg i)
    (fun g hg => D.preimage_move g hg i)

theorem fix_Spart (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.Spart i = D.Spart i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

theorem mem_Spart (i : D.O) (x : S.Name) (p : P) :
    S.atomic.MemF p x (D.Spart i) ↔ S.atomic.MemF p x (D.B i) ∧ (D.preimage i).holds p x :=
  UnaryRelation.mem_select _ _ _ _ _ _ x p

theorem Spart_subset_B (i : D.O) (p : P) : S.SubsetF p (D.Spart i) (D.B i) :=
  fun x q _ hx => ((D.mem_Spart i x q).mp hx).1

theorem Spart_subset (i : D.O) (p : P) : S.SubsetF p (D.Spart i) D.X :=
  fun x q hq hx => D.B_subset i p x q hq (D.Spart_subset_B i p x q hq hx)

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceGeometry -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace SliceData
variable (D : SliceData S)

def sliceGraph (i : D.O) : S.Name :=
  (D.slice i).graph D.A (D.B i) D.support D.support_mem (fun _ hg => D.fix_A hg)
    (fun g hg => D.fix_B g hg i) (fun g hg => D.slice_move g hg i)

/-- Each Cartesian slice surjects onto its actual image. -/
theorem sliceGraph_surjection (i : D.O) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![D.sliceGraph i,D.A,D.B i] p (SetLanguage.surjection 0 1 2) := by
  unfold sliceGraph
  apply BinaryRelation.graph_surjection
  · intro a q hq ha r hrq
    have hab := (S.opair_mem_cartesianName D.A (Name.check D.O) a (Name.check i.val) q).mpr
      ⟨ha,S.check_mem_of_mem i.property q⟩
    obtain ⟨s,hsr,x,hx,hax⟩ := S.mapsTo_total hs hq hab r hrq
    have hR : (D.slice i).holds s a x := ⟨S.atomic.mem_mono (hsr.trans hrq) ha,hx,hax⟩
    exact ⟨s,hsr,x,(D.mem_B i x s).mpr (fun t hts => ⟨t,le_rfl,a,(D.slice i).mono hts hR⟩),hR⟩
  · intro q hq a x y hx hy
    exact S.mapsTo_unique hs hq
      ((S.opair_mem_cartesianName D.A (Name.check D.O) a (Name.check i.val) q).mpr
        ⟨hx.1,S.check_mem_of_mem i.property q⟩) hx.2.2 hy.2.2
  · intro x q _ hx r hrq
    obtain ⟨s,hsr,a,ha⟩ := (D.mem_B i x q).mp hx r hrq
    exact ⟨s,hsr,a,ha.1,ha⟩

/-- Restrict f to the disjoint source and target pieces. -/
def partGraph (i : D.O) : S.Name := S.restrictionGraph D.f (D.Spart i) (D.Ypart i)

theorem partGraph_surjection (i : D.O) (p : P)
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![D.partGraph i,D.Spart i,D.Ypart i] p (SetLanguage.surjection 0 1 2) := by
  unfold partGraph restrictionGraph
  apply BinaryRelation.graph_surjection
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,y,hxB,hy,hxy⟩ := ((D.mem_Spart i x q).mp hx).2 r hrq
    have hxS := S.atomic.mem_mono (hsr.trans hrq) hx
    exact ⟨s,hsr,y,hy,hxS,hy,hxy⟩
  · intro q hq x y z hy hz
    exact S.mapsTo_unique hf hq (D.Spart_subset i p x q hq hy.1) hy.2.2 hz.2.2
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,x,hxB,hyY,hxy⟩ := ((D.mem_Ypart i y q).mp hy).2.1 r hrq
    have hy' := S.atomic.mem_mono (hsr.trans hrq) hy
    have hxS : S.atomic.MemF s x (D.Spart i) := (D.mem_Spart i x s).mpr
      ⟨hxB,fun t hts => ⟨t,le_rfl,y,S.atomic.mem_mono hts hxB,S.atomic.mem_mono hts hy',
        S.app_mono hts hxy⟩⟩
    exact ⟨s,hsr,x,hxS,hxS,hy',hxy⟩

/-- The source pieces need not cover X, but they are pairwise disjoint. -/
theorem Spart_disjoint (p : P)
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.mapsTo 0 1 2))
    {i j : D.O} {q : P} (hq : q ≤ p) {x : S.Name}
    (hi : S.atomic.MemF q x (D.Spart i)) (hj : S.atomic.MemF q x (D.Spart j)) : i = j := by
  obtain ⟨r,hrq,y,hxB,hy,hxy⟩ := ((D.mem_Spart i x q).mp hi).2 q le_rfl
  obtain ⟨s,hsr,z,_,hz,hxz⟩ := ((D.mem_Spart j x q).mp hj).2 r hrq
  have hxX := D.B_subset i p x s (hsr.trans (hrq.trans hq)) (S.atomic.mem_mono hsr hxB)
  have he := S.mapsTo_unique hf (hsr.trans (hrq.trans hq)) hxX (S.app_mono hsr hxy) hxz
  exact D.Ypart_disjoint ((S.atomic.mem_congr he (S.atomic.eq_refl s (D.Ypart i))).mp
    (S.atomic.mem_mono hsr hy)) hz

/-- All target values occur in some slice, densely with an actual ground
index. No choice of slice indices is made. -/
theorem occurrence_cover (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (y : S.Name) {q : P} (hq : q ≤ p) (hy : S.atomic.MemF q y D.Y) :
    ∀ r, r ≤ q → ∃ t, t ≤ r ∧ ∃ i : D.O, (D.occurrence i).holds t y := by
  intro r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
  obtain ⟨t,hts,z,hz,hzx⟩ := S.surjection_onto hs (hsr.trans (hrq.trans hq)) hx s le_rfl
  obtain ⟨b,hbt,a,j,ha,hj,hzaj⟩ := (S.mem_cartesianName D.A (Name.check D.O) z t).mp hz t le_rfl
  obtain ⟨c,hcb,k,hk,hjk⟩ := (S.mem_check D.O j b).mp hj b le_rfl
  let i : D.O := ⟨k,hk⟩
  have hzai := S.atomic.eq_trans (S.atomic.eq_mono hcb hzaj)
    (S.eq_opair_congr (S.atomic.eq_refl c a) hjk)
  have hax := (S.app_congr (S.atomic.eq_refl c D.s) hzai (S.atomic.eq_refl c x)).mp
    (S.app_mono (hcb.trans hbt) hzx)
  have hslice : (D.slice i).holds c a x :=
    ⟨S.atomic.mem_mono hcb ha,S.atomic.mem_mono (hcb.trans (hbt.trans hts)) hx,hax⟩
  have hxB := (D.mem_B i x c).mpr (fun d hdc => ⟨d,le_rfl,a,(D.slice i).mono hdc hslice⟩)
  refine ⟨c,hcb.trans (hbt.trans (hts.trans hsr)),i,?_⟩
  intro d hdc
  exact ⟨d,le_rfl,x,S.atomic.mem_mono hdc hxB,
    S.atomic.mem_mono (hdc.trans (hcb.trans (hbt.trans (hts.trans (hsr.trans hrq))))) hy,
    S.app_mono (hdc.trans (hcb.trans (hbt.trans hts))) hxy⟩

/-- Taking the least occurrence partitions the whole target. -/
theorem Ypart_cover (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (y : S.Name) {q : P} (hq : q ≤ p) (hy : S.atomic.MemF q y D.Y) :
    ∀ r, r ≤ q → ∃ t, t ≤ r ∧ ∃ i : D.O, S.atomic.MemF t y (D.Ypart i) := by
  intro r hrq
  obtain ⟨t,htr,i,hi⟩ := LeastOccurrence.dense D.O D.occurrence y q
    (D.occurrence_cover p hs hf y hq hy) r hrq
  exact ⟨t,htr,i,(D.mem_Ypart i y t).mpr ⟨S.atomic.mem_mono (htr.trans hrq) hy,hi⟩⟩

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI

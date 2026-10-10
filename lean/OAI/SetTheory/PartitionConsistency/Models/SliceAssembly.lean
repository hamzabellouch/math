import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.SliceGeometry
import OAI.SetTheory.PartitionConsistency.Models.ConcreteQuotients

namespace OAI

/-! ## SliceAssembly -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The empty binary relation, with its regular interpretation. -/
def falseRelation : S.BinaryRelation where
  holds _ _ _ := False
  mono _ h := h
  regular h := by obtain ⟨_,_,h⟩ := h _ le_rfl; exact h
  congr _ _ := Iff.rfl

/-- An empty domain has an internal injection into any set. -/
theorem empty_domain_injection (X Y : S.Name) (p : P)
    (hX : ∀ x q, q ≤ p → ¬ S.atomic.MemF q x X) :
    ∃ j : S.Name, S.Forces ![j,X,Y] p (SetLanguage.injection 0 1 2) := by
  let H := S.tupleStabilizer ![X,Y]
  refine ⟨S.falseRelation.graph X Y H (S.tupleStabilizer_mem _)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 0)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1) (fun _ _ _ _ _ h => h.elim),?_⟩
  apply BinaryRelation.graph_injection
  · intro x q hq hx
    exact (hX x q hq hx).elim
  · intro q hq x y z h
    exact h.elim
  · intro q hq x y z h
    exact h.elim

theorem empty_domain_wellorderable (X : S.Name) (p : P)
    (hX : ∀ x q, q ≤ p → ¬ S.atomic.MemF q x X) :
    S.Forces ![X] p (SetLanguage.wellorderable 0) := by
  obtain ⟨j,hj⟩ := S.empty_domain_injection X (Name.check (0 : Ordinal.{u}).toZFSet) p hX
  exact S.wellorderable_of_check_injection X j 0 p hj

/-- Nonwellorderability alone supplies a member densely. This selects only
one member below one condition, never a family of default members. -/
theorem nonwellorderable_member_dense (X : S.Name) (p : P)
    (hX : S.Forces ![X] p (SetLanguage.wellorderable 0).neg) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x X := by
  intro q hq
  by_contra h
  have he : ∀ x r, r ≤ q → ¬ S.atomic.MemF r x X := fun x r hr hx => h ⟨r,hr,x,hx⟩
  exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp hX q hq
    (S.empty_domain_wellorderable X q he)

namespace SliceData
variable {S} (D : SliceData S)

/-- A uniformly supported family of candidate injections is assembled into
one graph. Totality uses the target partition, while one-to-one-ness uses the
disjoint source pieces. No assertion that these source pieces cover X is made. -/
theorem assemble (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (c : D.O → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter) (hHD : H ≤ D.support)
    (hc : ∀ g ∈ H, ∀ i, g • c i = c i)
    (hj : ∀ i, S.Forces ![c i,D.Ypart i,D.Spart i] p (SetLanguage.injection 0 1 2)) :
    ∃ j : S.Name, S.Forces ![j,D.Y,D.X] p (SetLanguage.injection 0 1 2) := by
  let R := BinaryRelation.familyUnion (fun i => S.boundedApp (c i) (D.Ypart i) (D.Spart i))
  have hR : ∀ g ∈ H, ∀ t y x, R.holds t y x → R.holds (S.move g t) (g • y) (g • x) := by
    intro g hg
    exact BinaryRelation.familyUnion_move _ g (fun i => S.boundedApp_move _ _ _ g
      (hc g hg i) (D.fix_Ypart g (hHD hg) i) (D.fix_Spart g (hHD hg) i))
  refine ⟨R.graph D.Y D.X H hH (fun _ hg => D.fix_Y (hHD hg))
    (fun _ hg => D.fix_X (hHD hg)) hR,?_⟩
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,i,hyi⟩ := D.Ypart_cover p hs hf y hq hy r hrq
    obtain ⟨t,hts,x,hxi,hyx⟩ := S.mapsTo_total (S.injection_mapsTo (hj i))
      (hsr.trans (hrq.trans hq)) hyi s le_rfl
    exact ⟨t,hts.trans hsr,x,D.Spart_subset i p x t (hts.trans (hsr.trans (hrq.trans hq))) hxi,
      fun b hbt => ⟨b,le_rfl,i,S.atomic.mem_mono (hbt.trans hts) hyi,
        S.atomic.mem_mono hbt hxi,S.app_mono hbt hyx⟩⟩
  · intro q hq y x z hx hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hyi,hxi,hyx⟩ := hx r hrq
    obtain ⟨t,hts,k,hyk,hzk,hyz⟩ := hz s (hsr.trans hrq)
    have hik := D.Ypart_disjoint (S.atomic.mem_mono hts hyi) hyk
    subst k
    exact ⟨t,hts.trans hsr,S.mapsTo_unique (S.injection_mapsTo (hj i))
      (hts.trans (hsr.trans (hrq.trans hq))) hyk (S.app_mono hts hyx) hyz⟩
  · intro q hq y z x hy hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hyi,hxi,hyx⟩ := hy r hrq
    obtain ⟨t,hts,k,hzk,hxk,hzx⟩ := hz s (hsr.trans hrq)
    have htp := hts.trans (hsr.trans (hrq.trans hq))
    have hik := D.Spart_disjoint p (S.surjection_mapsTo hf) htp (S.atomic.mem_mono hts hxi) hxk
    subst k
    exact ⟨t,hts.trans hsr,S.injection_one (hj i) htp (S.atomic.mem_mono hts hyi) hzk
      (S.app_mono hts hyx) hzx⟩

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceCandidates -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- Pointwise existence of a candidate. The wellorderable case uses ordinal
choice for the fibers of this one slice. In the other case two classified
images of A give a reverse injection; it need not be a section of f. -/
theorem slice_candidate (D : SliceData S) (hA : D.A = A) (i : D.O) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name,
      S.Forces ![j,D.Ypart i,D.Spart i] q (SetLanguage.injection 0 1 2) := by
  have hpart := D.partGraph_surjection i p (S.surjection_mapsTo hf)
  by_cases hwo : ∃ q, q ≤ p ∧ S.Forces ![D.Ypart i] q (SetLanguage.wellorderable 0)
  · obtain ⟨q,hqp,hwo⟩ := hwo
    obtain ⟨r,hrq,j,hj⟩ := wellorderable_target_injection (D.partGraph i) (D.Spart i) (D.Ypart i)
      q (S.atomic.forceFormula_mono hqp hpart) hwo
    exact ⟨r,hrq.trans hqp,j,hj⟩
  · have hYn : S.Forces ![D.Ypart i] p (SetLanguage.wellorderable 0).neg :=
      (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr (fun q hq hh => hwo ⟨q,hq,hh⟩)
    have hSn : S.Forces ![D.Spart i] p (SetLanguage.wellorderable 0).neg := by
      apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
      intro q hq hh
      exact hwo ⟨q,hq,S.wellorderable_image (D.partGraph i) (D.Spart i) (D.Ypart i) q
        (S.atomic.forceFormula_mono hq hpart) hh⟩
    obtain ⟨q,hqp,d,hd⟩ := S.nonwellorderable_member_dense (D.Spart i) p hSn p le_rfl
    have hB : S.Forces ![D.sliceGraph i,A,D.B i] q (SetLanguage.surjection 0 1 2) := by
      rw [← hA]
      exact D.sliceGraph_surjection i q (S.surjection_mapsTo (S.atomic.forceFormula_mono hqp hs))
    let aS := S.subsetImageGraph (D.sliceGraph i) A (D.Spart i) d
    have has : S.Forces ![aS,A,D.Spart i] q (SetLanguage.surjection 0 1 2) :=
      S.subset_image_surjection (D.sliceGraph i) A (D.B i) (D.Spart i) d q hB (D.Spart_subset_B i q) hd
    let aY := S.compositionGraph aS (D.partGraph i) A (D.Spart i) (D.Ypart i)
    have hay : S.Forces ![aY,A,D.Ypart i] q (SetLanguage.surjection 0 1 2) :=
      S.compositionGraph_surjection _ _ _ _ _ q has (S.atomic.forceFormula_mono hqp hpart)
    obtain ⟨r,hrq,kS,hkS⟩ := nonwellorderable_image_bijection aS (D.Spart i) q has
      (S.atomic.forceFormula_mono hqp hSn)
    obtain ⟨t,htr,kY,hkY⟩ := nonwellorderable_image_bijection aY (D.Ypart i) r
      (S.atomic.forceFormula_mono hrq hay) (S.atomic.forceFormula_mono (hrq.trans hqp) hYn)
    have hkS := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp
      (S.atomic.forceFormula_mono htr hkS)
    have hkY := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp hkY
    have hi := S.inverseGraph_injection kY A (D.Ypart i) t hkY.1 hkY.2
    exact ⟨t,htr.trans (hrq.trans hqp),
      S.compositionGraph (S.inverseGraph kY A (D.Ypart i)) kS (D.Ypart i) A (D.Spart i),
      S.compositionGraph_injection _ _ _ _ _ t hi hkS.2⟩

/-- Choose the already defined slice injections with one common support and
assemble them. There is no simultaneous selection of auxiliary wellorderings,
defaults, or quotient bijections in the pointwise argument. -/
theorem presentation_reverse_injection (D : SliceData S) (hA : D.A = A) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,D.Y,D.X] q (SetLanguage.injection 0 1 2) := by
  let v : D.O → Fin 2 → S.Name := fun i => ![D.Ypart i,D.Spart i]
  have hv : ∀ g ∈ D.support, ∀ i k, g • v i k = v i k := by
    intro g hg i k
    fin_cases k
    · exact D.fix_Ypart g hg i
    · exact D.fix_Spart g hg i
  have hex : ∀ i, S.Forces (v i) p (SetLanguage.injection 2 0 1).ex := by
    intro i q hqp
    obtain ⟨r,hrq,j,hj⟩ := slice_candidate D hA i q
      (S.atomic.forceFormula_mono hqp hs) (S.atomic.forceFormula_mono hqp hf)
    refine ⟨r,hrq,j,?_⟩
    have he : Fin.snoc (v i) j = ![D.Ypart i,D.Spart i,j] := by
      ext k
      fin_cases k <;> rfl
    rw [he]
    exact (S.forces_injection _ r 2 0 1).mpr ((S.forces_injection _ r 0 1 2).mp hj)
  obtain ⟨q,hqp,H,hH,c,hc,hj⟩ := uniform_maximum_dense (SetLanguage.injection 2 0 1) v
    D.support D.support_mem hv p hex
  obtain ⟨j,hj⟩ := D.assemble q (S.atomic.forceFormula_mono hqp hs) (S.atomic.forceFormula_mono hqp hf)
    c (D.support ⊓ H) (S.normal.2.2.1 _ _ D.support_mem hH) inf_le_left
    (fun g hg => hc g hg.2) (by
      intro i
      have hi := hj i
      have he : Fin.snoc (v i) (c i) = ![D.Ypart i,D.Spart i,c i] := by
        ext k
        fin_cases k <;> rfl
      rw [he] at hi
      exact (S.forces_injection _ q 0 1 2).mpr ((S.forces_injection _ q 2 0 1).mp hi))
  exact ⟨q,hqp,j,hj⟩

end
end PartitionConsistency.ConcreteSystem

end OAI

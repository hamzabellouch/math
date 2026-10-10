import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.RelationCalculus
import OAI.SetTheory.PartitionConsistency.Models.ConcreteQuotients
import OAI.SetTheory.PartitionConsistency.Models.UniformNames

namespace OAI

/-! ## KernelImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def kernelRelation (h A B : S.Name) : S.BinaryRelation :=
  (S.boundedApp h A B).comp (S.boundedApp h A B).inverse

theorem kernelRelation_move (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B)
    (p : P) (a b : S.Name) (hab : (S.kernelRelation h A B).holds p a b) :
    (S.kernelRelation h A B).holds (S.move g p) (g • a) (g • b) := by
  intro q hq
  obtain ⟨r,hrq,y,ha,hb⟩ := hab ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • y,
    S.boundedApp_move h A B g hh hA hB r a y ha,
    S.boundedApp_move h A B g hh hA hB r b y hb⟩

def kernelGraph (h A B : S.Name) : S.Name :=
  (S.kernelRelation h A B).graph A A (S.tupleStabilizer ![h,A,B])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => S.kernelRelation_move h A B g ((S.mem_tupleStabilizer _ g).mp hg 0)
      ((S.mem_tupleStabilizer _ g).mp hg 1) ((S.mem_tupleStabilizer _ g).mp hg 2))

theorem kernelGraph_fixed (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B) :
    g • S.kernelGraph h A B = S.kernelGraph h A B := by
  apply BinaryRelation.graph_fixed
  apply (S.mem_tupleStabilizer _ g).mpr
  intro i
  fin_cases i <;> assumption

theorem app_kernelGraph (h A B a b : S.Name) (p : P) :
    S.App p (S.kernelGraph h A B) a b ↔ (S.kernelRelation h A B).holds p a b := by
  unfold kernelGraph
  erw [BinaryRelation.app_graph]
  constructor
  · exact fun hi => hi.2.2
  · intro hi
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,hi⟩
    · intro q hq
      obtain ⟨r,hrq,y,ha,_⟩ := hi q hq
      exact ⟨r,hrq,ha.1⟩
    · intro q hq
      obtain ⟨r,hrq,y,_,hb⟩ := hi q hq
      exact ⟨r,hrq,hb.1⟩

/-- Kernel membership says exactly equality of the actual function values;
no representatives of classes have been chosen. -/
theorem app_kernelGraph_value {h A B a y : S.Name} {p q : P}
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (ha : S.atomic.MemF q a A) (hay : S.App q h a y) (b : S.Name) :
    S.App q (S.kernelGraph h A B) a b ↔ S.atomic.MemF q b A ∧ S.App q h b y := by
  rw [S.app_kernelGraph]
  constructor
  · intro hi
    have hd r (hrq : r ≤ q) : ∃ s, s ≤ r ∧ S.atomic.MemF s b A ∧ S.App s h b y := by
      obtain ⟨s,hsr,z,has,hbs⟩ := hi r hrq
      have hzy := S.mapsTo_unique hf (hsr.trans (hrq.trans hq)) has.1 has.2.2
        (S.app_mono (hsr.trans hrq) hay)
      exact ⟨s,hsr,hbs.1,(S.app_congr (S.atomic.eq_refl s h) (S.atomic.eq_refl s b) hzy).mp hbs.2.2⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun r hr => (hd r hr).imp (fun s hs => ⟨hs.1,hs.2.1⟩)),
      (S.appRelation h).regular (fun r hr => (hd r hr).imp (fun s hs => ⟨hs.1,hs.2.2⟩))⟩
  · rintro ⟨hb,hby⟩ r hrq
    have hy := S.mapsTo_value hf hq ha hay
    exact ⟨r,le_rfl,y,⟨S.atomic.mem_mono hrq ha,S.atomic.mem_mono hrq hy,S.app_mono hrq hay⟩,
      ⟨S.atomic.mem_mono hrq hb,S.atomic.mem_mono hrq hy,S.app_mono hrq hby⟩⟩

theorem kernel_class_same_value {h A B a b y : S.Name} {p q : P}
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (ha : S.atomic.MemF q a A) (hb : S.atomic.MemF q b A)
    (hay : S.App q h a y) (hby : S.App q h b y) :
    S.atomic.EqF q (S.relationClass A (S.kernelGraph h A B) a)
      (S.relationClass A (S.kernelGraph h A B) b) := by
  apply S.eq_of_same_members
  intro x r hrq
  rw [S.mem_relationClass,S.mem_relationClass,
    S.app_kernelGraph_value hf (hrq.trans hq) (S.atomic.mem_mono hrq ha) (S.app_mono hrq hay),
    S.app_kernelGraph_value hf (hrq.trans hq) (S.atomic.mem_mono hrq hb) (S.app_mono hrq hby)]

/-- Graph of the representative-free correspondence `h(a) ↦ [a]`. -/
def imageClassRelation (h A B : S.Name) : S.BinaryRelation where
  holds p y C := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
    S.atomic.MemF r a A ∧ S.App r h a y ∧
      S.atomic.EqF r C (S.relationClass A (S.kernelGraph h A B) a)
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hh⟩ := h q hq
    obtain ⟨s,hsr,a,ha⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,a,ha⟩
  congr := by
    intro p y y' C C' hy hC
    have step {y y' C C' : S.Name} (hy : S.atomic.EqF p y y') (hC : S.atomic.EqF p C C')
        (hh : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
          S.atomic.MemF r a A ∧ S.App r h a y ∧ S.atomic.EqF r C
            (S.relationClass A (S.kernelGraph h A B) a)) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
          S.atomic.MemF r a A ∧ S.App r h a y' ∧ S.atomic.EqF r C'
            (S.relationClass A (S.kernelGraph h A B) a) := by
      intro q hq
      obtain ⟨r,hrq,a,ha,hay,he⟩ := hh q hq
      exact ⟨r,hrq,a,ha,(S.app_congr (S.atomic.eq_refl r h) (S.atomic.eq_refl r a)
        (S.atomic.eq_mono (hrq.trans hq) hy)).mp hay,
        S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hq) hC)) he⟩
    exact ⟨step hy hC,step (S.atomic.eq_symm hy) (S.atomic.eq_symm hC)⟩

theorem imageClassRelation_move (h A B : S.Name) (g : Γ)
    (hh : g • h = h) (hA : g • A = A) (hB : g • B = B)
    (p : P) (y C : S.Name) (hi : (S.imageClassRelation h A B).holds p y C) :
    (S.imageClassRelation h A B).holds (S.move g p) (g • y) (g • C) := by
  intro q hq
  obtain ⟨r,hrq,a,ha,hay,he⟩ := hi ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • a,?_,?_,?_⟩
  · simpa only [hA] using (S.mem_symmetry g r a A).mp ha
  · simpa only [hh] using (S.app_symmetry g r h a y).mp hay
  · simpa only [S.relationClass_move,hA,S.kernelGraph_fixed h A B g hh hA hB] using
      (S.eq_symmetry g r C _).mp he

theorem imageClassRelation_one (h A B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ y C D : S.Name,
      (S.imageClassRelation h A B).holds q y C →
      (S.imageClassRelation h A B).holds q y D → S.atomic.EqF q C D := by
  intro q hq y C D hC hD
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay,hCa⟩ := hC r hrq
  obtain ⟨t,hts,b,hb,hby,hDb⟩ := hD s (hsr.trans hrq)
  have hc := S.kernel_class_same_value hf (hts.trans (hsr.trans (hrq.trans hq)))
    (S.atomic.mem_mono hts ha) hb (S.app_mono hts hay) hby
  exact ⟨t,hts.trans hsr,S.atomic.eq_trans (S.atomic.eq_mono hts hCa)
    (S.atomic.eq_trans hc (S.atomic.eq_symm hDb))⟩

theorem imageClassRelation_inj (h A B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ y z C : S.Name,
      (S.imageClassRelation h A B).holds q y C →
      (S.imageClassRelation h A B).holds q z C → S.atomic.EqF q y z := by
  intro q hq y z C hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay,hCa⟩ := hy r hrq
  obtain ⟨t,hts,b,hb,hbz,hCb⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have ham := S.atomic.mem_mono hts ha
  have haym := S.app_mono hts hay
  have haa : S.atomic.MemF t a (S.relationClass A (S.kernelGraph h A B) a) :=
    (S.mem_relationClass _ _ _ _ _).mpr ⟨ham,
      (S.app_kernelGraph_value hf htp ham haym a).mpr ⟨ham,haym⟩⟩
  have heab := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hts hCa)) hCb
  have hab := (S.mem_relationClass _ _ _ _ _).mp
    ((S.atomic.mem_congr (S.atomic.eq_refl t a) heab).mp haa)
  have haz := ((S.app_kernelGraph_value hf htp hb hbz a).mp hab.2).2
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp ham haym haz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

abbrev A : S.Name := labelSet aleph0_le_μ (posetCode κ)

def imageQuotient (h B : S.Name) : S.Name :=
  quotientName aleph0_le_μ (posetCode κ) (S.kernelGraph h A B)

theorem mem_imageQuotient (h B C : S.Name) (p : P) :
    S.atomic.MemF p C (imageQuotient h B) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
        S.atomic.MemF r a A ∧ S.atomic.EqF r C (S.relationClass A (S.kernelGraph h A B) a) := by
  change (system aleph0_le_μ).atomic.MemF p C (quotientName _ _ _) ↔ _
  erw [mem_quotientName_iff_isClass]
  exact S.forces_isClass ![C,A,S.kernelGraph h A B] p 0 1 2

def imageQuotientGraph (h B : S.Name) : S.Name :=
  (S.imageClassRelation h A B).graph B (imageQuotient h B) (S.tupleStabilizer ![h,B])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => quotientName_fixed _ _ _ g (S.kernelGraph_fixed h A B g
      ((S.mem_tupleStabilizer _ g).mp hg 0) (smul_labelSet _ _ g)
      ((S.mem_tupleStabilizer _ g).mp hg 1)))
    (fun g hg => S.imageClassRelation_move h A B g ((S.mem_tupleStabilizer _ g).mp hg 0)
      (smul_labelSet _ _ g) ((S.mem_tupleStabilizer _ g).mp hg 1))

theorem app_imageQuotientGraph (h B y C : S.Name) (p : P) :
    S.App p (imageQuotientGraph h B) y C ↔
      S.atomic.MemF p y B ∧ S.atomic.MemF p C (imageQuotient h B) ∧
        (S.imageClassRelation h A B).holds p y C := by
  exact BinaryRelation.app_graph _ _ _ _ _ _ _ _ _ _ _

theorem imageQuotientGraph_mapsTo (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.mapsTo 0 1 2) := by
  unfold imageQuotientGraph
  apply BinaryRelation.graph_mapsTo
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,a,ha,hay⟩ := S.surjection_onto hf hq hy r hrq
    refine ⟨s,hsr,S.relationClass A (S.kernelGraph h A B) a,?_,?_⟩
    · exact (mem_imageQuotient _ _ _ _).mpr (fun t hts =>
        ⟨t,le_rfl,a,S.atomic.mem_mono hts ha,S.atomic.eq_refl t _⟩)
    · exact fun t hts => ⟨t,le_rfl,a,S.atomic.mem_mono hts ha,S.app_mono hts hay,S.atomic.eq_refl t _⟩
  · exact S.imageClassRelation_one h A B p (S.surjection_mapsTo hf)

theorem imageQuotientGraph_injection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨imageQuotientGraph_mapsTo h B p hf,?_⟩
  rintro x y z q hq _ r hrq _ s hsr ⟨hx,hy⟩
  have hx := (app_imageQuotientGraph h B x z s).mp hx
  have hy := (app_imageQuotientGraph h B y z s).mp hy
  exact S.imageClassRelation_inj h A B p (S.surjection_mapsTo hf) s
    (hsr.trans (hrq.trans hq)) x y z hx.2.2 hy.2.2

theorem imageQuotientGraph_surjection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨imageQuotientGraph_mapsTo h B p hf,?_⟩
  intro C q hq hC r hrq
  obtain ⟨s,hsr,a,ha,he⟩ := (mem_imageQuotient h B C q).mp hC r hrq
  obtain ⟨t,hts,y,hy,hay⟩ := S.mapsTo_total (S.surjection_mapsTo hf) (hsr.trans (hrq.trans hq)) ha s le_rfl
  refine ⟨t,hts.trans hsr,y,hy,?_⟩
  apply (app_imageQuotientGraph h B y C t).mpr
  refine ⟨hy,S.atomic.mem_mono (hts.trans (hsr.trans hrq)) hC,?_⟩
  exact fun b hbt => ⟨b,le_rfl,a,S.atomic.mem_mono (hbt.trans hts) ha,
    S.app_mono hbt hay,S.atomic.eq_mono (hbt.trans hts) he⟩

/-- Every nonwellorderable image of A is now bijective to A. This is
obtained from the actual kernel quotient and its representative-free graph. -/
theorem nonwellorderable_image_bijection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2))
    (hno : S.Forces ![B] p (SetLanguage.wellorderable 0).neg) :
    ∃ q, q ≤ p ∧ ∃ f : S.Name,
      S.Forces ![f,A,B] q ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  have hQ : S.Forces ![imageQuotient h B] p (SetLanguage.wellorderable 0).neg := by
    apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
    intro q hq hwo
    obtain ⟨r,hrq,η,hη,hinj⟩ := (S.forces_wellorderable _ _ _).mp hwo q le_rfl
    obtain ⟨s,hsr,J,hJ⟩ := hinj r le_rfl
    have hB : S.Forces ![B] s (SetLanguage.wellorderable 0) := by
      rw [S.forces_wellorderable]
      intro t hts
      refine ⟨t,le_rfl,η,S.atomic.forceFormula_mono (hts.trans hsr) hη,?_⟩
      intro a hat
      refine ⟨a,le_rfl,S.compositionGraph (imageQuotientGraph h B) J B (imageQuotient h B) η,?_⟩
      exact S.compositionGraph_injection _ _ _ _ _ a
        (S.atomic.forceFormula_mono (hat.trans (hts.trans (hsr.trans (hrq.trans hq))))
          (imageQuotientGraph_injection h B p hf))
        (S.atomic.forceFormula_mono (hat.trans hts) hJ)
    exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp hno s (hsr.trans (hrq.trans hq)) hB
  obtain ⟨q,hq,f,hf'⟩ := nonwellorderable_quotient_bijection (S.kernelGraph h A B) p hQ
  have hh := S.atomic.forceFormula_mono hq hf
  have hfi := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp hf'
  let J := S.inverseGraph (imageQuotientGraph h B) B (imageQuotient h B)
  have hJs := S.inverseGraph_surjection _ _ _ q (imageQuotientGraph_surjection h B q hh)
    (imageQuotientGraph_injection h B q hh)
  have hJi := S.inverseGraph_injection _ _ _ q (imageQuotientGraph_surjection h B q hh)
    (imageQuotientGraph_injection h B q hh)
  refine ⟨q,hq,S.compositionGraph f J A (imageQuotient h B) B,?_⟩
  apply (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mpr
  exact ⟨S.compositionGraph_surjection _ _ _ _ _ q hfi.1 hJs,
    S.compositionGraph_injection _ _ _ _ _ q hfi.2 hJi⟩

end
end PartitionConsistency.ConcreteSystem


/-! ## UniformMaximum -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- Simultaneous use of the localized maximum principle. The same larger
root is chosen before any witnesses, hence all the witnesses have one common
support, even for a ground family of arbitrarily large small cardinality. -/
theorem uniform_maximum_dense {ι : Sort*} {n} (φ : Formula (n+1))
    (v : ι → Fin n → S.Name) (H : Subgroup (Equiv.Perm I)) (hH : H ∈ S.filter)
    (hv : ∀ g ∈ H, ∀ i k, g • v i k = v i k)
    (t : P) (hf : ∀ i, S.Forces (v i) t φ.ex) :
    ∃ r, r ≤ t ∧ ∃ G : Subgroup (Equiv.Perm I), G ∈ S.filter ∧
      ∃ f : ι → S.Name, (∀ g ∈ G, ∀ i, g • f i = f i) ∧
        ∀ i, S.Forces (Fin.snoc (v i) (f i)) r φ := by
  obtain ⟨emb⟩ := (Cardinal.le_def T I).mp size_lt.le
  let : Nonempty (Diagram T I) := ⟨⟨emb⟩⟩
  obtain ⟨a,hat⟩ := exists_condition_below t
  obtain ⟨J,hJ,hJH⟩ := hH
  have hU : Cardinal.mk ↥(J ∪ a.1.support) ≤ Cardinal.mk T := by
    rw [cardinal_T]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (a.1.cardinal_support.trans aleph0_le_μ)).trans_eq
        (Cardinal.add_eq_self aleph0_le_μ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through size_lt T.e complement_cardinal a.2 hU
  have hpa : ((a.1,p) : P) ≤ t :=
    (WithTop.coe_le_coe.mpr (show (a.1,p) ≤ a from ⟨le_rfl,⟨T.e,hp⟩⟩)).trans hat
  obtain ⟨q,hq,_⟩ := Diagram.extend_through size_lt T.e complement_cardinal p
    (J := ∅) (by simp)
  have hqp : q ≤ p := ⟨T.e,hq⟩
  have hc : a.1.support ⊆ q.range := fun k hk => Diagram.range_antitone hqp (hcover (Or.inr hk))
  have hvec : ∀ g ∈ SupportFilter.Fix p.range, ∀ i k, g • v i k = v i k := by
    intro g hg
    exact hv g (hJH ((SupportFilter.mem_Fix _ _).mpr (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp hg k (hcover (Or.inl hk)))))
  have hchoice : ∀ i, ∃ f : S.Name, (∀ g ∈ SupportFilter.Fix q.range, g • f = f) ∧
      S.Forces (Fin.snoc (v i) f) ((a.1,q) : P) φ := by
    intro i
    exact localized_maximum aleph0_le_μ cardinal_T size_lt finiteMergers T.e complement_cardinal
      rootProbes φ (v i) p q hq (fun g hg k => hvec g hg i k) a.1 hc
      (S.atomic.forceFormula_mono hpa (hf i))
  choose f hfix hforce using hchoice
  exact ⟨(a.1,q),(WithTop.coe_le_coe.mpr (show (a.1,q) ≤ (a.1,p) from ⟨le_rfl,hqp⟩)).trans hpa,
    SupportFilter.Fix q.range,⟨q.range,by rw [Diagram.cardinal_range,cardinal_T],le_rfl⟩,
    f,fun g hg i => hfix i g hg,hforce⟩

end
end PartitionConsistency.ConcreteSystem

end OAI

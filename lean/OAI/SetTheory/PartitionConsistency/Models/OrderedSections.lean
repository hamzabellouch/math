import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.UniformImages
import OAI.SetTheory.PartitionConsistency.Models.OrdinalChoice

namespace OAI

/-! ## LeastOccurrence -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace LeastOccurrence
variable (X : ZFSet.{u}) (R : X → S.UnaryRelation)

/-- Occurrence at this index and forced nonoccurrence at every smaller
index in the fixed ground wellordering. -/
def At (p : P) (x : S.Name) (i : X) : Prop :=
  (R i).holds p x ∧ ∀ j, WellOrderingRel j i → ∀ q, q ≤ p → ¬ (R j).holds q x

omit [OrderTop P] in
theorem mono {p q : P} {x : S.Name} {i : X} (h : q ≤ p) (hi : At X R p x i) : At X R q x i :=
  ⟨(R i).mono h hi.1,fun j hj r hr => hi.2 j hj r (hr.trans h)⟩

omit [OrderTop P] in
theorem congr {p : P} {x y : S.Name} {i : X} (he : S.atomic.EqF p x y) :
    At X R p x i ↔ At X R p y i := by
  have step {x y : S.Name} (he : S.atomic.EqF p x y) (h : At X R p x i) : At X R p y i := by
    refine ⟨((R i).congr he).mp h.1,?_⟩
    intro j hj q hq hy
    exact h.2 j hj q hq (((R j).congr (S.atomic.eq_mono hq he)).mpr hy)
  exact ⟨step he,step (S.atomic.eq_symm he)⟩

omit [OrderTop P] in
theorem unique {p : P} {x : S.Name} {i j : X} (hi : At X R p x i) (hj : At X R p x j) : i = j := by
  rcases trichotomous_of WellOrderingRel i j with hh | hh | hh
  · exact (hj.2 i hh p le_rfl hi.1).elim
  · exact hh
  · exact (hi.2 j hh p le_rfl hj.1).elim

def predicate (i : X) : S.UnaryRelation where
  holds p x := At X R p x i
  mono := mono X R
  regular := by
    intro p x h
    refine ⟨(R i).regular (fun q hq => (h q hq).imp (fun r hr => ⟨hr.1,hr.2.1⟩)),?_⟩
    intro j hj q hq hi
    obtain ⟨r,hrq,hr⟩ := h q hq
    exact hr.2 j hj r le_rfl ((R j).mono hrq hi)
  congr := congr X R

omit [OrderTop P] in
/-- Minimal compatible occurrence exists densely. -/
theorem dense (x : S.Name) (p : P)
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, At X R r x i := by
  intro q hq
  have hne : {i | ∃ r, r ≤ q ∧ (R i).holds r x}.Nonempty := by
    obtain ⟨r,hrq,i,hi⟩ := h q hq
    exact ⟨i,r,hrq,hi⟩
  obtain ⟨i,⟨r,hrq,hi⟩,hmin⟩ := WellOrderingRel.isWellOrder.wf.has_min _ hne
  exact ⟨r,hrq,i,hi,fun j hj s hsr hs => hmin j ⟨s,hsr.trans hrq,hs⟩ hj⟩

omit [OrderTop P] in
theorem move (H : Subgroup Γ)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (g : Γ) (hg : g ∈ H) {p : P} {x : S.Name} {i : X} (hi : At X R p x i) :
    At X R (S.move g p) (g • x) i := by
  refine ⟨hR g hg i p x hi.1,?_⟩
  intro j hj q hq hh
  have hback := hR g⁻¹ (H.inv_mem hg) j q (g • x) hh
  have heq : S.move g⁻¹ q = (S.move g).symm q := by
    change S.codeEquiv.symm (S.action.perm g⁻¹ (S.codeEquiv q)) =
      S.codeEquiv.symm ((S.action.perm g).symm (S.codeEquiv q))
    rw [map_inv]
    rfl
  simp only [inv_smul_smul,heq] at hback
  exact hi.2 j hj ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq) hback

/-- The least-index graph, regularized in both the value and index names. -/
def relation : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
    S.atomic.EqF r y (Name.check i.val) ∧ At X R r x i
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,i,hi⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
          S.atomic.EqF r y (Name.check i.val) ∧ At X R r x i) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
          S.atomic.EqF r y' (Name.check i.val) ∧ At X R r x' i := by
      intro q hq
      obtain ⟨r,hrq,i,hi,hr⟩ := h q hq
      exact ⟨r,hrq,i,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hq) hy)) hi,
        (congr X R (S.atomic.eq_mono (hrq.trans hq) hx)).mp hr⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

theorem relation_one {p : P} {x y z : S.Name}
    (hy : (relation X R).holds p x y) (hz : (relation X R).holds p x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hq
  obtain ⟨r,hrq,i,hyi,hi⟩ := hy q hq
  obtain ⟨s,hsr,j,hzj,hj⟩ := hz r (hrq.trans hq)
  have hij := unique X R (mono X R hsr hi) hj
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hyi) (S.atomic.eq_symm hzj)⟩

theorem relation_inj (p : P)
    (hone : ∀ i q, q ≤ p → ∀ x y, (R i).holds q x → (R i).holds q y → S.atomic.EqF q x y) :
    ∀ q, q ≤ p → ∀ x y z, (relation X R).holds q x z →
      (relation X R).holds q y z → S.atomic.EqF q x y := by
  intro q hq x y z hx hy
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,i,hzi,hi⟩ := hx r hrq
  obtain ⟨t,hts,j,hzj,hj⟩ := hy s (hsr.trans hrq)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val t).mp
    (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hts hzi)) hzj))
  subst j
  exact ⟨t,hts.trans hsr,hone i t (hts.trans (hsr.trans (hrq.trans hq))) x y
    ((R i).mono hts hi.1) hj.1⟩

theorem relation_move (H : Subgroup Γ)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (g : Γ) (hg : g ∈ H) (p : P) (x y : S.Name) (h : (relation X R).holds p x y) :
    (relation X R).holds (S.move g p) (g • x) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,i,he,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,?_,move X R H hR g hg hi⟩
  simpa only [Name.smul_check] using (S.eq_symmetry g r y (Name.check i.val)).mp he

/-- Every family of regular occurrences covering a set and with at most one
value at each index supplies an internal injection into the ground index set. -/
theorem exists_injection (Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hY : ∀ g ∈ H, g • Y = Y)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (p : P)
    (hcover : ∀ x q, q ≤ p → S.atomic.MemF q x Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i, (R i).holds s x)
    (hone : ∀ i q, q ≤ p → ∀ x y, (R i).holds q x → (R i).holds q y → S.atomic.EqF q x y) :
    ∃ f : S.Name, S.Forces ![f,Y,Name.check X] p (SetLanguage.injection 0 1 2) := by
  refine ⟨(relation X R).graph Y (Name.check X) H hH hY (fun g _ => Name.smul_check S g X)
    (relation_move X R H hR),?_⟩
  apply BinaryRelation.graph_injection
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,i,hi⟩ := dense X R x q (hcover x q hq hx) r hrq
    exact ⟨s,hsr,Name.check i.val,S.check_mem_of_mem i.property s,
      fun t hts => ⟨t,le_rfl,i,S.atomic.eq_refl t _,mono X R hts hi⟩⟩
  · intro q _ x y z
    exact relation_one X R
  · exact relation_inj X R p hone

end LeastOccurrence
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Dense presentation of a wellorderability witness by a ground ordinal. -/
theorem wellorderable_check_dense (X : S.Name) (p : P)
    (h : S.Forces ![X] p (SetLanguage.wellorderable 0)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u}, ∃ J : S.Name,
      S.Forces ![J,X,Name.check β.toZFSet] r (SetLanguage.injection 0 1 2) := by
  intro q hq
  obtain ⟨r,hrq,η,ho,hj⟩ := (S.forces_wellorderable _ _ _).mp h q hq
  obtain ⟨s,hsr,β,he⟩ := S.forces_ordinal_decide ![η] r 0 ho r le_rfl
  obtain ⟨t,hts,J,hJ⟩ := hj s hsr
  refine ⟨t,hts.trans (hsr.trans hrq),β,J,?_⟩
  apply (S.atomic.forceFormula_tuple_congr (p := t) (φ := SetLanguage.injection 0 1 2)
    (v := ![J,X,η]) (w := ![J,X,Name.check β.toZFSet]) ?_).mp hJ
  intro k
  fin_cases k
  · exact S.atomic.eq_refl t J
  · exact S.atomic.eq_refl t X
  · exact S.atomic.eq_mono hts he

/-- The value of a function at the (at most one) point of a given ordinal
index in an injection of its domain. -/
def indexedImage (f J X Y : S.Name) (Ξ : ZFSet.{u}) (i : Ξ) : S.UnaryRelation where
  holds p y := ((S.boundedApp J X (Name.check Ξ)).inverse.comp
    (S.boundedApp f X Y)).holds p (Name.check i.val) y
  mono := BinaryRelation.mono _
  regular := BinaryRelation.regular _
  congr hx := BinaryRelation.congr _ (S.atomic.eq_refl _ _) hx

theorem indexedImage_move (f J X Y : S.Name) (Ξ : ZFSet.{u}) (g : Γ)
    (hf : g • f = f) (hJ : g • J = J) (hX : g • X = X) (hY : g • Y = Y)
    (i : Ξ) (p : P) (y : S.Name) (h : (S.indexedImage f J X Y Ξ i).holds p y) :
    (S.indexedImage f J X Y Ξ i).holds (S.move g p) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,x,hx,hy⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • x,?_,
    S.boundedApp_move f X Y g hf hX hY r x y hy⟩
  change (S.boundedApp J X (Name.check Ξ)).holds (S.move g r) (g • x) (Name.check i.val)
  simpa only [Name.smul_check] using
    S.boundedApp_move J X (Name.check Ξ) g hJ hX (Name.smul_check S g Ξ) r x (Name.check i.val) hx

theorem indexedImage_one (f J X Y : S.Name) (Ξ : ZFSet.{u}) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hJ : S.Forces ![J,X,Name.check Ξ] p (SetLanguage.injection 0 1 2)) :
    ∀ i q, q ≤ p → ∀ y z, (S.indexedImage f J X Y Ξ i).holds q y →
      (S.indexedImage f J X Y Ξ i).holds q z → S.atomic.EqF q y z := by
  intro i q hq y z hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := hy r hrq
  obtain ⟨t,hts,a,ha,haz⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have hxa := S.injection_one hJ htp (S.atomic.mem_mono hts hx.1) ha.1
    (S.app_mono hts hx.2.2) ha.2.2
  have hay := (S.app_congr (S.atomic.eq_refl t f) hxa (S.atomic.eq_refl t y)).mp
    (S.app_mono hts hxy.2.2)
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp ha.1 hay haz.2.2⟩

theorem indexedImage_cover (f J X Y : S.Name) (Ξ : ZFSet.{u}) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hJ : S.Forces ![J,X,Name.check Ξ] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ y q, q ≤ p → S.atomic.MemF q y Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i, (S.indexedImage f J X Y Ξ i).holds s y := by
  intro y q hq hy r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
  obtain ⟨t,hts,j,hj,hxj⟩ := S.mapsTo_total hJ (hsr.trans (hrq.trans hq)) hx s le_rfl
  obtain ⟨a,hat,i,hi,hji⟩ := (S.mem_check Ξ j t).mp hj t le_rfl
  refine ⟨a,hat.trans (hts.trans hsr),⟨i,hi⟩,?_⟩
  intro b hba
  have hbs := hba.trans (hat.trans hts)
  refine ⟨b,le_rfl,x,?_,?_⟩
  · exact ⟨S.atomic.mem_mono hbs hx,S.check_mem_of_mem hi b,
      (S.app_congr (S.atomic.eq_refl b J) (S.atomic.eq_refl b x) (S.atomic.eq_mono hba hji)).mp
        (S.app_mono (hba.trans hat) hxj)⟩
  · exact ⟨S.atomic.mem_mono hbs hx,S.atomic.mem_mono (hbs.trans (hsr.trans hrq)) hy,
      S.app_mono hbs hxy⟩

/-- Images of wellorderable sets are wellorderable, by least preimages, not
by a use of Choice. -/
theorem wellorderable_image (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hX : S.Forces ![X] p (SetLanguage.wellorderable 0)) :
    S.Forces ![Y] p (SetLanguage.wellorderable 0) := by
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro q hq
  obtain ⟨r,hrq,β,J,hJ⟩ := S.wellorderable_check_dense X p hX q hq
  let H := S.tupleStabilizer ![f,J,X,Y]
  have hR : ∀ g ∈ H, ∀ i p y, (S.indexedImage f J X Y β.toZFSet i).holds p y →
      (S.indexedImage f J X Y β.toZFSet i).holds (S.move g p) (g • y) := by
    intro g hg
    exact S.indexedImage_move f J X Y β.toZFSet g
      ((S.mem_tupleStabilizer _ g).mp hg 0) ((S.mem_tupleStabilizer _ g).mp hg 1)
      ((S.mem_tupleStabilizer _ g).mp hg 2) ((S.mem_tupleStabilizer _ g).mp hg 3)
  have hfr := S.atomic.forceFormula_mono (hrq.trans hq) hf
  obtain ⟨K,hK⟩ := LeastOccurrence.exists_injection β.toZFSet
    (S.indexedImage f J X Y β.toZFSet) Y H (S.tupleStabilizer_mem _)
      (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 3) hR r
      (S.indexedImage_cover f J X Y β.toZFSet r hfr (S.injection_mapsTo hJ))
      (S.indexedImage_one f J X Y β.toZFSet r (S.surjection_mapsTo hfr) hJ)
  exact ⟨r,hrq,S.wellorderable_of_check_injection Y K β r hK⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## RelationFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w i
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace BinaryRelation
/-- Regular union of an arbitrary indexed family of binary relations. The
bounded graph constructor subsequently makes this relation an actual set. -/
def familyUnion {ι : Sort i} (R : ι → S.BinaryRelation) : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x y
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,i,hi⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x y) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x' y' := by
      intro q hq
      obtain ⟨r,hrq,i,hi⟩ := h q hq
      exact ⟨r,hrq,i,((R i).congr (S.atomic.eq_mono (hrq.trans hq) hx)
        (S.atomic.eq_mono (hrq.trans hq) hy)).mp hi⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

omit [OrderTop P] in
theorem familyUnion_move {ι : Sort i} (R : ι → S.BinaryRelation) (g : Γ)
    (hR : ∀ i p x y, (R i).holds p x y → (R i).holds (S.move g p) (g • x) (g • y))
    (p : P) (x y : S.Name) (h : (familyUnion R).holds p x y) :
    (familyUnion R).holds (S.move g p) (g • x) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,i,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,hR i r x y hi⟩

def atLeft (R : S.BinaryRelation) (x : S.Name) : S.UnaryRelation where
  holds p y := R.holds p x y
  mono := R.mono
  regular := R.regular
  congr h := R.congr (S.atomic.eq_refl _ _) h

def atRight (R : S.BinaryRelation) (y : S.Name) : S.UnaryRelation := R.inverse.atLeft y

end BinaryRelation

namespace UnaryRelation

def member (X : S.Name) : S.UnaryRelation where
  holds p x := S.atomic.MemF p x X
  mono := S.atomic.mem_mono
  regular := S.atomic_regular.2 _ _ _
  congr h := S.atomic.mem_congr h (S.atomic.eq_refl _ _)

def neg (R : S.UnaryRelation) : S.UnaryRelation where
  holds p x := ∀ q, q ≤ p → ¬ R.holds q x
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq hx := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    exact hr r le_rfl (R.mono hrq hx)
  congr := by
    intro p x y he
    have step {x y : S.Name} (he : S.atomic.EqF p x y)
        (h : ∀ q, q ≤ p → ¬ R.holds q x) : ∀ q, q ≤ p → ¬ R.holds q y := by
      intro q hq hy
      exact h q hq ((R.congr (S.atomic.eq_mono hq he)).mpr hy)
    exact ⟨step he,step (S.atomic.eq_symm he)⟩

end UnaryRelation
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedSection -/

namespace PartitionConsistency.SetLanguage
/-- A preimage for the (possibly absent) value at one ordinal index. -/
def indexedSection : Formula 6 :=
  .all ((Formula.mem 6 2).imp ((edge 3 6 4).imp ((Formula.mem 5 1).conj (edge 0 5 6))))
end PartitionConsistency.SetLanguage

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
theorem forces_indexedSection (f X Y J i x : S.Name) (p : P) :
    S.Forces ![f,X,Y,J,i,x] p SetLanguage.indexedSection ↔
      ∀ y q, q ≤ p → S.atomic.MemF q y Y →
        ∀ r, r ≤ q → S.App r J y i → S.atomic.MemF r x X ∧ S.App r f x y := by
  simp only [Forces,SetLanguage.indexedSection,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_conj,S.forces_edge]
  rfl

omit [OrderTop P] in
/-- One fiber can be chosen without any simultaneous use of choice; an
unoccupied ordinal index imposes no requirement on the selected name. -/
theorem indexedSection_exists (f X Y J O i : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hJ : S.Forces ![J,Y,O] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![f,X,Y,J,i] p SetLanguage.indexedSection.ex := by
  intro q hq
  by_cases h : ∃ r, r ≤ q ∧ ∃ y, S.atomic.MemF r y Y ∧ S.App r J y i
  · obtain ⟨r,hrq,y,hy,hyi⟩ := h
    obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf (hrq.trans hq) hy r le_rfl
    refine ⟨s,hsr.trans hrq,x,?_⟩
    have hv : Fin.snoc ![f,X,Y,J,i] x = ![f,X,Y,J,i,x] := by
      ext k
      fin_cases k <;> rfl
    rw [hv]
    apply (S.forces_indexedSection _ _ _ _ _ _ _).mpr
    intro z t hts hz a hat hzi
    have hay := S.atomic.mem_mono (hat.trans (hts.trans hsr)) hy
    have haz := S.atomic.mem_mono hat hz
    have hzy := S.injection_one hJ (hat.trans (hts.trans (hsr.trans (hrq.trans hq)))) haz hay hzi
      (S.app_mono (hat.trans (hts.trans hsr)) hyi)
    exact ⟨S.atomic.mem_mono (hat.trans hts) hx,
      (S.app_congr (S.atomic.eq_refl a f) (S.atomic.eq_refl a x) hzy).mpr
        (S.app_mono (hat.trans hts) hxy)⟩
  · refine ⟨q,le_rfl,Name.empty,?_⟩
    have hv : Fin.snoc ![f,X,Y,J,i] (Name.empty : S.Name) = ![f,X,Y,J,i,Name.empty] := by
      ext k
      fin_cases k <;> rfl
    rw [hv]
    apply (S.forces_indexedSection _ _ _ _ _ _ _).mpr
    intro y r hrq hy s hsr hji
    exact (h ⟨s,hsr.trans hrq,y,S.atomic.mem_mono hsr hy,hji⟩).elim

def sectionPart (J Y i x : S.Name) : S.BinaryRelation where
  holds p y z := S.atomic.MemF p y Y ∧ S.App p J y i ∧ S.atomic.EqF p z x
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.app_mono h hh.2.1,S.atomic.eq_mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.1⟩)),(S.appRelation J).regular (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),S.atomic_regular.1 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr hy hz := and_congr (S.atomic.mem_congr hy (S.atomic.eq_refl _ _))
    (and_congr (S.app_congr (S.atomic.eq_refl _ _) hy (S.atomic.eq_refl _ _))
      ⟨fun h => S.atomic.eq_trans (S.atomic.eq_symm hz) h,fun h => S.atomic.eq_trans hz h⟩)

theorem sectionPart_move (J Y i x : S.Name) (g : Γ)
    (hJ : g • J = J) (hY : g • Y = Y) (hi : g • i = i) (hx : g • x = x)
    (p : P) (y z : S.Name) (h : (S.sectionPart J Y i x).holds p y z) :
    (S.sectionPart J Y i x).holds (S.move g p) (g • y) (g • z) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [hY] using (S.mem_symmetry g p y Y).mp h.1
  · simpa only [hJ,hi] using (S.app_symmetry g p J y i).mp h.2.1
  · simpa only [hx] using (S.eq_symmetry g p z x).mp h.2.2

/-- A uniformly supported collection of local preimages gives one internal
injection, including its totality and its absence of extraneous graph entries. -/
theorem section_injection_of_uniform (f X Y J : S.Name) (Ξ : ZFSet.{u}) (c : Ξ → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hX : ∀ g ∈ H, g • X = X)
    (hY : ∀ g ∈ H, g • Y = Y) (hJ : ∀ g ∈ H, g • J = J)
    (hc : ∀ g ∈ H, ∀ i, g • c i = c i) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hj : S.Forces ![J,Y,Name.check Ξ] p (SetLanguage.mapsTo 0 1 2))
    (hs : ∀ i y q, q ≤ p → S.atomic.MemF q y Y → S.App q J y (Name.check i.val) →
      S.atomic.MemF q (c i) X ∧ S.App q f (c i) y) :
    ∃ K : S.Name, S.Forces ![K,Y,X] p (SetLanguage.injection 0 1 2) := by
  let R := BinaryRelation.familyUnion (fun i : Ξ => S.sectionPart J Y (Name.check i.val) (c i))
  have hR : ∀ g ∈ H, ∀ t y z, R.holds t y z → R.holds (S.move g t) (g • y) (g • z) := by
    intro g hg
    exact BinaryRelation.familyUnion_move _ g (fun i => S.sectionPart_move J Y (Name.check i.val)
      (c i) g (hJ g hg) (hY g hg) (Name.smul_check S g i.val) (hc g hg i))
  refine ⟨R.graph Y X H hH hY hX hR,?_⟩
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,i,hi,hyi⟩ := S.mapsTo_total hj hq hy r hrq
    obtain ⟨t,hts,a,ha,hia⟩ := (S.mem_check Ξ i s).mp hi s le_rfl
    have hty := S.atomic.mem_mono (hts.trans (hsr.trans hrq)) hy
    have hyai := (S.app_congr (S.atomic.eq_refl t J) (S.atomic.eq_refl t y) hia).mp
      (S.app_mono hts hyi)
    have hval := hs ⟨a,ha⟩ y t (hts.trans (hsr.trans (hrq.trans hq))) hty hyai
    refine ⟨t,hts.trans hsr,c ⟨a,ha⟩,hval.1,?_⟩
    intro b hbt
    exact ⟨b,le_rfl,⟨a,ha⟩,S.atomic.mem_mono hbt hty,S.app_mono hbt hyai,S.atomic.eq_refl b _⟩
  · intro q hq y x z hx hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hy,hyi,hxi⟩ := hx r hrq
    obtain ⟨t,hts,j,_,hyj,hzj⟩ := hz s (hsr.trans hrq)
    have he := S.mapsTo_unique hj (hts.trans (hsr.trans (hrq.trans hq)))
      (S.atomic.mem_mono hts hy) (S.app_mono hts hyi) hyj
    have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val t).mp he)
    subst j
    exact ⟨t,hts.trans hsr,S.atomic.eq_trans (S.atomic.eq_mono hts hxi) (S.atomic.eq_symm hzj)⟩
  · intro q hq y z x hy hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hys,hyi,hxi⟩ := hy r hrq
    obtain ⟨t,hts,j,hzt,hzj,hxj⟩ := hz s (hsr.trans hrq)
    have htp := hts.trans (hsr.trans (hrq.trans hq))
    have hy' := hs i y t htp (S.atomic.mem_mono hts hys) (S.app_mono hts hyi)
    have hz' := hs j z t htp hzt hzj
    have hxy := (S.app_congr (S.atomic.eq_refl t f) (S.atomic.eq_mono hts hxi)
      (S.atomic.eq_refl t y)).mpr hy'.2
    have hxz := (S.app_congr (S.atomic.eq_refl t f) hxj (S.atomic.eq_refl t z)).mpr hz'.2
    have hxX := (S.atomic.mem_congr hxj (S.atomic.eq_refl t X)).mpr hz'.1
    exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp hxX hxy hxz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- In the concrete system, surjections onto a wellorderable target admit
sections densely. The common support is chosen before any fiber values. -/
theorem wellorderable_target_injection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hY : S.Forces ![Y] p (SetLanguage.wellorderable 0)) :
    ∃ q, q ≤ p ∧ ∃ K : S.Name, S.Forces ![K,Y,X] q (SetLanguage.injection 0 1 2) := by
  obtain ⟨r,hrp,β,J,hJ⟩ := S.wellorderable_check_dense Y p hY p le_rfl
  let H := S.tupleStabilizer ![f,X,Y,J]
  let v : β.toZFSet → Fin 5 → S.Name := fun i => ![f,X,Y,J,Name.check i.val]
  have hv : ∀ g ∈ H, ∀ i k, g • v i k = v i k := by
    intro g hg i k
    fin_cases k
    · exact (S.mem_tupleStabilizer _ g).mp hg 0
    · exact (S.mem_tupleStabilizer _ g).mp hg 1
    · exact (S.mem_tupleStabilizer _ g).mp hg 2
    · exact (S.mem_tupleStabilizer _ g).mp hg 3
    · exact Name.smul_check S g i.val
  obtain ⟨s,hsr,G,hG,c,hc,hchoices⟩ := uniform_maximum_dense SetLanguage.indexedSection v H
    (S.tupleStabilizer_mem _) hv r (fun i => S.indexedSection_exists f X Y J
      (Name.check β.toZFSet) (Name.check i.val) r (S.atomic.forceFormula_mono hrp hf) hJ)
  obtain ⟨K,hK⟩ := S.section_injection_of_uniform f X Y J β.toZFSet c (H ⊓ G)
    (S.normal.2.2.1 _ _ (S.tupleStabilizer_mem _) hG)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 2)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 3)
    (fun g hg => hc g hg.2) s (S.surjection_mapsTo (S.atomic.forceFormula_mono (hsr.trans hrp) hf))
    (S.injection_mapsTo (S.atomic.forceFormula_mono hsr hJ)) (by
      intro i y t hts hy hji
      have hi := hchoices i
      have hv : Fin.snoc (v i) (c i) = ![f,X,Y,J,Name.check i.val,c i] := by
        ext k
        fin_cases k <;> rfl
      rw [hv] at hi
      exact (S.forces_indexedSection _ _ _ _ _ _ _).mp hi y t hts hy t le_rfl hji)
  exact ⟨s,hsr.trans hrp,K,hK⟩

end
end PartitionConsistency.ConcreteSystem

end OAI

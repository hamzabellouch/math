import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.CodeLinks
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricChoice

namespace OAI

/-! ## UniformFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The range of a small ground family all of whose entries have the same
literal support. This is an actual HS name, not an external evaluated set. -/
def uniformRange {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) : S.Name :=
  S.collect f (fun _ _ => True) H hH (fun g hg i _ _ => ⟨i,(hfix g hg i).symm,trivial⟩)

omit [OrderTop P] in
theorem uniformRange_fixed {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (g : Γ) (hg : g ∈ H) :
    g • S.uniformRange f H hH hfix = S.uniformRange f H hH hfix :=
  Subtype.ext (S.collectName_fixed _ _ H
    (fun g hg i _ _ => ⟨i,(hfix g hg i).symm,trivial⟩) g hg)

omit [OrderTop P] in
theorem mem_uniformRange {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (x : S.Name) (p : P) :
    S.atomic.MemF p x (S.uniformRange f H hH hfix) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, S.atomic.EqF r x (f i) := by
  rw [uniformRange,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,_,_,_,he⟩ := h q hqp
    exact ⟨r,hrq,i,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,i,he⟩ := h q hqp
    exact ⟨r,hrq,i,r,trivial,le_rfl,he⟩

omit [OrderTop P] in
theorem uniformRange_mem {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (i : ι) (p : P) : S.atomic.MemF p (f i) (S.uniformRange f H hH hfix) :=
  (S.mem_uniformRange f H hH hfix (f i) p).mpr
    (fun q _ => ⟨q,le_rfl,i,S.atomic.eq_refl q _⟩)

/-- The canonical family graph enumerates exactly the corresponding range.
The witnesses of the surjection formula are internal ordered-pair sets. -/
theorem indexedGraph_surjection (X : ZFSet.{u}) (f : X → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (p : P) :
    S.Forces ![S.indexedGraph X f H hH hfix,Name.check X,S.uniformRange f H hH hfix] p
      (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  constructor
  · rw [S.forces_mapsTo]
    refine ⟨S.indexedGraph_functionOn X f H hH hfix p,?_⟩
    intro x y q _ _ r _ ha
    apply (S.mem_uniformRange f H hH hfix y r).mpr
    intro s hsr
    obtain ⟨t,hts,i,_,hi⟩ := (S.app_indexedGraph X f H hH hfix x y r).mp ha s hsr
    exact ⟨t,hts,i,hi⟩
  · intro y q _ hy r hrq
    obtain ⟨s,hsr,i,hi⟩ := (S.mem_uniformRange f H hH hfix y q).mp hy r hrq
    refine ⟨s,hsr,Name.check i.val,S.check_mem_of_mem i.property s,?_⟩
    exact (S.app_congr (S.atomic.eq_refl s _) (S.atomic.eq_refl s _) hi).mpr
      (S.indexedGraph_app_at X f H hH hfix i s)

omit [OrderTop P] in
/-- The injection sentence, with its full maps-to conjunct retained. -/
theorem forces_injection {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.injection f a b) ↔
      S.Forces ![v f,v a,v b] p (SetLanguage.mapsTo 0 1 2) ∧
      ∀ x y z : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → S.atomic.MemF r y (v a) → ∀ s, s ≤ r →
          S.App s (v f) x z ∧ S.App s (v f) y z → S.atomic.EqF s x y := by
  simp only [Forces,SetLanguage.injection,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_equal,S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1,2] = ![v f,v a,v b] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

/-- A bounded functional relation which is also one-to-one gives an actual
internal injection graph. -/
theorem BinaryRelation.graph_injection (R : S.BinaryRelation)
    (X Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hX : ∀ g ∈ H, g • X = X) (hY : ∀ g ∈ H, g • Y = Y)
    (hR : ∀ g ∈ H, ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))
    (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z)
    (hinj : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x z → R.holds q y z →
      S.atomic.EqF q x y) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨R.graph_mapsTo X Y H hH hX hY hR p htotal hone,?_⟩
  rintro x y z q hqp _ r hrq _ s hsr ⟨hx,hy⟩
  exact hinj s (hsr.trans (hrq.trans hqp)) x y z
    ((R.app_graph X Y H hH hX hY hR x z s).mp hx).2.2
    ((R.app_graph X Y H hH hX hY hR y z s).mp hy).2.2

namespace UniformInverse
variable {S}
variable (X : ZFSet.{u}) (f : X → S.Name)

/-- The index is the least possible index of this value. Negative equality
with every earlier entry is forced, not merely unforced at this condition. -/
def LeastValue (p : P) (x : S.Name) (i : X) : Prop :=
  S.atomic.EqF p x (f i) ∧ ∀ j, WellOrderingRel j i → ∀ q, q ≤ p → ¬ S.atomic.EqF q x (f j)

omit [OrderTop P] in
theorem least_mono {p q : P} {x : S.Name} {i : X}
    (h : q ≤ p) (hi : LeastValue X f p x i) : LeastValue X f q x i :=
  ⟨S.atomic.eq_mono h hi.1,fun j hj r hr => hi.2 j hj r (hr.trans h)⟩

omit [OrderTop P] in
theorem least_congr {p : P} {x y : S.Name} {i : X}
    (he : S.atomic.EqF p x y) : LeastValue X f p x i ↔ LeastValue X f p y i := by
  have step {x y : S.Name} (he : S.atomic.EqF p x y) (h : LeastValue X f p x i) :
      LeastValue X f p y i := by
    refine ⟨S.atomic.eq_trans (S.atomic.eq_symm he) h.1,?_⟩
    intro j hj q hqp hy
    exact h.2 j hj q hqp (S.atomic.eq_trans (S.atomic.eq_mono hqp he) hy)
  exact ⟨step he,step (S.atomic.eq_symm he)⟩

omit [OrderTop P] in
theorem least_unique {p : P} {x : S.Name} {i j : X}
    (hi : LeastValue X f p x i) (hj : LeastValue X f p x j) : i = j := by
  rcases trichotomous_of WellOrderingRel i j with h | h | h
  · exact (hj.2 i h p le_rfl hi.1).elim
  · exact h
  · exact (hi.2 j h p le_rfl hj.1).elim

/-- Regularization of the indexed least-value relation. -/
def Holds (p : P) (x y : S.Name) : Prop :=
  ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
    S.atomic.EqF r y (Name.check i.val) ∧ LeastValue X f r x i

def relation : S.BinaryRelation where
  holds := Holds X f
  mono h hx q hqp := hx q (hqp.trans h)
  regular h q hqp := by
    obtain ⟨r,hrq,hh⟩ := h q hqp
    obtain ⟨s,hsr,hi⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : Holds X f p x y) : Holds X f p x' y' := by
      intro q hqp
      obtain ⟨r,hrq,i,he,hl⟩ := h q hqp
      exact ⟨r,hrq,i,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hqp) hy)) he,
        (least_congr X f (S.atomic.eq_mono (hrq.trans hqp) hx)).mp hl⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

theorem relation_one {p : P} {x y z : S.Name}
    (hy : (relation X f).holds p x y) (hz : (relation X f).holds p x z) :
    S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,hyi,hi⟩ := hy q hqp
  obtain ⟨s,hsr,j,hzj,hj⟩ := hz r (hrq.trans hqp)
  have hij := least_unique X f (least_mono X f hsr hi) hj
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hyi) (S.atomic.eq_symm hzj)⟩

theorem relation_inj {p : P} {x y z : S.Name}
    (hx : (relation X f).holds p x z) (hy : (relation X f).holds p y z) :
    S.atomic.EqF p x y := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,hzi,hi⟩ := hx q hqp
  obtain ⟨s,hsr,j,hzj,hj⟩ := hy r (hrq.trans hqp)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val s).mp
    (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hsr hzi)) hzj))
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hi.1) (S.atomic.eq_symm hj.1)⟩

/-- Least indices are dense below every condition forcing membership in
this range. Minimality is proved using the ground wellorder; no choice
function in the symmetric extension or completeness of a filter is assumed. -/
theorem relation_total (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (x : S.Name) (p : P)
    (hm : S.atomic.MemF p x (S.uniformRange f H hH hfix)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
      S.atomic.MemF r y (Name.check X) ∧ (relation X f).holds r x y := by
  intro q hqp
  have hne : {i : X | ∃ r, r ≤ q ∧ S.atomic.EqF r x (f i)}.Nonempty := by
    obtain ⟨r,hrq,i,he⟩ := (S.mem_uniformRange f H hH hfix x p).mp hm q hqp
    exact ⟨i,r,hrq,he⟩
  obtain ⟨i,⟨r,hrq,hi⟩,hmin⟩ := WellOrderingRel.isWellOrder.wf.has_min _ hne
  have hl : LeastValue X f r x i := by
    refine ⟨hi,?_⟩
    intro j hj s hsr he
    exact hmin j ⟨s,hsr.trans hrq,he⟩ hj
  exact ⟨r,hrq,Name.check i.val,S.check_mem_of_mem i.property r,
    fun s hsr => ⟨s,le_rfl,i,S.atomic.eq_refl s _,least_mono X f hsr hl⟩⟩

omit [OrderTop P] in
/-- The least-value test is covariant under each automorphism fixing all
entries of the family. Its negative conjunct is transported at every stronger
condition by the inverse order isomorphism. -/
theorem least_move (H : Subgroup Γ)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (g : Γ) (hg : g ∈ H)
    {p : P} {x : S.Name} {i : X} (hi : LeastValue X f p x i) :
    LeastValue X f (S.move g p) (g • x) i := by
  refine ⟨?_,?_⟩
  · simpa only [hfix g hg i] using (S.eq_symmetry g p x (f i)).mp hi.1
  · intro j hj q hqp he
    have hq : (S.move g).symm q ≤ p := (S.move g).symm_apply_le.mpr hqp
    apply hi.2 j hj ((S.move g).symm q) hq
    apply (S.eq_symmetry g ((S.move g).symm q) x (f j)).mpr
    simpa only [OrderIso.apply_symm_apply,hfix g hg j] using he

theorem relation_move (H : Subgroup Γ)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (g : Γ) (hg : g ∈ H)
    (p : P) (x y : S.Name) (h : (relation X f).holds p x y) :
    (relation X f).holds (S.move g p) (g • x) (g • y) := by
  intro q hqp
  obtain ⟨r,hrq,i,he,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hqp)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,?_,least_move X f H hfix g hg hi⟩
  simpa only [Name.smul_check] using (S.eq_symmetry g r y (Name.check i.val)).mp he

end UniformInverse

/-- The sequence range admits an internal injection into its ground index
set. This implements the least-occurrence argument with an actual HS graph;
it does not assume that all its values are ground or that equalities of
values can be decided uniformly by a single condition. -/
def uniformRangeInverse (X : ZFSet.{u}) (f : X → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) : S.Name :=
  (UniformInverse.relation X f).graph (S.uniformRange f H hH hfix) (Name.check X)
    H hH (S.uniformRange_fixed f H hH hfix) (fun g _ => Name.smul_check S g X)
    (UniformInverse.relation_move X f H hfix)

theorem uniformRangeInverse_injection (X : ZFSet.{u}) (f : X → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (p : P) :
    S.Forces ![S.uniformRangeInverse X f H hH hfix,S.uniformRange f H hH hfix,Name.check X]
      p (SetLanguage.injection 0 1 2) := by
  apply (UniformInverse.relation X f).graph_injection
  · intro x q _ hx
    exact UniformInverse.relation_total X f H hH hfix x q hx
  · intro q _ x y z
    exact UniformInverse.relation_one X f
  · intro q _ x y z
    exact UniformInverse.relation_inj X f

/-- The same least-index graph restricted to an arbitrary supported set.
The set need not have a literal representative among the indexed entries. -/
def uniformSubsetInverse (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) : S.Name :=
  (UniformInverse.relation X f).graph Y (Name.check X) H hH hY
    (fun g _ => Name.smul_check S g X) (UniformInverse.relation_move X f H hfix)

theorem uniformSubsetInverse_injection (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) (p : P)
    (hsub : S.SubsetF p Y (S.uniformRange f H hH hfix)) :
    S.Forces ![S.uniformSubsetInverse X f Y H hH hfix hY,Y,Name.check X]
      p (SetLanguage.injection 0 1 2) := by
  apply (UniformInverse.relation X f).graph_injection
  · intro x q hqp hx
    exact UniformInverse.relation_total X f H hH hfix x q (hsub x q hqp hx)
  · intro q _ x y z
    exact UniformInverse.relation_one X f
  · intro q _ x y z
    exact UniformInverse.relation_inj X f

/-- If a set cannot be injected into the index set, then densely it has an
element outside this evaluation list. Nonmembership in the list is forced
below the witness condition, rather than just presently undecided. -/
theorem outside_uniformRange (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) (p : P)
    (hno : ∀ q, q ≤ p → ∀ J : S.Name,
      ¬ S.Forces ![J,Y,Name.check X] q (SetLanguage.injection 0 1 2)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, S.atomic.MemF r y Y ∧
      ∀ s, s ≤ r → ¬ S.atomic.MemF s y (S.uniformRange f H hH hfix) := by
  intro q hqp
  have hsub : ¬ S.SubsetF q Y (S.uniformRange f H hH hfix) := by
    intro h
    exact hno q hqp _ (S.uniformSubsetInverse_injection X f Y H hH hfix hY q h)
  change ¬ (∀ y r, r ≤ q → S.atomic.MemF r y Y →
    S.atomic.MemF r y (S.uniformRange f H hH hfix)) at hsub
  push Not at hsub
  obtain ⟨y,r,hrq,hy,hout⟩ := hsub
  have hstrong : ∃ s, s ≤ r ∧ ∀ t, t ≤ s →
      ¬ S.atomic.MemF t y (S.uniformRange f H hH hfix) := by
    by_contra hn
    push Not at hn
    exact hout (S.atomic_regular.2 _ _ _ hn)
  obtain ⟨s,hsr,hs⟩ := hstrong
  exact ⟨s,hsr.trans hrq,y,S.atomic.mem_mono hsr hy,hs⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckOrdinal -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Members of a checked ordinal are locally checked smaller ordinals. -/
theorem mem_checkOrdinal (α : Ordinal.{u}) (x : S.Name) (p : P) :
    S.atomic.MemF p x (Name.check α.toZFSet) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u}, β < α ∧
        S.atomic.EqF r x (Name.check β.toZFSet) := by
  rw [S.mem_check]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,y,hy,he⟩ := h q hqp
    obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
    exact ⟨r,hrq,β,hβ,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,β,hβ,he⟩ := h q hqp
    exact ⟨r,hrq,β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ,he⟩

/-- Transitivity of a ground ordinal survives arbitrary set symmetric
forcing. Quantified members here are all HS names, not just check names. -/
theorem transF_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.TransF p (Name.check α.toZFSet) := by
  intro x y q _ hx hy
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,β,hβ,he⟩ := (S.mem_checkOrdinal α x q).mp hx r hrq
  have hm : S.atomic.MemF s y (Name.check β.toZFSet) :=
    (S.atomic.mem_congr (S.atomic.eq_refl s y) he).mp (S.atomic.mem_mono (hsr.trans hrq) hy)
  obtain ⟨t,hts,γ,hγ,he'⟩ := (S.mem_checkOrdinal β y s).mp hm s le_rfl
  exact ⟨t,hts.trans hsr,(S.atomic.mem_congr he' (S.atomic.eq_refl t _)).mpr
    (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr (hγ.trans hβ)) t)⟩

/-- Each member of a check ordinal is forced to be transitive as well. -/
theorem ordF_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.OrdF p (Name.check α.toZFSet) := by
  refine ⟨S.transF_checkOrdinal α p,?_⟩
  intro x q _ hx y z r hrq hy hz
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,β,_,he⟩ := (S.mem_checkOrdinal α x q).mp hx s (hsr.trans hrq)
  have ht : S.TransF t x := (S.transF_congr he).mpr (S.transF_checkOrdinal β t)
  exact ⟨t,hts,ht y z t le_rfl (S.atomic.mem_mono (hts.trans hsr) hy)
    (S.atomic.mem_mono (hts.trans hsr) hz)⟩

omit [OrderTop P] in
/-- Internal membership well-foundedness follows from the proved name-rank
Foundation argument, and holds for every set of the symmetric model. -/
theorem forces_membershipWellFounded {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.membershipWellFounded a) := by
  simp only [Forces,SetLanguage.membershipWellFounded,
    S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_mem]
  intro x q _ hx r hrq
  obtain ⟨s,hsr,y,hy⟩ := (S.forces_nonempty _ q 1).mp hx.2 r hrq
  obtain ⟨t,hts,z,hz,hmin⟩ := S.minimal_member x y s hy
  refine ⟨t,hts.trans hsr,z,hz,?_⟩
  intro b u hut hbx v hvu hbz
  exact hmin b v (hvu.trans hut) hbz (S.atomic.mem_mono hvu hbx)

/-- An actual checked ordinal satisfies the exact ordinal formula used by
`ACwo`. Neither external well-foundedness of a model nor a weakened proxy
for that formula is used. -/
theorem forces_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.Forces ![Name.check α.toZFSet] p (SetLanguage.ordinal 0) := by
  refine ⟨(S.forces_transitiveSet _ p 0).mpr (S.transF_checkOrdinal α p),?_,
    S.forces_membershipWellFounded _ p 0⟩
  change S.Forces ![Name.check α.toZFSet] p (SetLanguage.membershipLinear 0)
  simp only [Forces,SetLanguage.membershipLinear,
    S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  refine ⟨?_,?_,?_⟩
  · intro x q _ hx r hrq hself
    obtain ⟨s,hsr,β,_,he⟩ := (S.mem_checkOrdinal α x r).mp
      (S.atomic.mem_mono hrq hx) r le_rfl
    have h := (S.atomic.mem_congr he he).mp (S.atomic.mem_mono hsr hself)
    exact ZFSet.mem_irrefl β.toZFSet ((S.mem_check_check _ _ s).mp h)
  · intro x y z q hqp hx r hrq hy s hsr hz t hts hxy
    have ht := (S.ordF_checkOrdinal α p).2 z s (hsr.trans (hrq.trans hqp)) hz
    exact ht y x t hts hxy.2 hxy.1
  · intro x y q _ hx r hrq hy
    apply (S.atomic.forceFormula_disj _ _ _ _).mpr
    intro s hsr
    obtain ⟨t,hts,β,_,hxβ⟩ := (S.mem_checkOrdinal α x q).mp hx s (hsr.trans hrq)
    obtain ⟨u,hut,γ,_,hyγ⟩ := (S.mem_checkOrdinal α y r).mp hy t (hts.trans hsr)
    refine ⟨u,hut.trans hts,?_⟩
    have hxβ := S.atomic.eq_mono hut hxβ
    rcases lt_trichotomy β γ with h | h | h
    · right
      apply (S.atomic.forceFormula_disj _ _ _ _).mpr
      intro v hvu
      exact ⟨v,le_rfl,Or.inl (S.atomic.mem_mono hvu
        ((S.atomic.mem_congr hxβ hyγ).mpr
          (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) u)))⟩
    · left
      change S.atomic.EqF u x y
      subst γ
      exact S.atomic.eq_trans hxβ (S.atomic.eq_symm hyγ)
    · right
      apply (S.atomic.forceFormula_disj _ _ _ _).mpr
      intro v hvu
      exact ⟨v,le_rfl,Or.inr (S.atomic.mem_mono hvu
        ((S.atomic.mem_congr hyγ hxβ).mpr
          (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) u)))⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI

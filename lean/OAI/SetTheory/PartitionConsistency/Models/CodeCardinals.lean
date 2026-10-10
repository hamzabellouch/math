import Mathlib
import OAI.SetTheory.PartitionConsistency.Models.AssignedGraphs

namespace OAI

/-! ## CodeCardinal -/

/-! The upper bound for the actual name for the persistent code order type.
Its possible ordinal values are bounded by literal representation records
and the proved chain condition of the countable Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

namespace LocalWitness
variable {hμ c} {r : Diagram M I} {A : I → (system (M := M) (I := I) (κ := κ) hμ).Name}
variable {τ : LocalName hμ c r} {d e : CohenForcing.Condition I κ}

/-- A stronger principal quotient retains every literal representation
witness. In particular its three ground record entries do not change. -/
def below (w : LocalWitness hμ (principalFilter d) r A τ) (hed : e ≤ d) :
    LocalWitness hμ (principalFilter e) r A τ :=
  { w with mem := (mem_principalFilter _ _).mpr (hed.trans ((mem_principalFilter _ _).mp w.mem)) }

@[simp] theorem record_below (w : LocalWitness hμ (principalFilter d) r A τ) (hed : e ≤ d) :
    (w.below hed).record = w.record := rfl
end LocalWitness

namespace ChainCode
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

/-- Every decided value of the literal ordinal-type name has ground
cardinality at most μ. Neither genericity nor a supply of representatives
is an assumption: the needed records are obtained by density. -/
theorem ordinalType_cardinal_le (hpower : μ ^ Cardinal.aleph0 = μ)
    (hκ : Cardinal.mk κ ≤ μ) (b : M)
    (hb : Cardinal.mk ((Set.range (fun x : M => b*x))ᶜ : Set M) = Cardinal.mk M)
    (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) :
    θ.card ≤ μ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let toIio : θ.ToType ≃ Set.Iio θ := Ordinal.ToType.mk.toEquiv.symm
  let R (e : CohenForcing.Condition I κ) (rec : LocalRecord (M := M) (κ := κ))
      (β : θ.ToType) : Prop :=
    ∃ a : Index hμ c C, ∃ τ : LocalName hμ c v.diagram,
      IsSelected hμ c hcard hsize hmerger hj E hE C a e ∧
      Rooted hμ c C (code hμ c C a) e τ ∧
      S.atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check (toIio β).val.toZFSet) ∧
      ∃ w : LocalWitness hμ (principalFilter e) v.diagram (labelClass hμ c E) τ, w.record = rec
  have total (β : θ.ToType) : ∃ rec e, R e rec β := by
    obtain ⟨e,hed,a,ha,hea⟩ := member_ordinalRank hμ c hcard hsize hmerger hj E hE C d θ hθ (toIio β)
    obtain ⟨τ,hτ,hrooted⟩ := working_rooted hμ c hcard hsize hmerger hj E hE C e (code hμ c C a) ha.1
    obtain ⟨f,hfe,t,⟨m,hm⟩,hs,j,⟨x,rfl⟩,heq⟩ :=
      classRepresentationSet_denseBelow hμ c hsize b hb v.diagram E τ e hτ e le_rfl
    let w : LocalWitness hμ (principalFilter f) v.diagram (labelClass hμ c E) τ :=
      ⟨t,m,hm,x,f,(mem_principalFilter _ _).mpr le_rfl,hs,heq⟩
    refine ⟨w.record,f,a,τ,isSelected_mono hμ c hcard hsize hmerger hj E hE C hfe ha,
      rooted_mono hfe hrooted,?_,w,rfl⟩
    exact S.atomic.eq_mono
      (WithTop.coe_le_coe.mpr (show (f,v.diagram) ≤ (e,v.diagram) from ⟨hfe,le_rfl⟩)) hea
  have single (rec : LocalRecord (M := M) (κ := κ)) (β γ : θ.ToType)
      (p p' : CohenForcing.Condition I κ) (hp : R p rec β) (hp' : R p' rec γ)
      (hcompat : ForcingQuotient.Compatible p p') : β = γ := by
    obtain ⟨a,τ,ha,hta,hea,w,hw⟩ := hp
    obtain ⟨a',σ,ha',htb,heb,w',hw'⟩ := hp'
    obtain ⟨f,hfp,hfp'⟩ := hcompat
    have heq : LocalQuotient.ofName (principalFilter f) τ = LocalQuotient.ofName (principalFilter f) σ :=
      LocalWitness.equal_of_record_eq hsize hmerger
        (by
          intro π hπ j
          rw [labelClass_move,supported_mono hμ ⟨v.index,v.root⟩ E hE π hπ])
        (w.below hfp) (w'.below hfp') (hw.trans hw'.symm)
    have hτσ : S.atomic.EqF ((f,v.diagram) : Poset M I κ) τ.name σ.name :=
      ((localAtomic hμ v.diagram).eqG_principal f _ _).mp
        ((LocalQuotient.ofName_eq (principalFilter f) τ σ).mp heq)
    have hs : Same hμ c C f (code hμ c C a) (code hμ c C a') :=
      (rooted_eq_iff_same hsize hmerger (rooted_mono hfp hta) (rooted_mono hfp' htb)).mp hτσ
    have haa : a = a' := (code hμ c C).injective
      (selected_unique hμ c hcard hsize hmerger hj E hE C
        (isSelected_mono hμ c hcard hsize hmerger hj E hE C hfp ha)
        (isSelected_mono hμ c hcard hsize hmerger hj E hE C hfp' ha') hs)
    subst a'
    have hle : ((f,v.diagram) : Poset M I κ) ≤ ((p,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hfp,le_rfl⟩
    have hle' : ((f,v.diagram) : Poset M I κ) ≤ ((p',v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hfp',le_rfl⟩
    apply toIio.injective
    apply Subtype.ext
    apply Ordinal.toZFSet_injective
    exact (S.eq_check_iff _ _ ((f,v.diagram) : Poset M I κ)).mp
      (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hle hea)) (S.atomic.eq_mono hle' heb))
  have hcc : ChainBound (P := CohenForcing.Condition I κ) μ := by
    intro A hA
    exact CohenForcing.Condition.antichain_cardinal_le hμ hpower A (by
      intro p hp q hq hc
      exact hA p hp q hq (CohenForcing.Condition.compatible_iff.mp hc))
  have hrec : Cardinal.mk (LocalRecord (M := M) (κ := κ)) ≤ μ := by
    change Cardinal.mk (M × M × CohenForcing.Condition M κ) ≤ μ
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact (mul_le_mul' hcard
      ((mul_le_mul' hcard (CohenForcing.Condition.cardinal_le hμ hpower hcard hκ)).trans_eq
        (Cardinal.mul_eq_self hμ))).trans_eq (Cardinal.mul_eq_self hμ)
  calc
    θ.card = Cardinal.mk θ.ToType := (Cardinal.mk_toType θ).symm
    _ ≤ Cardinal.mk (LocalRecord (M := M) (κ := κ)) * μ := hcc.cardinal_le_mul R total single
    _ ≤ μ * μ := mul_le_mul' hrec le_rfl
    _ = μ := Cardinal.mul_eq_self hμ

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## CodeLower -/

/-! The lower bound for the actual persistent-code ordinal. Independent
probe rows give distinct ranks whenever their witnessing conditions are
compatible. The countable Cohen chain bound then gives the cardinal estimate,
without postulating a filter meeting an ambient uncountable family. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hjoin : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable {v : Vertex q} (C : Vertex.Chain v)

omit [Infinite M] [Infinite I] in
/-- Changing a code within its forced equivalence class preserves its
root representative. Equality is reflected along the actual chain arrows. -/
theorem rooted_of_same {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    {τ : LocalName hμ c v.diagram} (ha : Rooted hμ c C a d τ) (hs : Same hμ c C d a b) :
    Rooted hμ c C b d τ := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hs
  refine ⟨max N L,?_⟩
  intro i hi
  have hr : v.diagram ≤ (C.vertex i).diagram := by
    obtain ⟨f⟩ := C.increasing 0 i (Nat.zero_le i)
    simpa only [C.first] using (show (C.vertex 0).diagram ≤ (C.vertex i).diagram from ⟨f.index,f.diagram⟩)
  exact (system hμ).atomic.eq_trans
    ((system hμ).atomic.eq_symm ((system hμ).atomic.eq_mono
      (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hr⟩))
      (hL i ((le_max_right _ _).trans hi)))) (hN i ((le_max_left _ _).trans hi))

/-- For every probe row one can force a selected representative and its
ordinal rank. Equal possible ranks in compatible conditions force two probe
classes equal, contrary to the outside-list assertion and exact intersection. -/
theorem ordinalType_lower_count (e b : M) {K : Type u} [Uncountable K]
    (m : K × K → M) (hmb : ∀ i, m i*b = v.index*e)
    (hm : ∀ i (n : M), n ∣ v.index ∧ n ∣ m i ↔ n ∈ v.ideal.carrier)
    (hinter : ∀ i (n : M), n ∣ v.index → n ∉ v.ideal.carrier →
      ∀ z : M, n ∣ z ∧ m i ∣ z ↔ v.index*e ∣ z)
    (hind : ∀ i j, i ≠ j → ∀ z : M, m i ∣ z ∧ m j ∣ z ↔ v.index*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub e).range, π • E = E)
    (t : Diagram M I) (ht : t.sub b = q.sub e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : Poset M I κ, z ≤ (d₀,t) →
      ¬ (system hμ).atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard (q.sub e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub e).range)
    (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hjoin E
        (supported_mono hμ (q.self_le_sub e) E hE) C) (Name.check θ.toZFSet)) :
    Cardinal.mk K ≤ θ.card * Cardinal.continuum := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let hEq := supported_mono hμ (q.self_le_sub e) E hE
  let toIio : θ.ToType ≃ Set.Iio θ := Ordinal.ToType.mk.toEquiv.symm
  have hp : v.diagram.sub (v.index*e) = q.sub e := by rw [← Diagram.sub_sub,v.root]
  obtain ⟨d',σ,hs,hroot,hσ,hout'⟩ := outsideClass_copies hμ c hcard hsize
    (q.sub e) v.diagram v.index e b hp m hmb E hE t ht d₀ hd₀ j hj hout
  let τ (i : K × K) : LocalName hμ c v.diagram :=
    (σ i).restrict (v.diagram.self_le_sub (m i))
  have hdisj : Pairwise (fun i k : K × K => Disjoint
      ((d' i).support \ (q.sub e).range) ((d' k).support \ (q.sub e).range)) := by
    intro i k hik
    rw [Set.disjoint_left]
    rintro z ⟨hzi,hzp⟩ ⟨hzk,_⟩
    apply hzp
    have hi := v.diagram.range_inter_sub (m i) (m k) (v.index*e) (hind i k hik)
    rw [hp] at hi
    exact hi ▸ ⟨hs i hzi,hs k hzk⟩
  have hits (i : K) : ∃ f, f ≤ d ∧ ∃ k : K, f ≤ d' (i,k) := by
    let D := CohenForcing.Condition.probeDenseSet
      (d₀.restrict (q.sub e).range) (fun k : K => d' (i,k))
    have hD : Dense D := CohenForcing.Condition.probeDenseSet_dense (q.sub e).range
      (d₀.restrict (q.sub e).range) (fun k : K => d' (i,k)) (fun k => hroot (i,k))
      (fun x y hxy => hdisj (fun he => hxy (congrArg Prod.snd he)))
    obtain ⟨f,hfd,hf⟩ := hD d
    rcases hf with hf | hf
    · exact (hf (CohenForcing.Condition.compatible_iff.mpr ⟨f,le_rfl,hfd.trans hd⟩)).elim
    · exact ⟨f,hfd,hf⟩
  have hel (i : K × K) (f : CohenForcing.Condition I κ) :
      S.Forces ![(τ i).name,labelSet hμ c,E] ((f,v.diagram) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) := hσ i _
  have stable (i : K × K) (f : CohenForcing.Condition I κ) (hfi : f ≤ d' i) :
      forcedAvailability hμ c hcard hsize hmerger f v.diagram v.index (τ i) = v.ideal := by
    let F := principalFilter f
    have hi : d' i ∈ F := (mem_principalFilter _ _).mpr hfi
    have hσi : EligibleName hμ c F (v.diagram.sub (m i)) E (σ i) :=
      ⟨f,(mem_principalFilter _ _).mpr le_rfl,hσ i _⟩
    have hh := classFromLocal_profile hμ c hcard hsize hmerger F q v.diagram (q.sub e)
      v.index e (m i) b v.root hp (hmb i) v.ideal (hm i) (hinter i) E hEq
      (σ i) hσi (d' i) hi (hout' i)
    rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hEq F
      v.diagram v.index v.root] at hh
    exact hh
  let R (f : CohenForcing.Condition I κ) (β : θ.ToType) (i : K) : Prop :=
    ∃ k : K, f ≤ d' (i,k) ∧ ∃ a : Index hμ c C,
      IsSelected hμ c hcard hsize hmerger hjoin E hEq C a f ∧
      Rooted hμ c C (code hμ c C a) f (τ (i,k)) ∧
      S.atomic.EqF ((f,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hjoin E hEq C a) (Name.check (toIio β).val.toZFSet)
  have total (i : K) : ∃ β f, R f β i := by
    obtain ⟨f,hfd,k,hfk⟩ := hits i
    obtain ⟨a,ha,hτa⟩ := exists_working_code_of_stable hμ c hcard hsize hmerger E hEq hjoin C f
      (τ (i,k)) (hel (i,k) f) (fun g hgf => stable (i,k) g (hgf.trans hfk))
    obtain ⟨g,hgf,a',ha',hsame⟩ := dense_selected hμ c hcard hsize hmerger hjoin E hEq C f a ha
    let smallA : Index hμ c C := (code hμ c C).symm a'
    have hsmallA : IsSelected hμ c hcard hsize hmerger hjoin E hEq C smallA g := by
      simpa only [IsSelected,smallA,Equiv.apply_symm_apply] using ha'
    have hgθ : S.atomic.EqF ((g,v.diagram) : Poset M I κ)
        (ordinalType hμ c hcard hsize hmerger hjoin E hEq C) (Name.check θ.toZFSet) :=
      S.atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (g,v.diagram) ≤ (d,v.diagram) from ⟨hgf.trans hfd,le_rfl⟩)) hθ
    obtain ⟨z,hzg,β,hzβ⟩ := ordinalRank_decide hμ c hcard hsize hmerger hjoin E hEq C
      smallA g hsmallA θ hgθ
    refine ⟨toIio.symm β,z,k,(hzg.trans hgf).trans hfk,smallA,
      isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzg hsmallA,?_,?_⟩
    · have har : Rooted hμ c C a f (τ (i,k)) := ⟨0,fun n _ => hτa n⟩
      have hbr := rooted_of_same hμ c C (rooted_mono hgf har) hsame
      simpa only [smallA,Equiv.apply_symm_apply] using rooted_mono hzg hbr
    · simpa only [Equiv.apply_symm_apply] using hzβ
  have single (β : θ.ToType) (i i' : K) (f g : CohenForcing.Condition I κ)
      (hf : R f β i) (hg : R g β i') (hfg : ForcingQuotient.Compatible f g) : i = i' := by
    obtain ⟨k,hfk,a,ha,hτa,heβ⟩ := hf
    obtain ⟨k',hgk,a',ha',hτb,heβ'⟩ := hg
    obtain ⟨z,hzf,hzg⟩ := hfg
    have hle : ((z,v.diagram) : Poset M I κ) ≤ ((f,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hzf,le_rfl⟩
    have hle' : ((z,v.diagram) : Poset M I κ) ≤ ((g,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hzg,le_rfl⟩
    have hab : a = a' := (ordinalRank_eq_iff hμ c hcard hsize hmerger hjoin E hEq C a a' z
      (isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzf ha)
      (isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzg ha')).mp
        (S.atomic.eq_trans (S.atomic.eq_mono hle heβ) (S.atomic.eq_symm (S.atomic.eq_mono hle' heβ')))
    subst a'
    have heq : S.atomic.EqF ((z,v.diagram) : Poset M I κ) (τ (i,k)).name (τ (i',k')).name :=
      (rooted_eq_iff_same hsize hmerger (rooted_mono hzf hτa) (rooted_mono hzg hτb)).mpr
        (same_refl z _)
    by_contra hii
    have hneq : (i,k) ≠ (i',k') := fun h => hii (congrArg Prod.fst h)
    have hip (l : K × K) : v.diagram.sub (m l) ≤ q.sub e :=
      ⟨b,by rw [Diagram.sub_sub,hmb l,hp]⟩
    have hi : (v.diagram.sub (m (i,k))).range ∩ (v.diagram.sub (m (i',k'))).range = (q.sub e).range := by
      rw [← hp]
      exact v.diagram.range_inter_sub _ _ _ (hind _ _ hneq)
    apply outsideLocal_not_equal hμ c hcard hsize hmerger (principalFilter z) (q.sub e)
      (v.diagram.sub (m (i,k))) (v.diagram.sub (m (i',k'))) v.diagram
      (hip (i,k)) (hip (i',k')) hi (v.diagram.self_le_sub _) (v.diagram.self_le_sub _)
      (d' (i,k)) ((mem_principalFilter _ _).mpr (hzf.trans hfk)) (σ (i,k)) (hout' (i,k))
      (LocalQuotient.ofName (principalFilter z) (σ (i',k')))
    exact (LocalQuotient.ofName_eq (principalFilter z) (τ (i,k)) (τ (i',k'))).mpr
      (((localAtomic hμ v.diagram).eqG_principal z _ _).mpr heq)
  have hcc : ChainBound (P := CohenForcing.Condition I κ) Cardinal.continuum := by
    intro A hA
    exact CohenForcing.Condition.antichain_continuum A (by
      intro p hp q hq hc
      exact hA p hp q hq (CohenForcing.Condition.compatible_iff.mp hc))
  simpa only [Cardinal.mk_toType] using hcc.cardinal_le_mul R total single

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI

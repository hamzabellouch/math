import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection
import OAI.Topology.ArtinGroups.Complexes.HomMono

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

noncomputable def sourceShift (E:BasedComplex Q (K:=K) I) (n v:ℤ) :
    BasedComplex Q (K:=K) I where
  placement i:=⟨(E.placement i).color,(E.placement i).cochain+n,(E.placement i).internal+v⟩
  differential:=cochainSign (K:=K) n • E.differential
  entries:=projectiveEntries_smul Q _ E.entries
  degree i j:=by
    constructor
    · intro h
      change cochainSign (K:=K) n • E.differential i j=0
      rw [(E.degree i j).1 (by dsimp only at h; omega),smul_zero]
    · change Homogeneous Q (0+((E.placement i).internal+v)-((E.placement j).internal+v))
        (cochainSign (K:=K) n • E.differential i j)
      convert homogeneous_smul Q (E.degree i j).2 _ using 1; omega
  square_zero:=by
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,cochainSign_mul_self,one_smul,E.square_zero]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma sourceShift_pure (E:BasedComplex Q (K:=K) I) (n v:ℤ) {q:ℤ}
    (hE:∀ i,(E.placement i).level=q) :
    ∀ i,((sourceShift Q E n v).placement i).level=q+n+v := by
  intro i
  have hi:=hE i
  dsimp [sourceShift,GeneratorPlacement.level] at hi ⊢
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma sourceShift_cycle (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (n v:ℤ) {f:Matrix I J (Q.Zigzag K)} (hf:f∈homCycles Q E F n v) :
    f∈homCycles Q (sourceShift Q E n v) F 0 0 := by
  refine ⟨⟨hf.1.1,?_⟩,?_⟩
  · intro i j
    constructor
    · intro h
      exact (hf.1.2 i j).1 (by dsimp [sourceShift] at h; omega)
    · change Homogeneous Q (0+((E.placement i).internal+v)-(F.placement j).internal) (f i j)
      convert (hf.1.2 i j).2 using 1; omega
  · have hh:=congrArg (fun M:Matrix I J (Q.Zigzag K)=>cochainSign (K:=K) n • M) hf.2
    rw [smul_zero] at hh
    change cochainSign (K:=K) n • (E.differential*f-cochainSign (K:=K) n • (f*F.differential))=0 at hh
    rw [smul_sub,smul_smul,cochainSign_mul_self,one_smul] at hh
    change cochainSign (K:=K) n • E.differential*f-cochainSign (K:=K) 0 • (f*F.differential)=0
    simpa only [Matrix.smul_mul,cochainSign_zero,one_smul] using hh

omit [Fintype V] [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma derivedMono_postcompose_injective (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L)
    {d q n v:ℤ} (hE:∀ i,(E.placement i).level=d)
    (hF:∀ j,(F.placement j).level=q) (h:n+v=q-d) (f:Map Q F G)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    Function.Injective (postcomposeOnCycles Q E F G f n v) := by
  apply (postcomposeOnCycles Q E F G f n v).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  have he:∀ i,((sourceShift Q E n v).placement i).level=q := by
    intro i
    have hh:=sourceShift_pure Q E n v hE i
    omega
  have hb:=hm (FiniteModel.ofComplex Q (sourceShift Q E n v))
    (classUpperBound_of_representative Q _ (fun i=>(he i).le)) g.val
    (sourceShift_cycle Q E F n v g.property)
  change g.val*f.matrix∈homBoundaries Q (sourceShift Q E n v) G 0 0 →
    g.val∈homBoundaries Q (sourceShift Q E n v) F 0 0 at hb
  have hp:g.val*f.matrix=0 := by
    have hh:=congrArg Subtype.val hg
    exact hh
  have hz:=hb (by rw [hp]; exact Submodule.zero_mem _)
  rw [pure_coefficient_boundaries_zero Q (sourceShift Q E n v) F he hF (by omega)] at hz
  apply Subtype.ext
  exact hz

omit [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma derivedMono_coefficient_homDimension_mono (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L)
    {d q n v:ℤ} (hE:∀ i,(E.placement i).level=d)
    (hF:∀ j,(F.placement j).level=q) (hG:∀ j,(G.placement j).level=q)
    (h:n+v=q-d) (f:Map Q F G)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    homDimension Q E F n v≤homDimension Q E G n v := by
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF h).finrank_eq,
    (pureCoefficientCohomology Q E G hE hG h).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (derivedMono_postcompose_injective Q E F G hE hF h f hm)

omit [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma derivedMono_total_coefficient_mono (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (G:BasedComplex Q (K:=K) L)
    {d q:ℤ} (hE:∀ i,(E.placement i).level=d)
    (hF:∀ j,(F.placement j).level=q) (hG:∀ j,(G.placement j).level=q)
    (f:Map Q F G)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f) :
    totalHomDimension Q E F (q-d)≤totalHomDimension Q E G (q-d) := by
  let D:=homInternalSupport Q E F ∪ homInternalSupport Q E G
  rw [totalHomDimension_eq_sum_of_subset Q E F (q-d) D Finset.subset_union_left,
    totalHomDimension_eq_sum_of_subset Q E G (q-d) D Finset.subset_union_right]
  exact Finset.sum_le_sum fun v _=>
    derivedMono_coefficient_homDimension_mono Q E F G hE hF hG (by omega) f hm

omit [DecidableEq I] [DecidableEq J] in
lemma derivedSubobject_cartan_inequality (M:BasedComplex Q (K:=K) J)
    (S:BasedComplex Q (K:=K) I) (Y:BasedComplex Q (K:=K) L)
    {q d:ℤ} (hM:∀ i,(M.placement i).level=q)
    (hS:∀ i,(S.placement i).level=q) (hY:∀ i,(Y.placement i).level=d)
    (f:Map Q S M)
    (hm:∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
      HomMonoFrom Q T.complex f)
    (active:Set V) (hsS:∀ i,(S.placement i).color∈active)
    (hsY:∀ α∈active,∀ c,coefficientSocle Q Y α c=⊥)
    (hmid:totalHomDimension Q M Y (d-q+1)=0) :
    (totalHomDimension Q M Y (d-q):ℝ)≤
      (generatorVector Q M-generatorVector Q S) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q Y)) := by
  rw [sub_dotProduct,pure_cartan_euler Q M Y hM hY,pure_cartan_euler Q S Y hS hY]
  have hz:=pure_total_coefficient_homDimension_zero_of_socle_zero Q S Y hS hY active hsS hsY
  have hi:=derivedMono_total_coefficient_mono Q Y S M hY hS hM f hm
  have hi':(totalHomDimension Q Y S (q-d):ℝ)≤totalHomDimension Q Y M (q-d):=by exact_mod_cast hi
  have hn:(0:ℝ)≤totalHomDimension Q S Y (d-q+1):=Nat.cast_nonneg _
  rw [hmid,hz,Nat.cast_zero]
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI

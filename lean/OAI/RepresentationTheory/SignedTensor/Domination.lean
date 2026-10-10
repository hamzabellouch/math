import Mathlib
import OAI.RepresentationTheory.SignedTensor.Basic
import OAI.RepresentationTheory.Tensor.Postselection
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.SignedTensor
open PositiveTensor

/- Partial-trace invariance of the actual regrouping signs on each fixed
exception sector. No assumption of complex conditional probabilities occurs. -/
theorem partialTrace_regroup {p l : ℕ} (E : Finset (Fin l))
    (v : Word p l × Word p l → ℂ)
    (hv : ∀ u w, v (u,w) ≠ 0 → ∀ i,
      (odd (u i) ↔ ¬ odd (w i)) ↔ i ∈ E) :
    partialTrace (PositiveTensor.outer (fun uw => regroupPhase uw.1 uw.2 * v uw)) =
      partialTrace (PositiveTensor.outer v) := by
  ext u u'
  apply Finset.sum_congr rfl
  intro w _
  change (regroupPhase u w * v (u,w)) * star (regroupPhase u' w * v (u',w)) =
    v (u,w)*star (v (u',w))
  by_cases hu : v (u,w) = 0
  · simp [hu]
  by_cases hu' : v (u',w) = 0
  · simp [hu']
  have he : regroupPhase u w = regroupPhase u' w := by
    apply regroupPhase_of_same_parity
    intro i
    have hi := hv u w hu i
    have hi' := hv u' w hu' i
    tauto
  rw [star_mul,regroupPhase_star,he]
  calc
    _ = (regroupPhase u' w * regroupPhase u' w) * (v (u,w)*star (v (u',w))) := by ring
    _ = _ := by rw [regroupPhase_square,one_mul]

abbrev Pair (p : ℕ) := Letter p × Letter p
abbrev MatchedPair (p : ℕ) := {a : Pair p // odd a.1 ↔ odd a.2}

/- Valid pinned exceptional data. Injectivity is essential: it is supplied
by the proved repeated-mismatch cancellation, not imposed on the kernel. -/
structure ExceptionPattern (p l : ℕ) where
  sites : Finset (Fin l)
  pair : sites → Pair p
  mismatch : ∀ i, odd (pair i).1 ↔ ¬ odd (pair i).2
  injective : Function.Injective pair
  deriving Fintype

/- Every nonzero commuting matrix entry has literal valid exceptional data. -/
def entryPattern {p l : ℕ} (A : commutant p l) (u w : Word p l) (h : A.val u w ≠ 0) :
    ExceptionPattern p l where
  sites := mismatchSlots u w
  pair i := (u i.val,w i.val)
  mismatch i := (Finset.mem_filter.mp i.property).2
  injective := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    exact h (commutant_entry_zero_repeated_mismatch A u w i.val j.val hij
      (congrArg Prod.fst he) (congrArg Prod.snd he) (Finset.mem_filter.mp i.property).2)

namespace ExceptionPattern
variable {p l : ℕ}

def encode (F : ExceptionPattern p l) (a : Pair p) : Option (Fin l) :=
  if h : ∃ i : F.sites, F.pair i = a then some (Classical.choose h).val else none

lemma encode_eq_some (F : ExceptionPattern p l) (a : Pair p) (i : Fin l) :
    F.encode a = some i ↔ ∃ hi : i ∈ F.sites, F.pair ⟨i,hi⟩ = a := by
  unfold encode
  split_ifs with h
  · constructor
    · intro he
      have hi := Option.some.inj he
      subst i
      exact ⟨(Classical.choose h).property, Classical.choose_spec h⟩
    · rintro ⟨hi,he⟩
      have hh : Classical.choose h = ⟨i,hi⟩ := F.injective ((Classical.choose_spec h).trans he.symm)
      rw [hh]
  · constructor
    · intro he; cases he
    · rintro ⟨hi,he⟩
      exact (h ⟨⟨i,hi⟩,he⟩).elim

lemma mem_sites_iff (F : ExceptionPattern p l) (i : Fin l) :
    i ∈ F.sites ↔ ∃ a, F.encode a = some i := by
  constructor
  · intro hi
    exact ⟨F.pair ⟨i,hi⟩,(F.encode_eq_some _ i).mpr ⟨hi,rfl⟩⟩
  · rintro ⟨a,ha⟩
    exact ((F.encode_eq_some a i).mp ha).choose

lemma encode_injective : Function.Injective (encode (p := p) (l := l)) := by
  intro F G he
  have hs : F.sites = G.sites := by
    ext i
    rw [F.mem_sites_iff,G.mem_sites_iff]
    simp only [he]
  cases F with | mk E f hf hfi =>
    cases G with | mk E' g hg hgi =>
      dsimp at hs
      subst E'
      have hp : f = g := by
        funext i
        have hh : (ExceptionPattern.mk E f hf hfi).encode (f i) = some i.val :=
          ((ExceptionPattern.mk E f hf hfi).encode_eq_some _ _).mpr ⟨i.property,rfl⟩
        rw [congrFun he (f i)] at hh
        obtain ⟨hi,hv⟩ := ((ExceptionPattern.mk E g hg hgi).encode_eq_some _ _).mp hh
        exact hv.symm
      subst g
      rfl

lemma card_le : Fintype.card (ExceptionPattern p l) ≤ (l+1)^((2*p)*(2*p)) := by
  have hc := Fintype.card_le_of_injective (encode (p := p) (l := l)) encode_injective
  simpa only [Fintype.card_fun,Fintype.card_option,Fintype.card_fin,
    Fintype.card_prod] using hc

lemma sites_card_le (F : ExceptionPattern p l) : F.sites.card ≤ (2*p)*(2*p) := by
  have hc := Fintype.card_le_of_injective F.pair F.injective
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using hc

/- Slots not occupied by a pinned exceptional symbol. -/
abbrev Free (F : ExceptionPattern p l) := {i : Fin l // i ∉ F.sites}
abbrev FreeWord (F : ExceptionPattern p l) := F.Free → MatchedPair p

def fillPair (F : ExceptionPattern p l) (x : F.FreeWord) (i : Fin l) : Pair p :=
  if hi : i ∈ F.sites then F.pair ⟨i,hi⟩ else (x ⟨i,hi⟩).val

def fill (F : ExceptionPattern p l) (x : F.FreeWord) : Word p l × Word p l :=
  (fun i => (F.fillPair x i).1, fun i => (F.fillPair x i).2)

lemma fillPair_at_pin (F : ExceptionPattern p l) (x : F.FreeWord) (i : F.sites) :
    F.fillPair x i.val = F.pair i := by simp [fillPair,i.property]

lemma fillPair_at_free (F : ExceptionPattern p l) (x : F.FreeWord) (i : F.Free) :
    F.fillPair x i.val = (x i).val := by simp [fillPair,i.property]

lemma fill_mismatch_iff (F : ExceptionPattern p l) (x : F.FreeWord) (i : Fin l) :
    (odd ((F.fill x).1 i) ↔ ¬ odd ((F.fill x).2 i)) ↔ i ∈ F.sites := by
  change (odd (F.fillPair x i).1 ↔ ¬ odd (F.fillPair x i).2) ↔ _
  by_cases hi : i ∈ F.sites
  · rw [show F.fillPair x i = F.pair ⟨i,hi⟩ from F.fillPair_at_pin x ⟨i,hi⟩]
    exact iff_of_true (F.mismatch ⟨i,hi⟩) hi
  · rw [show F.fillPair x i = (x ⟨i,hi⟩).val from F.fillPair_at_free x ⟨i,hi⟩]
    have hm := (x ⟨i,hi⟩).property
    tauto

lemma fill_injective (F : ExceptionPattern p l) : Function.Injective F.fill := by
  intro x y he
  funext i
  apply Subtype.ext
  have hh : F.fillPair x i.val = F.fillPair y i.val :=
    Prod.ext (congrFun (congrArg Prod.fst he) i.val) (congrFun (congrArg Prod.snd he) i.val)
  simpa only [F.fillPair_at_free] using hh

lemma fill_disjoint {F G : ExceptionPattern p l} (x : F.FreeWord) (y : G.FreeWord)
    (he : F.fill x = G.fill y) : F = G := by
  have hs : F.sites = G.sites := by
    ext i
    rw [← F.fill_mismatch_iff x i,← G.fill_mismatch_iff y i,he]
  cases F with | mk E f hf hfi =>
    cases G with | mk E' g hg hgi =>
      dsimp at hs
      subst E'
      have hp : f = g := by
        funext i
        have hh : (ExceptionPattern.mk E f hf hfi).fillPair x i.val =
            (ExceptionPattern.mk E g hg hgi).fillPair y i.val :=
          Prod.ext (congrFun (congrArg Prod.fst he) i.val) (congrFun (congrArg Prod.snd he) i.val)
        simpa only [fillPair_at_pin] using hh
      subst g
      rfl

lemma entry_in_range (A : commutant p l) (u w : Word p l) (h : A.val u w ≠ 0) :
    ∃ x : (entryPattern A u w h).FreeWord, (entryPattern A u w h).fill x = (u,w) := by
  let F := entryPattern A u w h
  let x : F.FreeWord := fun i => ⟨(u i.val,w i.val),by
    have hi : i.val ∉ mismatchSlots u w := i.property
    have hm : ¬ (odd (u i.val) ↔ ¬ odd (w i.val)) := by
      simpa only [mismatchSlots,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    tauto⟩
  refine ⟨x,?_⟩
  have he (i : Fin l) : F.fillPair x i = (u i,w i) := by
    unfold fillPair
    split_ifs <;> rfl
  exact Prod.ext (funext fun i => congrArg Prod.fst (he i))
    (funext fun i => congrArg Prod.snd (he i))

/- Extend a permutation of the free slots by the identity on the exceptions. -/
def extendPerm (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) : Equiv.Perm (Fin l) :=
  Equiv.Perm.ofSubtype σ

lemma extendPerm_pin (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (i : F.sites) :
    F.extendPerm σ i.val = i.val := by
  simp [extendPerm,Equiv.Perm.ofSubtype_apply_of_not_mem,i.property]

lemma extendPerm_free (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (i : F.Free) :
    F.extendPerm σ i.val = (σ i).val := by
  exact Equiv.Perm.ofSubtype_apply_of_mem σ i.property

lemma fill_transport (F : ExceptionPattern p l) (σ : Equiv.Perm F.Free) (x : F.FreeWord) :
    F.fill (fun i => x (σ⁻¹ i)) =
      (wordPerm (F.extendPerm σ) (F.fill x).1, wordPerm (F.extendPerm σ) (F.fill x).2) := by
  have hinv : (F.extendPerm σ)⁻¹ = F.extendPerm σ⁻¹ := by
    simp only [extendPerm,map_inv]
  have he (i : Fin l) : F.fillPair (fun i => x (σ⁻¹ i)) i =
      F.fillPair x ((F.extendPerm σ)⁻¹ i) := by
    rw [hinv]
    by_cases hi : i ∈ F.sites
    · rw [show F.extendPerm σ⁻¹ i = i from F.extendPerm_pin σ⁻¹ ⟨i,hi⟩]
      simp [fillPair,hi]
    · rw [show F.extendPerm σ⁻¹ i = (σ⁻¹ ⟨i,hi⟩).val from F.extendPerm_free σ⁻¹ ⟨i,hi⟩]
      rw [show F.fillPair (fun i => x (σ⁻¹ i)) i = (x (σ⁻¹ ⟨i,hi⟩)).val from
        F.fillPair_at_free (fun i => x (σ⁻¹ i)) ⟨i,hi⟩,F.fillPair_at_free]
  exact Prod.ext (funext fun i => congrArg Prod.fst (he i))
    (funext fun i => congrArg Prod.snd (he i))

def purified (F : ExceptionPattern p l) (A : commutant p l) (x : F.FreeWord) : ℂ :=
  regroupPhase (F.fill x).1 (F.fill x).2 * A.val (F.fill x).1 (F.fill x).2

lemma purified_invariant (F : ExceptionPattern p l) (A : commutant p l)
    (σ : Equiv.Perm F.Free) (x : F.FreeWord) :
    F.purified A (fun i => x (σ⁻¹ i)) = F.purified A x := by
  unfold purified
  rw [F.fill_transport]
  apply regrouped_commutant_invariant
  intro i hi
  exact F.extendPerm_pin σ ⟨i,(F.fill_mismatch_iff x i).mp hi⟩

end ExceptionPattern
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

def embedding (F : ExceptionPattern p l) : F.FreeWord ↪ (Word p l × Word p l) :=
  ⟨F.fill,F.fill_injective⟩

def component (F : ExceptionPattern p l) (A : commutant p l) (uw : Word p l × Word p l) : ℂ :=
  if uw ∈ Set.range F.fill then A.val uw.1 uw.2 else 0

lemma component_image (F : ExceptionPattern p l) (A : commutant p l) (x : F.FreeWord) :
    F.component A (F.fill x) = A.val (F.fill x).1 (F.fill x).2 := by
  simp [component]

lemma component_inclusion (F : ExceptionPattern p l) (A : commutant p l) :
    F.component A = (inclusion F.embedding).mulVec (fun x => A.val (F.fill x).1 (F.fill x).2) := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (fun x => A.val (F.fill x).1 (F.fill x).2) x
    change (inclusion F.embedding).mulVec (fun x => A.val (F.fill x).1 (F.fill x).2) (F.fill x) = _ at hh
    exact (F.component_image A x).trans hh.symm
  · rw [show F.component A q = 0 from ite_eq_right hq]
    exact (inclusion_mulVec_notin F.embedding _ q hq).symm

lemma purified_inclusion (F : ExceptionPattern p l) (A : commutant p l) :
    (inclusion F.embedding).mulVec (F.purified A) =
      fun q => regroupPhase q.1 q.2 * F.component A q := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (F.purified A) x
    change (inclusion F.embedding).mulVec (F.purified A) (F.fill x) = _ at hh
    rw [hh,F.component_image]
    rfl
  · rw [inclusion_mulVec_notin F.embedding _ q hq]
    simp [component,hq]

lemma component_partialTrace (F : ExceptionPattern p l) (A : commutant p l) :
    partialTrace (PositiveTensor.outer ((inclusion F.embedding).mulVec (F.purified A))) =
      partialTrace (PositiveTensor.outer (F.component A)) := by
  rw [F.purified_inclusion]
  apply partialTrace_regroup F.sites
  intro u w h i
  have hq : (u,w) ∈ Set.range F.fill := by
    by_contra hn
    exact h (ite_eq_right hn)
  obtain ⟨x,hx⟩ := hq
  have he := F.fill_mismatch_iff x i
  simpa only [hx] using he

lemma component_sum (A : commutant p l) :
    ∑ F : ExceptionPattern p l, F.component A = fun q => A.val q.1 q.2 := by
  funext q
  rw [Finset.sum_apply]
  by_cases hq : A.val q.1 q.2 = 0
  · simp [component,hq]
  · let F := entryPattern A q.1 q.2 hq
    obtain ⟨x,hx⟩ := entry_in_range A q.1 q.2 hq
    have hmem : q ∈ Set.range F.fill := ⟨x,hx⟩
    rw [Finset.sum_eq_single F]
    · exact ite_eq_left hmem
    · intro G _ hG
      apply ite_eq_right
      rintro ⟨y,hy⟩
      exact hG (fill_disjoint y x (hy.trans hx.symm))
    · simp

lemma component_square_sum (A : commutant p l) (q : Word p l × Word p l) :
    ∑ F : ExceptionPattern p l, F.component A q * star (F.component A q) =
      A.val q.1 q.2 * star (A.val q.1 q.2) := by
  by_cases hq : A.val q.1 q.2 = 0
  · simp [component,hq]
  · let F := entryPattern A q.1 q.2 hq
    obtain ⟨x,hx⟩ := entry_in_range A q.1 q.2 hq
    have hmem : q ∈ Set.range F.fill := ⟨x,hx⟩
    rw [Finset.sum_eq_single F]
    · simp [component,hmem]
    · intro G _ hG
      have hn : q ∉ Set.range G.fill := by
        rintro ⟨y,hy⟩
        exact hG (fill_disjoint y x (hy.trans hx.symm))
      simp [component,hn]
    · simp

lemma purified_trace (F : ExceptionPattern p l) (A : commutant p l) :
    Matrix.trace (OrdinaryTensor.outer (F.purified A)) =
      Matrix.trace (PositiveTensor.outer (F.component A)) := by
  rw [show OrdinaryTensor.outer (F.purified A) = Matrix.vecMulVec (F.purified A) (star (F.purified A)) from rfl,
    ← inclusion_trace_outer F.embedding,F.purified_inclusion]
  apply Finset.sum_congr rfl
  intro q _
  change (regroupPhase q.1 q.2 * F.component A q) *
    star (regroupPhase q.1 q.2 * F.component A q) = F.component A q * star (F.component A q)
  rw [star_mul,regroupPhase_star]
  calc
    _ = (regroupPhase q.1 q.2 * regroupPhase q.1 q.2) * (F.component A q * star (F.component A q)) := by ring
    _ = _ := by rw [regroupPhase_square,one_mul]

lemma sum_purified_trace (A : commutant p l) :
    ∑ F : ExceptionPattern p l, Matrix.trace (OrdinaryTensor.outer (F.purified A)) =
      Matrix.trace (A.val*A.val.conjTranspose) := by
  simp_rw [purified_trace]
  simp only [PositiveTensor.outer,Matrix.trace,Matrix.diag_apply,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [Finset.sum_comm]
  simp_rw [component_square_sum]
  simp only [Fintype.sum_prod_type,Matrix.mul_apply,Matrix.conjTranspose_apply]
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}
lemma free_card (F : ExceptionPattern p l) : Fintype.card F.Free = l-F.sites.card := by
  simp only [Free,Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin]
lemma free_card_pos (F : ExceptionPattern p l) (hl : (2*p)*(2*p) < l) : 0 < Fintype.card F.Free := by
  rw [F.free_card]
  exact Nat.sub_pos_of_lt (lt_of_le_of_lt F.sites_card_le hl)
lemma free_card_le (F : ExceptionPattern p l) : Fintype.card F.Free ≤ l := by
  rw [F.free_card]
  exact Nat.sub_le _ _

lemma matchedPair_nonempty (hp : 0 < p) : Nonempty (MatchedPair p) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),Iff.rfl⟩⟩

/- Exact domination of a pinned component by a finite product mixture on its
free slots, after the proved sign cancellation in the genuine partial trace. -/
theorem component_postselection (F : ExceptionPattern p l) (hp : 0 < p)
    (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (OrdinaryTensor.outer (F.purified A)) *
        ((Fintype.card F.Free+1 : ℕ) : ℂ)^(2*Fintype.card (MatchedPair p))) •
      partialTrace (inclusion F.embedding * (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose) -
      partialTrace (PositiveTensor.outer (F.component A))).PosSemidef := by
  let : Nonempty (MatchedPair p) := matchedPair_nonempty hp
  have h := OrdinaryTensor.invariant_vector_postselection (I := F.Free) (A := MatchedPair p) (F.free_card_pos hl)
    (F.purified A) (F.purified_invariant A)
  have hc := h.mul_mul_conjTranspose_same (inclusion F.embedding)
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at hc
  have ho : inclusion F.embedding * OrdinaryTensor.outer (F.purified A) * (inclusion F.embedding).conjTranspose =
      PositiveTensor.outer ((inclusion F.embedding).mulVec (F.purified A)) :=
    mul_outer_mul_star _ _
  rw [ho] at hc
  have hp := partialTrace_posSemidef _ hc
  simpa only [partialTrace_sub,partialTrace_smul,F.component_partialTrace A] using hp
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor

def pairAmplitude {p : ℕ} (z : MatchedPair p → ℂ) : Matrix (Letter p) (Letter p) ℂ :=
  fun a b => if h : odd a ↔ odd b then z ⟨(a,b),h⟩ else 0

lemma pairAmplitude_unit_trace {p : ℕ} (z : MatchedPair p → ℂ)
    (hz : ∑ a, z a * star (z a) = 1) :
    Matrix.trace (pairAmplitude z * (pairAmplitude z).conjTranspose) = 1 := by
  have hs := Fintype.sum_of_injective
    (Subtype.val : MatchedPair p → Pair p) Subtype.val_injective
    (fun a => z a * star (z a))
    (fun a : Pair p => pairAmplitude z a.1 a.2 * star (pairAmplitude z a.1 a.2))
    (by
      intro a ha
      have hn : ¬ (odd a.1 ↔ odd a.2) := by
        intro h
        exact ha ⟨⟨a,h⟩,rfl⟩
      simp [pairAmplitude,hn])
    (by intro a; simp [pairAmplitude,a.property])
  rw [hz] at hs
  simpa only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type] using hs.symm

lemma pairAmplitude_even {p : ℕ} (z : MatchedPair p → ℂ) (a b : Letter p)
    (hab : odd a ↔ ¬ odd b) :
    (pairAmplitude z * (pairAmplitude z).conjTranspose) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hac : odd a ↔ odd c
  · have hbc : ¬ (odd b ↔ odd c) := by tauto
    simp [Matrix.conjTranspose_apply,pairAmplitude,hbc]
  · simp [Matrix.conjTranspose_apply,pairAmplitude,hac]

/- The real even one-site density obtained by the literal auxiliary partial
trace of a unit matched-pair vector. -/
def pairDensity {p : ℕ} (z : MatchedPair p → ℂ) (hz : ∑ a, z a * star (z a) = 1) : EvenDensity p :=
  ⟨pairAmplitude z * (pairAmplitude z).conjTranspose,
    Matrix.posSemidef_self_mul_conjTranspose _, pairAmplitude_unit_trace z hz,
    pairAmplitude_even z⟩
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

def basisDensity (a : Letter p) : Matrix (Letter p) (Letter p) ℂ :=
  Matrix.diagonal (fun b => if b=a then 1 else 0)

lemma basisDensity_posSemidef (a : Letter p) : (basisDensity a).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b=a then _ else _
  split_ifs <;> norm_num

lemma basisDensity_le_one (a : Letter p) : (1-basisDensity a).PosSemidef := by
  have he : (1-basisDensity a) = Matrix.diagonal (fun b => if b=a then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i=a <;> simp [basisDensity,Matrix.diagonal,hi]
    · simp [basisDensity,Matrix.diagonal,hij]

  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro b
  change (0 : ℂ) ≤ if b=a then _ else _
  split_ifs <;> norm_num

lemma basisDensity_trace (a : Letter p) : Matrix.trace (basisDensity a) = 1 := by
  simp [basisDensity,Matrix.trace_diagonal]

def pinAmplitude (a : Pair p) : Matrix (Letter p) (Letter p) ℂ :=
  fun i j => if (i,j)=a then 1 else 0

lemma pinAmplitude_density (a : Pair p) : pinAmplitude a * (pinAmplitude a).conjTranspose = basisDensity a.1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,pinAmplitude]
  rw [Finset.sum_eq_single a.2]
  · by_cases hi : i=a.1 <;> by_cases hj : j=a.1 <;>
      simp [Prod.ext_iff,hi,hj,basisDensity,Matrix.diagonal,eq_comm]
  · intro k _ hk
    simp [Prod.ext_iff,hk]
  · simp

def keep (s : ℕ) : ℝ := s/(s+1)
def noise (s p : ℕ) : ℝ := 1/((s+1)*(2*p))

lemma keep_nonneg (s : ℕ) : 0 ≤ keep s := div_nonneg (Nat.cast_nonneg _) (by positivity)
lemma noise_nonneg (s p : ℕ) : 0 ≤ noise s p := by unfold noise; positivity
lemma keep_add_noise (s p : ℕ) (hp : 0 < p) : keep s + noise s p*(2*p) = 1 := by
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hs : (s : ℝ)+1 ≠ 0 := by positivity
  unfold keep noise
  field_simp

def depolarized (s : ℕ) (r : EvenDensity p) : Matrix (Letter p) (Letter p) ℂ :=
  (keep s : ℂ) • r.val + (noise s p : ℂ) • 1

lemma depolarized_posSemidef (s : ℕ) (r : EvenDensity p) : (depolarized s r).PosSemidef := by
  exact (r.property.1.smul (by exact_mod_cast keep_nonneg s)).add
    (Matrix.PosSemidef.one.smul (by exact_mod_cast noise_nonneg s p))

lemma depolarized_trace (s : ℕ) (hp : 0 < p) (r : EvenDensity p) : Matrix.trace (depolarized s r) = 1 := by
  rw [depolarized,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,r.property.2.1]
  simp only [Matrix.trace_one,Fintype.card_fin,smul_eq_mul,mul_one]
  exact_mod_cast keep_add_noise s p hp

lemma depolarized_even (s : ℕ) (r : EvenDensity p) (i j : Letter p)
    (hij : odd i ↔ ¬ odd j) : depolarized s r i j = 0 := by
  have hne : i ≠ j := by intro h; subst j; tauto
  simp [depolarized,Matrix.smul_apply,r.property.2.2 i j hij,hne]

def depolarizedDensity (s : ℕ) (hp : 0 < p) (r : EvenDensity p) : EvenDensity p :=
  ⟨depolarized s r,depolarized_posSemidef s r,depolarized_trace s hp r,depolarized_even s r⟩

lemma depolarized_free (s : ℕ) (r : EvenDensity p) :
    (depolarized s r - (keep s : ℂ) • r.val).PosSemidef := by
  simpa only [depolarized,add_sub_cancel_left] using
    (Matrix.PosSemidef.one (n := Letter p) (R := ℂ)).smul (by exact_mod_cast noise_nonneg s p)

lemma depolarized_pin (s : ℕ) (r : EvenDensity p) (a : Letter p) :
    (depolarized s r - (noise s p : ℂ) • basisDensity a).PosSemidef := by
  have ht : (0 : ℂ) ≤ (keep s : ℂ) := by exact_mod_cast keep_nonneg s
  have hu : (0 : ℂ) ≤ (noise s p : ℂ) := by exact_mod_cast noise_nonneg s p
  have h := (r.property.1.smul ht).add ((basisDensity_le_one a).smul hu)
  simpa only [depolarized,smul_sub,add_sub_assoc] using h
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

def pinnedDensity (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    Matrix (Word p l) (Word p l) ℂ :=
  productMatrix (fun i => if hi : i ∈ E then basisDensity (a ⟨i,hi⟩) else r.val)

lemma pinnedDensity_posSemidef (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    (pinnedDensity E a r).PosSemidef := by
  apply productMatrix_posSemidef
  intro i
  split_ifs with hi
  · exact basisDensity_posSemidef _
  · exact r.property.1

lemma keep_pow_lower (s n : ℕ) (hn : n ≤ s) : 1 ≤ (s+1 : ℝ) * (keep s)^n := by
  have hs : (0 : ℝ) < s+1 := by positivity
  have hi : (s+1 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hs).mpr (by linarith [Nat.cast_nonneg (α := ℝ) s])
  have hb := one_add_mul_le_pow (a := -((s+1 : ℝ)⁻¹)) (by linarith : -2 ≤ -((s+1 : ℝ)⁻¹)) n
  have he : (1 - (s+1 : ℝ)⁻¹) = keep s := by unfold keep; field_simp; ring
  calc
    1 ≤ (s+1 : ℝ)-n := by
      have hn' : (n : ℝ) ≤ s := by exact_mod_cast hn
      linarith
    _ = (s+1 : ℝ)*(1+n * (-((s+1 : ℝ)⁻¹))) := by field_simp; ring
    _ ≤ (s+1 : ℝ)*(1+(-((s+1 : ℝ)⁻¹)))^n := mul_le_mul_of_nonneg_left hb hs.le
    _ = _ := by rw [show 1+(-((s+1 : ℝ)⁻¹)) = keep s from he]

lemma pin_coefficient_le (s p k : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hk : k ≤ (2*p)*(2*p)) :
    (s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^k ≤ (s+1 : ℝ)^(13*p^2) := by
  have hs : (1 : ℝ) ≤ s+1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  have hp' : (p : ℝ) ≤ s := by exact_mod_cast hps
  have ha : (2*p : ℝ) ≤ (s+1 : ℝ)^2 := by nlinarith [sq_nonneg (s : ℝ)]
  have hbase : (s+1 : ℝ)*(2*p) ≤ (s+1 : ℝ)^3 := by
    nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ s+1)]
  have hexp : 3*k+1 ≤ 13*p^2 := by
    have hp1 : 1 ≤ p*p := by nlinarith
    nlinarith [hk]
  calc
    _ ≤ (s+1 : ℝ) * ((s+1 : ℝ)^3)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
    _ = (s+1 : ℝ)^(3*k+1) := by rw [← pow_mul,pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hs hexp

/- Each pinned ordinary product density is dominated by a tensor power of a
single even density, with only polynomial cost per actual exception. -/
theorem pinned_absorption (s : ℕ) (hp : 0 < p) (hls : l ≤ s)
    (E : Finset (Fin l)) (a : E → Letter p) (r : EvenDensity p) :
    (((s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^E.card : ℝ) : ℂ) •
      densityPower l (depolarized s r) - pinnedDensity E a r |>.PosSemidef := by
  let c : Fin l → ℂ := fun i => if i ∈ E then (noise s p : ℂ) else (keep s : ℂ)
  let f : Fin l → Matrix (Letter p) (Letter p) ℂ :=
    fun i => if hi : i ∈ E then basisDensity (a ⟨i,hi⟩) else r.val
  have hlocal (i : Fin l) : (c i • f i).PosSemidef := by
    by_cases hi : i ∈ E
    · simpa only [c,f,ite_eq_left hi,dite_eq_left hi] using
        (basisDensity_posSemidef (a ⟨i,hi⟩)).smul (show (0 : ℂ) ≤ (noise s p : ℂ) by exact_mod_cast noise_nonneg s p)
    · simpa only [c,f,ite_eq_right hi,dite_eq_right hi] using
        r.property.1.smul (show (0 : ℂ) ≤ (keep s : ℂ) by exact_mod_cast keep_nonneg s)
  have hdiff (i : Fin l) : (depolarized s r - c i • f i).PosSemidef := by
    by_cases hi : i ∈ E
    · simpa only [c,f,ite_eq_left hi,dite_eq_left hi] using depolarized_pin s r (a ⟨i,hi⟩)
    · simpa only [c,f,ite_eq_right hi,dite_eq_right hi] using depolarized_free s r
  have h := productMatrix_mono (fun i => c i • f i) (fun _ => depolarized s r) hlocal hdiff
  rw [productMatrix_smul] at h
  have hc : (∏ i, c i) = ((keep s)^(l-E.card) * (noise s p)^E.card : ℝ) := by
    have hE : Finset.univ.filter (fun i : Fin l => i ∈ E) = E := by ext i; simp
    have hC : Finset.univ.filter (fun i : Fin l => i ∉ E) = Eᶜ := by ext i; simp
    simp only [c,Finset.prod_ite,hE,hC,Finset.prod_const,Finset.card_compl,Fintype.card_fin]
    push_cast
    ring
  rw [hc] at h
  let C : ℝ := (s+1 : ℝ) * ((s+1 : ℝ)*(2*p))^E.card
  have hC : (0 : ℝ) ≤ C := by dsimp [C]; positivity
  have hu : ((s+1 : ℝ)*(2*p))*noise s p = 1 := by
    have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    unfold noise
    field_simp
  have hCW : 1 ≤ C*((keep s)^(l-E.card)*(noise s p)^E.card) := by
    calc
      _ ≤ (s+1 : ℝ)*(keep s)^(l-E.card) := keep_pow_lower s _ (le_trans (Nat.sub_le _ _) hls)
      _ = _ := by
        dsimp [C]
        calc
          _ = ((s+1 : ℝ)*(keep s)^(l-E.card))*((((s+1 : ℝ)*(2*p))*noise s p)^E.card) := by rw [hu,one_pow,mul_one]
          _ = _ := by rw [mul_pow]; ring
  have hh := h.smul (show (0 : ℂ) ≤ (C : ℂ) by exact_mod_cast hC)
  have hz := (pinnedDensity_posSemidef E a r).smul
    (show (0 : ℂ) ≤ ((C*((keep s)^(l-E.card)*(noise s p)^E.card)-1 : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hCW)
  have ht := hh.add hz
  change ((C : ℂ) • (densityPower l (depolarized s r) -
    (((keep s)^(l-E.card)*(noise s p)^E.card : ℝ) : ℂ) • pinnedDensity E a r) +
    ((C*((keep s)^(l-E.card)*(noise s p)^E.card)-1 : ℝ) : ℂ) • pinnedDensity E a r).PosSemidef at ht
  change ((C : ℂ) • densityPower l (depolarized s r) - pinnedDensity E a r).PosSemidef
  convert ht using 1
  simp only [smul_sub,smul_smul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one,
    sub_smul,one_smul]
  module
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}
theorem pinned_absorption_uniform (s : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (E : Finset (Fin l)) (hE : E.card ≤ (2*p)*(2*p)) (a : E → Letter p) (r : EvenDensity p) :
    ((((s+1 : ℝ)^(13*p^2)) : ℂ) • densityPower l (depolarized s r) - pinnedDensity E a r).PosSemidef := by
  have h := pinned_absorption s hp hls E a r
  have hle := pin_coefficient_le s p E.card hp hps hE
  have hr : (densityPower l (depolarized s r)).PosSemidef :=
    productMatrix_posSemidef (fun _ : Fin l => depolarized s r) (fun _ => depolarized_posSemidef s r)
  have hh := (hr.smul (show (0 : ℂ) ≤ (((s+1 : ℝ)^(13*p^2) -
    (s+1 : ℝ)*((s+1 : ℝ)*(2*p))^E.card : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hle)).add h
  convert hh using 1
  push_cast
  module
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

def siteAmplitude (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (i : Fin l) :
    Matrix (Letter p) (Letter p) ℂ :=
  if hi : i ∈ F.sites then pinAmplitude (F.pair ⟨i,hi⟩) else pairAmplitude z

def pairProduct (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (q : Word p l × Word p l) : ℂ := ∏ i, F.siteAmplitude z i (q.1 i) (q.2 i)

lemma siteAmplitude_pin (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) (i : F.sites) :
    F.siteAmplitude z i.val ((F.fill x).1 i.val) ((F.fill x).2 i.val) = 1 := by
  change F.siteAmplitude z i.val (F.fillPair x i.val).1 (F.fillPair x i.val).2 = 1
  rw [F.fillPair_at_pin]
  simp [siteAmplitude,i.property,pinAmplitude]

lemma siteAmplitude_free (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) (i : F.Free) :
    F.siteAmplitude z i.val ((F.fill x).1 i.val) ((F.fill x).2 i.val) = z (x i) := by
  change F.siteAmplitude z i.val (F.fillPair x i.val).1 (F.fillPair x i.val).2 = z (x i)
  rw [F.fillPair_at_free]
  simp [siteAmplitude,i.property,pairAmplitude,(x i).property]

lemma pairProduct_fill (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) (x : F.FreeWord) :
    F.pairProduct z (F.fill x) = OrdinaryTensor.tensorVector z x := by
  unfold pairProduct
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ F.sites)]
  simp only [F.siteAmplitude_pin,F.siteAmplitude_free,Finset.prod_const_one,one_mul]
  rfl

lemma pairProduct_nonzero (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (q : Word p l × Word p l) (hq : F.pairProduct z q ≠ 0) : q ∈ Set.range F.fill := by
  have hi (i : Fin l) : F.siteAmplitude z i (q.1 i) (q.2 i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hq) i (Finset.mem_univ i)
  have hp (i : F.sites) : (q.1 i.val,q.2 i.val) = F.pair i := by
    by_contra hn
    exact hi i.val (by simp [siteAmplitude,i.property,pinAmplitude,hn])
  have hf (i : F.Free) : odd (q.1 i.val) ↔ odd (q.2 i.val) := by
    by_contra hn
    exact hi i.val (by simp [siteAmplitude,i.property,pairAmplitude,hn])
  let x : F.FreeWord := fun i => ⟨(q.1 i.val,q.2 i.val),hf i⟩
  have he (i : Fin l) : F.fillPair x i = (q.1 i,q.2 i) := by
    by_cases hi : i ∈ F.sites
    · exact (F.fillPair_at_pin x ⟨i,hi⟩).trans (hp ⟨i,hi⟩).symm
    · exact F.fillPair_at_free x ⟨i,hi⟩
  exact ⟨x,Prod.ext (funext fun i => congrArg Prod.fst (he i)) (funext fun i => congrArg Prod.snd (he i))⟩

lemma pairProduct_inclusion (F : ExceptionPattern p l) (z : MatchedPair p → ℂ) :
    (inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z) = F.pairProduct z := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (OrdinaryTensor.tensorVector z) x
    change (inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z) (F.fill x) = _ at hh
    exact hh.trans (F.pairProduct_fill z x).symm
  · rw [inclusion_mulVec_notin F.embedding _ q hq]
    exact (not_ne_iff.mp (fun hh => hq (F.pairProduct_nonzero z q hh))).symm

/- Partial tracing a filled product vector yields pinned basis densities at
the true exceptions and the same even density at every remaining slot. -/
lemma filled_product_partialTrace (F : ExceptionPattern p l) (z : MatchedPair p → ℂ)
    (hz : ∑ a, z a * star (z a) = 1) :
    partialTrace (PositiveTensor.outer ((inclusion F.embedding).mulVec (OrdinaryTensor.tensorVector z))) =
      pinnedDensity F.sites (fun i => (F.pair i).1) (pairDensity z hz) := by
  rw [F.pairProduct_inclusion]
  have he : partialTrace (PositiveTensor.outer (F.pairProduct z)) =
      productMatrix (fun i => F.siteAmplitude z i * (F.siteAmplitude z i).conjTranspose) := by
    ext u v
    simpa only [partialTrace,PositiveTensor.outer,Matrix.vecMulVec_apply,Pi.star_apply,pairProduct] using
      pair_product_partialTrace (F.siteAmplitude z) u v
  rw [he]
  congr 1
  funext i
  by_cases hi : i ∈ F.sites
  · simp only [siteAmplitude,hi,dite_eq_left,pinAmplitude_density]
  · simp [siteAmplitude,hi,pairDensity]
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor.ExceptionPattern
open PositiveTensor
variable {p l : ℕ}

lemma purified_trace_le (F : ExceptionPattern p l) (A : commutant p l) :
    Matrix.trace (OrdinaryTensor.outer (F.purified A)) ≤ Matrix.trace (A.val*A.val.conjTranspose) := by
  rw [← sum_purified_trace A]
  exact Finset.single_le_sum (fun G _ => OrdinaryTensor.outer_trace_nonneg (G.purified A)) (Finset.mem_univ F)

abbrev Data (F : ExceptionPattern p l) :=
  OrdinaryTensor.Histogram F.Free (MatchedPair p) × OrdinaryTensor.PhaseSpace F.Free (MatchedPair p)

def dataDensity (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) (d : F.Data) : EvenDensity p :=
  pairDensity (OrdinaryTensor.empiricalVector d.1 d.2) (OrdinaryTensor.empiricalVector_unit hn d.1 d.2)

def dataPoint (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hn : 0 < Fintype.card F.Free) (d : F.Data) : EvenDensity p :=
  depolarizedDensity s hp (F.dataDensity hn d)

def rawPinned (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : F.Data, pinnedDensity F.sites (fun i => (F.pair i).1) (F.dataDensity hn d)

def rawDensity (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p) (hn : 0 < Fintype.card F.Free) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : F.Data, densityPower l (F.dataPoint s hp hn d).val

lemma rawPinned_posSemidef (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) :
    (F.rawPinned hn).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun d _ => pinnedDensity_posSemidef _ _ _)
lemma rawDensity_posSemidef (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p) (hn : 0 < Fintype.card F.Free) :
    (F.rawDensity s hp hn).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun d _ => densityPower_posSemidef _ _ (F.dataPoint s hp hn d).property.1)

lemma rawMixture_partialTrace (F : ExceptionPattern p l) (hn : 0 < Fintype.card F.Free) :
    partialTrace (inclusion F.embedding *
      (OrdinaryTensor.rawMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose) =
      F.rawPinned hn := by
  unfold OrdinaryTensor.rawMixture rawPinned
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_sum,Matrix.sum_mul,partialTrace_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  have he := congrArg (partialTrace (J := Word p l) (K := Word p l))
    (mul_outer_mul_star (inclusion F.embedding)
      (OrdinaryTensor.tensorVector (OrdinaryTensor.empiricalVector h t)))
  exact he.trans (F.filled_product_partialTrace _ (OrdinaryTensor.empiricalVector_unit hn h t))

lemma rawPinned_domination (F : ExceptionPattern p l) (hp : 0 < p) (hn : 0 < Fintype.card F.Free) :
    (F.rawPinned hn - partialTrace (inclusion F.embedding *
      (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose)).PosSemidef := by
  let : Nonempty (MatchedPair p) := matchedPair_nonempty hp
  have h := (OrdinaryTensor.rawMixture_domination (I := F.Free) (A := MatchedPair p)).mul_mul_conjTranspose_same (inclusion F.embedding)
  rw [Matrix.mul_sub,Matrix.sub_mul] at h
  have hh := partialTrace_posSemidef _ h
  simpa only [partialTrace_sub,F.rawMixture_partialTrace hn] using hh

lemma rawPinned_absorption (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hps : p ≤ s) (hls : l ≤ s) (hn : 0 < Fintype.card F.Free) :
    ((((s+1 : ℝ)^(13*p^2)) : ℂ) • F.rawDensity s hp hn - F.rawPinned hn).PosSemidef := by
  have hh := Matrix.posSemidef_sum Finset.univ (fun d _ =>
    pinned_absorption_uniform s hp hps hls F.sites F.sites_card_le
      (fun i => (F.pair i).1) (F.dataDensity hn d))
  simpa only [Finset.sum_sub_distrib,← Finset.smul_sum,rawPinned,rawDensity,dataPoint,depolarizedDensity] using hh
end CoordinateSweeps.SignedTensor.ExceptionPattern

namespace CoordinateSweeps.SignedTensor
open PositiveTensor
variable {p l : ℕ}

lemma matchedPair_card_le (p : ℕ) : Fintype.card (MatchedPair p) ≤ (2*p)*(2*p) := by
  simpa only [Pair,Fintype.card_prod,Letter,Fintype.card_fin] using
    (Fintype.card_subtype_le (fun a : Pair p => odd a.1 ↔ odd a.2))

namespace ExceptionPattern

def empty (p l : ℕ) : ExceptionPattern p l where
  sites := ∅
  pair i := False.elim (Finset.notMem_empty i.val i.property)
  mismatch i := False.elim (Finset.notMem_empty i.val i.property)
  injective i := False.elim (Finset.notMem_empty i.val i.property)

instance : Nonempty (ExceptionPattern p l) := ⟨empty p l⟩

lemma data_card_le (F : ExceptionPattern p l) : Fintype.card F.Data ≤ (l+1)^(8*p^2) := by
  have hh := OrdinaryTensor.histogram_card_le (I := F.Free) (A := MatchedPair p)
  have ht : Fintype.card (OrdinaryTensor.PhaseSpace F.Free (MatchedPair p)) =
      (Fintype.card F.Free+1)^Fintype.card (MatchedPair p) := by
    simp [OrdinaryTensor.PhaseSpace]
  rw [Fintype.card_prod,ht]
  calc
    _ ≤ (Fintype.card F.Free+1)^(2*Fintype.card (MatchedPair p)) := by
      rw [two_mul (Fintype.card (MatchedPair p)),pow_add]
      exact Nat.mul_le_mul_right _ hh
    _ ≤ (l+1)^(2*Fintype.card (MatchedPair p)) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right F.free_card_le 1) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith [matchedPair_card_le p])

lemma free_power_le (F : ExceptionPattern p l) (s : ℕ) (hls : l ≤ s) :
    (Fintype.card F.Free+1 : ℕ)^(2*Fintype.card (MatchedPair p)) ≤ (s+1)^(8*p^2) := by
  calc
    _ ≤ (s+1)^(2*Fintype.card (MatchedPair p)) :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (F.free_card_le.trans hls) 1) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith [matchedPair_card_le p])

lemma component_uniform_domination (F : ExceptionPattern p l) (s : ℕ) (hp : 0 < p)
    (hps : p ≤ s) (hls : l ≤ s) (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(21*p^2)) •
      F.rawDensity s hp (F.free_card_pos hl) - partialTrace (PositiveTensor.outer (F.component A))).PosSemidef := by
  let hn := F.free_card_pos hl
  let M := partialTrace (inclusion F.embedding *
      (OrdinaryTensor.finiteMixture (I := F.Free) (A := MatchedPair p)) * (inclusion F.embedding).conjTranspose)
  have hM : M.PosSemidef := partialTrace_posSemidef _
    (OrdinaryTensor.finiteMixture_posSemidef.mul_mul_conjTranspose_same _)
  have ht : (0 : ℂ) ≤ Matrix.trace (A.val*A.val.conjTranspose) :=
    (Matrix.posSemidef_self_mul_conjTranspose A.val).trace_nonneg
  have ha : (0 : ℂ) ≤ Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(8*p^2) :=
    mul_nonneg ht (by positivity)
  have hc : Matrix.trace (OrdinaryTensor.outer (F.purified A)) *
      ((Fintype.card F.Free+1 : ℕ) : ℂ)^(2*Fintype.card (MatchedPair p)) ≤
      Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(8*p^2) := by
    exact mul_le_mul (F.purified_trace_le A) (by exact_mod_cast F.free_power_le s hls)
      (by positivity) ht
  have h₁ := domination_pad _ M _ _ hM hc (F.component_postselection hp hl A)
  have h₂ := domination_trans _ M (F.rawPinned hn) _ 1 ha h₁ (by
    simpa only [one_smul] using F.rawPinned_domination hp hn)
  rw [mul_one] at h₂
  have h₃ := domination_trans _ (F.rawPinned hn) (F.rawDensity s hp hn) _
    (((s+1 : ℝ)^(13*p^2)) : ℂ) ha h₂ (F.rawPinned_absorption s hp hps hls hn)
  convert h₃ using 1
  push_cast
  rw [mul_assoc,← pow_add]
  congr 2; ring
end ExceptionPattern

abbrev DensityProfile (p l : ℕ) := Σ F : ExceptionPattern p l, F.Data

lemma densityProfile_card_le (p l : ℕ) : Fintype.card (DensityProfile p l) ≤ (l+1)^(12*p^2) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _F : ExceptionPattern p l, (l+1)^(8*p^2) :=
      Finset.sum_le_sum (fun F _ => F.data_card_le)
    _ = Fintype.card (ExceptionPattern p l) * (l+1)^(8*p^2) := by simp
    _ ≤ (l+1)^((2*p)*(2*p)) * (l+1)^(8*p^2) :=
      Nat.mul_le_mul_right _ (ExceptionPattern.card_le (p := p) (l := l))
    _ = _ := by rw [← pow_add]; congr 1; ring

lemma densityProfile_nonempty (hp : 0 < p) : Nonempty (DensityProfile p l) := by
  let : Nonempty (MatchedPair p) := ExceptionPattern.matchedPair_nonempty hp
  let F := ExceptionPattern.empty p l
  exact ⟨⟨F,Classical.choice inferInstance⟩⟩

def profilePoint (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l)
    (d : DensityProfile p l) : EvenDensity p := d.1.dataPoint s hp (d.1.free_card_pos hl) d.2

def rawProfileDensity (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    Matrix (Word p l) (Word p l) ℂ :=
  ∑ d : DensityProfile p l, densityPower l (profilePoint s p l hp hl d).val

lemma rawProfileDensity_eq (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    rawProfileDensity s p l hp hl = ∑ F : ExceptionPattern p l, F.rawDensity s hp (F.free_card_pos hl) := by
  exact Fintype.sum_sigma _

lemma rawProfileDensity_posSemidef (s p l : ℕ) (hp : 0 < p) (hl : (2*p)*(2*p) < l) :
    (rawProfileDensity s p l hp hl).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun d _ => densityPower_posSemidef _ _ (profilePoint s p l hp hl d).property.1)

/- Finite postselection for the literal signed action commutant. -/
theorem commutant_covariance_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hls : l ≤ s) (hl : (2*p)*(2*p) < l) (A : commutant p l) :
    ((Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(25*p^2)) •
      rawProfileDensity s p l hp hl - A.val*A.val.conjTranspose).PosSemidef := by
  have hc := partialTrace_posSemidef _ (outer_sum_domination (fun F : ExceptionPattern p l => F.component A))
  rw [ExceptionPattern.component_sum,partialTrace_sub,partialTrace_smul,partialTrace_sum,
    partialTrace_outer_matrix] at hc
  have hsum := Matrix.posSemidef_sum Finset.univ (fun (F : ExceptionPattern p l) _ =>
    F.component_uniform_domination s hp hps hls hl A)
  rw [Finset.sum_sub_distrib,← Finset.smul_sum,← rawProfileDensity_eq s p l hp hl] at hsum
  have h := domination_trans _ _ _ (Fintype.card (ExceptionPattern p l) : ℂ) _ (by positivity) hc hsum
  have hcard : Fintype.card (ExceptionPattern p l) ≤ (s+1)^(4*p^2) := by
    calc
      _ ≤ (l+1)^((2*p)*(2*p)) := ExceptionPattern.card_le (p := p) (l := l)
      _ ≤ (s+1)^((2*p)*(2*p)) := Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _
      _ = _ := by congr 1; ring
  apply domination_pad _ _ _ _ (rawProfileDensity_posSemidef s p l hp hl) _ h
  calc
    _ ≤ ((s+1 : ℕ) : ℂ)^(4*p^2) *
        (Matrix.trace (A.val*A.val.conjTranspose) * ((s+1 : ℕ) : ℂ)^(21*p^2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg (by positivity))
    _ = _ := by rw [mul_left_comm,← pow_add]; congr 2; ring
end CoordinateSweeps.SignedTensor

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace CoordinateSweeps.FiniteAtomic
variable {I X V : Type*} [Fintype I] [Nonempty I] [MeasurableSpace X]
  [MeasurableSingletonClass X] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def uniform (x : I → X) : Measure X :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

instance uniform_probability (x : I → X) : IsProbabilityMeasure (uniform x) := by
  constructor
  simp [uniform, Measure.finsetSum_apply, ENNReal.inv_mul_cancel,
    Fintype.card_ne_zero]

omit [Nonempty I] in
lemma uniform_integral (x : I → X) (f : X → V) :
    (∫ z, f z ∂uniform x) = (Fintype.card I : ℝ)⁻¹ • ∑ i, f (x i) := by
  unfold uniform
  rw [integral_smul_measure,integral_finsetSum_measure]
  · simp [integral_dirac]
  · intro i _
    exact integrable_dirac enorm_lt_top
end CoordinateSweeps.FiniteAtomic

namespace CoordinateSweeps.SignedTensor
open PositiveTensor MeasureTheory

instance (p : ℕ) : MeasurableSingletonClass (EvenDensity p) := by
  let : MeasurableSpace (Matrix (Letter p) (Letter p) ℂ) := borel _
  let : BorelSpace (Matrix (Letter p) (Letter p) ℂ) := ⟨rfl⟩
  change MeasurableSingletonClass {r : Matrix (Letter p) (Letter p) ℂ // _}
  infer_instance

lemma isotypic_mem_commutant {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ ∈ commutant p l := by
  intro σ
  rw [isotypic_eq_projector]
  exact (ρ.projector_commute (action p l) σ).symm

lemma isotypic_self_mul {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ * (isotypic (p := p) ρ).conjTranspose = isotypic (p := p) ρ := by
  rw [(isotypic_posSemidef ρ).isHermitian.eq,isotypic_eq_projector,ρ.projector_idempotent]

lemma isotypic_trace_le (s p l : ℕ) (hls : l ≤ s) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix.trace (isotypic (p := p) ρ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) := by
  rw [isotypic_trace]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := (multiplicity_le p l ρ).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _)
  have he : (2*p)*(2*p) = 4*p^2 := by ring
  rw [he] at hh
  exact_mod_cast hh

/- The large-slot case, as an actual probability mixture of even densities. -/
theorem density_domination_large (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : (2*p)*(2*p) < l) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    ∃ μ : Measure (EvenDensity p), IsProbabilityMeasure μ ∧
      (((ρ.dimension : ℂ) * ((s+1 : ℕ) : ℂ)^(41*p^2)) •
        (∫ r : EvenDensity p, densityPower l r.val ∂μ) - isotypic (p := p) ρ).PosSemidef := by
  let : Nonempty (DensityProfile p l) := densityProfile_nonempty hp
  let x := profilePoint s p l hp hl
  let μ := FiniteAtomic.uniform x
  refine ⟨μ,inferInstance,?_⟩
  have hint : (∫ r : EvenDensity p, densityPower l r.val ∂μ) =
      (Fintype.card (DensityProfile p l) : ℂ)⁻¹ • rawProfileDensity s p l hp hl := by
    rw [FiniteAtomic.uniform_integral]
    change (Fintype.card (DensityProfile p l) : ℝ)⁻¹ • rawProfileDensity s p l hp hl = _
    ext u v
    simp [Complex.real_smul]
  rw [hint]
  let A : commutant p l := ⟨isotypic ρ,isotypic_mem_commutant ρ⟩
  have h := commutant_covariance_domination s p l hp hps hls hl A
  change ((_ * _) • _ - isotypic ρ * (isotypic ρ).conjTranspose).PosSemidef at h
  simp only [A,isotypic_self_mul] at h
  have hcard : Fintype.card (DensityProfile p l) ≤ (s+1)^(12*p^2) :=
    (densityProfile_card_le p l).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _)
  have hc0 : (Fintype.card (DensityProfile p l) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbig : ((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹ ≥ 1 := by
    have hi : (0 : ℂ) ≤ (Fintype.card (DensityProfile p l) : ℂ)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_right (show (Fintype.card (DensityProfile p l) : ℂ) ≤
      ((s+1 : ℕ) : ℂ)^(12*p^2) by exact_mod_cast hcard) hi
    simpa only [mul_inv_cancel₀ hc0] using hh
  rw [smul_smul]
  apply domination_pad _ _ _ _ (rawProfileDensity_posSemidef s p l hp hl) _ h
  calc
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) * ((s+1 : ℕ) : ℂ)^(25*p^2) :=
      mul_le_mul_of_nonneg_right (isotypic_trace_le s p l hls ρ) (by positivity)
    _ = (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) := by
      rw [mul_assoc,← pow_add]; congr 2; ring
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2)) *
        (((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹) := by
      have hh := mul_le_mul_of_nonneg_left hbig
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) by positivity)
      simpa only [mul_one] using hh
    _ = _ := by
      rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]
      congr 3; ring

def uniformDensity (p : ℕ) (hp : 0 < p) : EvenDensity p :=
  ⟨((2*p : ℕ) : ℂ)⁻¹ • 1, Matrix.PosSemidef.one.smul (by positivity), by
    rw [Matrix.trace_smul,Matrix.trace_one]
    have hc : ((2*p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [Letter,Fintype.card_fin,smul_eq_mul] using inv_mul_cancel₀ hc,
    by
      intro i j hij
      have hne : i ≠ j := by intro he; subst j; tauto
      simp [hne]⟩

lemma densityPower_one (p l : ℕ) : densityPower l (1 : Matrix (Letter p) (Letter p) ℂ) = 1 := by
  ext u v
  by_cases huv : u=v
  · subst v
    simp [densityPower]
  · have hi : ∃ i, u i ≠ v i := Function.ne_iff.mp huv
    obtain ⟨i,hi⟩ := hi
    simp only [densityPower,Matrix.one_apply,ite_eq_right huv]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma densityPower_smul {p : ℕ} (l : ℕ) (c : ℂ) (r : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l (c • r) = c^l • densityPower l r := by
  ext u v
  simp [densityPower,Finset.prod_mul_distrib]

lemma uniformDensity_power (p l : ℕ) (hp : 0 < p) :
    densityPower l (uniformDensity p hp).val = (((2*p : ℕ) : ℂ)^l)⁻¹ • 1 := by
  change densityPower l ((((2*p : ℕ) : ℂ)⁻¹) • 1) = _
  rw [densityPower_smul,densityPower_one,inv_pow]

lemma small_power_le (s p l : ℕ) (hps : p ≤ s) (hl : l ≤ (2*p)*(2*p)) :
    (2*p)^l ≤ (s+1)^(8*p^2) := by
  have hb : 2*p ≤ (s+1)^2 := by nlinarith
  calc
    _ ≤ ((s+1)^2)^l := Nat.pow_le_pow_left hb l
    _ = (s+1)^(2*l) := by rw [pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

/- Small slot counts, including zero, require no exceptional-sector chart. -/
theorem density_domination_small (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : l ≤ (2*p)*(2*p)) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    ∃ μ : Measure (EvenDensity p), IsProbabilityMeasure μ ∧
      (((ρ.dimension : ℂ) * ((s+1 : ℕ) : ℂ)^(12*p^2)) •
        (∫ r : EvenDensity p, densityPower l r.val ∂μ) - isotypic (p := p) ρ).PosSemidef := by
  refine ⟨Measure.dirac (uniformDensity p hp),inferInstance,?_⟩
  rw [integral_dirac,uniformDensity_power,smul_smul]
  have hP := trace_domination (isotypic (p := p) ρ) (isotypic_posSemidef ρ)
  apply domination_pad _ 1 _ _ Matrix.PosSemidef.one _ hP
  have hc0 : (((2*p : ℕ) : ℂ)^l) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hi : (0 : ℂ) ≤ (((2*p : ℕ) : ℂ)^l)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_right (show (((2*p : ℕ) : ℂ)^l) ≤
    ((s+1 : ℕ) : ℂ)^(8*p^2) by exact_mod_cast small_power_le s p l hps hl) hi
  rw [mul_inv_cancel₀ hc0] at hh
  calc
    _ ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) := isotypic_trace_le s p l hls ρ
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) *
        (((s+1 : ℕ) : ℂ)^(8*p^2)*(((2*p : ℕ) : ℂ)^l)⁻¹) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) by positivity)
    _ = _ := by rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]; congr 3; ring

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor MeasureTheory

lemma domination_coefficient (D s p : ℕ) (hD : 0 < D) :
    (Complex.ofReal (Real.exp (Real.log D+41*p^2*Real.log (s+1)))) =
      (D : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : (0 : ℝ) < s+1 := by positivity
  rw [Real.exp_add,Real.exp_log hD']
  have he : (41 : ℝ)*p^2*Real.log (s+1) = ((41*p^2 : ℕ) : ℝ)*Real.log (s+1) := by push_cast; ring
  rw [he,Real.exp_nat_mul,Real.exp_log hs]
  push_cast
  rfl

/- Source05 equation13, with a concrete absolute constant. The measure is
constructed from finite empirical phase mixtures, not an added hypothesis. -/
theorem signed_density_domination : Domination := by
  refine ⟨41,by norm_num,?_⟩
  intro s p hp hps l hls ρ
  have hp0 : 0 < p := by omega
  rw [domination_coefficient ρ.dimension s p ρ.positive]
  by_cases hl : (2*p)*(2*p) < l
  · exact density_domination_large s p l hp0 hps hls hl ρ
  · obtain ⟨μ,hμ,h⟩ := density_domination_small s p l hp0 hps hls (by omega) ρ
    refine ⟨μ,hμ,?_⟩
    have hM : (∫ r : EvenDensity p, densityPower l r.val ∂μ).PosSemidef := by
      -- Positivity of the integral follows from the explicitly proved lower
      -- bound by a PSD projection; no measurability of arbitrary kernels is needed.
      have ha : 0 < (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(12*p^2) := by
        exact_mod_cast mul_pos (show (0 : ℝ) < ρ.dimension by exact_mod_cast ρ.positive)
          (pow_pos (show (0 : ℝ) < s+1 by positivity) _)
      have hh := h.add (isotypic_posSemidef ρ)
      rw [sub_add_cancel] at hh
      have hc : (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(12*p^2) ≠ 0 := ne_of_gt ha
      have hh' := hh.smul (le_of_lt (inv_pos.mpr ha))
      rwa [smul_smul,inv_mul_cancel₀ hc,one_smul] at hh'
    apply domination_pad _ _ _ _ hM _ h
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : 12*p^2 ≤ 41*p^2 := by omega
    exact_mod_cast Nat.pow_le_pow_right (show 0 < s+1 by omega) he

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open PositiveTensor

lemma finite_profile_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : (2*p)*(2*p) < l) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
       ((Fintype.card (DensityProfile p l) : ℂ)⁻¹ • rawProfileDensity s p l hp hl) -
       isotypic (p := p) ρ).PosSemidef := by
  let : Nonempty (DensityProfile p l) := densityProfile_nonempty hp
  let A : commutant p l := ⟨isotypic ρ,isotypic_mem_commutant ρ⟩
  have h := commutant_covariance_domination s p l hp hps hls hl A
  change ((_ * _) • _ - isotypic ρ * (isotypic ρ).conjTranspose).PosSemidef at h
  simp only [A,isotypic_self_mul] at h
  have hcard : Fintype.card (DensityProfile p l) ≤ (s+1)^(12*p^2) :=
    (densityProfile_card_le p l).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hls 1) _)
  have hc0 : (Fintype.card (DensityProfile p l) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbig : ((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹ ≥ 1 := by
    have hi : (0 : ℂ) ≤ (Fintype.card (DensityProfile p l) : ℂ)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_right (show (Fintype.card (DensityProfile p l) : ℂ) ≤
      ((s+1 : ℕ) : ℂ)^(12*p^2) by exact_mod_cast hcard) hi
    simpa only [mul_inv_cancel₀ hc0] using hh
  rw [smul_smul]
  apply domination_pad _ _ _ _ (rawProfileDensity_posSemidef s p l hp hl) _ h
  calc
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) * ((s+1 : ℕ) : ℂ)^(25*p^2) :=
      mul_le_mul_of_nonneg_right (isotypic_trace_le s p l hls ρ) (by positivity)
    _ = (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) := by
      rw [mul_assoc,← pow_add]; congr 2; ring
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2)) *
        (((s+1 : ℕ) : ℂ)^(12*p^2) * (Fintype.card (DensityProfile p l) : ℂ)⁻¹) := by
      have hh := mul_le_mul_of_nonneg_left hbig
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(29*p^2) by positivity)
      simpa only [mul_one] using hh
    _ = _ := by
      rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]
      congr 3; ring

lemma finite_uniform_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (hl : l ≤ (2*p)*(2*p)) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(12*p^2)) •
      densityPower l (uniformDensity p hp).val-isotypic (p := p) ρ).PosSemidef := by
  rw [uniformDensity_power,smul_smul]
  have hP := trace_domination (isotypic (p := p) ρ) (isotypic_posSemidef ρ)
  apply domination_pad _ 1 _ _ Matrix.PosSemidef.one _ hP
  have hc0 : (((2*p : ℕ) : ℂ)^l) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hi : (0 : ℂ) ≤ (((2*p : ℕ) : ℂ)^l)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_right (show (((2*p : ℕ) : ℂ)^l) ≤
    ((s+1 : ℕ) : ℂ)^(8*p^2) by exact_mod_cast small_power_le s p l hps hl) hi
  rw [mul_inv_cancel₀ hc0] at hh
  calc
    _ ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) := isotypic_trace_le s p l hls ρ
    _ ≤ ((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2)) *
        (((s+1 : ℕ) : ℂ)^(8*p^2)*(((2*p : ℕ) : ℂ)^l)⁻¹) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
        (show (0 : ℂ) ≤ (ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(4*p^2) by positivity)
    _ = _ := by rw [← mul_assoc,mul_assoc (ρ.dimension : ℂ),← pow_add]; congr 3; ring

/- Finite (not a hypothetical measure) version of source05:eq13. -/
theorem finite_density_domination (s p l : ℕ) (hp : 0 < p) (hps : p ≤ s) (hls : l ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    ∃ (I : Type) (_ : Fintype I) (_ : Nonempty I) (r : I → EvenDensity p),
      (((ρ.dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
        ((Fintype.card I : ℂ)⁻¹ • ∑ i, densityPower l (r i).val)-isotypic (p := p) ρ).PosSemidef := by
  by_cases hl : (2*p)*(2*p)<l
  · exact ⟨DensityProfile p l,inferInstance,densityProfile_nonempty hp,
      profilePoint s p l hp hl,finite_profile_domination s p l hp hps hls hl ρ⟩
  · refine ⟨PUnit,inferInstance,inferInstance,fun _ => uniformDensity p hp,?_⟩
    simp only [Fintype.card_punit,Nat.cast_one,inv_one,Finset.univ_unique,Finset.sum_singleton,one_smul]
    apply domination_pad _ _ _ _ (densityPower_posSemidef _ _ (uniformDensity p hp).property.1) _
      (finite_uniform_domination s p l hp hps hls (by omega) ρ)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (show 0 < s+1 by omega) (show 12*p^2≤41*p^2 by omega)
end CoordinateSweeps.SignedTensor

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI

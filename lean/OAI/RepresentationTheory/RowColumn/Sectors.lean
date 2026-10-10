import OAI.LinearAlgebra.MatrixState.Postselection
import OAI.RepresentationTheory.FiniteUnitary.Reconstruction
import OAI.RepresentationTheory.RowColumn.SignedWords

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
namespace RowColumn.MatrixState
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]

def evenAlgebra (odd : C → Prop) : StarSubalgebra ℂ (Matrix C C ℂ) where
  carrier := {M | ∀ c d, ¬(odd c ↔ odd d) → M c d=0}
  zero_mem' := by intro c d h; rfl
  add_mem' := by intro M N hM hN c d h; change M c d + N c d=0; simp only [hM c d h,hN c d h,add_zero]
  mul_mem' := by
    intro M N hM hN c d h
    change (∑ e, M c e * N e d)=0
    apply Finset.sum_eq_zero
    intro e _
    change M c e * N e d=0
    by_cases he : odd c ↔ odd e
    · rw [hN e d (fun hd => h (he.trans hd)), mul_zero]
    · rw [hM c e he, zero_mul]
  one_mem' := by
    intro c d h
    exact Matrix.one_apply_ne (fun he => h (he ▸ Iff.rfl))
  algebraMap_mem' := by
    intro z c d h
    have hcd : c≠d := fun he => h (he ▸ Iff.rfl)
    simp [Algebra.algebraMap_eq_smul_one, hcd]
  star_mem' := by
    intro M hM c d h
    change star (M d c)=0
    rw [hM d c (fun hh => h hh.symm), star_zero]

lemma evenAlgebra_mem (odd : C → Prop) (M : Matrix C C ℂ) :
    M ∈ evenAlgebra odd ↔ ∀ c d, ¬(odd c ↔ odd d) → M c d=0 := Iff.rfl

omit [DecidableEq S] in
lemma tensorMatrix_even_support (odd : C → Prop) (M : S → Matrix C C ℂ)
    (hM : ∀ i, M i ∈ evenAlgebra odd) (w v : S → C)
    (h : ¬ ∀ i, odd (w i) ↔ odd (v i)) : tensorMatrix M w v=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hM i (w i) (v i) hi)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddCount_eq (odd : C → Prop) [DecidablePred odd] (w v : S → C)
    (h : ∀ i, odd (w i) ↔ odd (v i)) :
    Fintype.card {i : S // odd (w i)} = Fintype.card {i : S // odd (v i)} := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight h)

def sectorTensor (odd : C → Prop) [DecidablePred odd] (k : ℕ) (M : S → Matrix C C ℂ) :
    Matrix (Signed.Words (S := S) odd k) (Signed.Words (S := S) odd k) ℂ :=
  (tensorMatrix M).submatrix Subtype.val Subtype.val

lemma sectorTensor_mul (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (M N : S → Matrix C C ℂ) (hM : ∀ i, M i ∈ evenAlgebra odd) :
    sectorTensor odd k (fun i => M i * N i) = sectorTensor odd k M * sectorTensor odd k N := by
  ext w v
  change tensorMatrix (fun i => M i*N i) w.1 v.1 = _
  rw [← tensorMatrix_mul]
  change (∑ z : S → C, tensorMatrix M w.1 z * tensorMatrix N z v.1) =
    ∑ z : Signed.Words (S := S) odd k, tensorMatrix M w.1 z.1 * tensorMatrix N z.1 v.1
  have hz : (∑ z : {z : S → C // ¬ Fintype.card {i : S // odd (z i)}=k},
      tensorMatrix M w.1 z.1 * tensorMatrix N z.1 v.1)=0 := by
    apply Finset.sum_eq_zero
    intro z _
    rw [tensorMatrix_even_support odd M hM w.1 z.1, zero_mul]
    intro hh
    exact z.2 ((oddCount_eq odd w.1 z.1 hh).symm.trans w.2)
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun z : S → C => Fintype.card {i : S // odd (z i)}=k)
    (fun z : S → C => tensorMatrix M w.1 z * tensorMatrix N z v.1)
  rw [hz, add_zero] at he
  exact he.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_star (odd : C → Prop) [DecidablePred odd] (k : ℕ) (M : S → Matrix C C ℂ) :
    sectorTensor odd k (fun i => star (M i)) = star (sectorTensor odd k M) := by
  unfold sectorTensor
  change (tensorMatrix (fun i => (M i).conjTranspose)).submatrix Subtype.val Subtype.val = _
  rw [← tensorMatrix_star]
  rfl

omit [DecidableEq S] [Fintype C] in
lemma sectorTensor_one (odd : C → Prop) [DecidablePred odd] (k : ℕ) :
    sectorTensor odd k (fun _ : S => (1 : Matrix C C ℂ))=1 := by
  rw [sectorTensor, tensorMatrix_one]
  exact Matrix.submatrix_one Subtype.val Subtype.val_injective

def sectorPowerHom (odd : C → Prop) [DecidablePred odd] (k : ℕ) :
    evenAlgebra odd →⋆* Matrix (Signed.Words (S := S) odd k) (Signed.Words (S := S) odd k) ℂ where
  toFun M := sectorTensor odd k (fun _ : S => M.val)
  map_one' := sectorTensor_one odd k
  map_mul' M _ := sectorTensor_mul odd k _ _ (fun _ => M.property)
  map_star' _ := sectorTensor_star odd k _

end RowColumn.MatrixState

noncomputable section
namespace RowColumn.Signed
open scoped Classical
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] in
lemma frame_pred_congr (p q : S → Prop) [dp : DecidablePred p] [dq : DecidablePred q]
    (hp : Fintype.card {x : S // p x} = k)
    (hq : Fintype.card {x : S // q x} = k)
    (he : p = q) (x : S) (hx : p x) (hy : q x) :
    Fintype.equivFinOfCardEq hp ⟨x,hx⟩ = Fintype.equivFinOfCardEq hq ⟨x,hy⟩ := by
  subst q
  have hd : dq = dp := Subsingleton.elim _ _
  subst dq
  rfl

omit [Fintype C] [DecidableEq C] in
omit [DecidableEq S] in
lemma oddFrame_parity_congr (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) (x : S)
    (hx : odd (w.1 x)) (hv : odd (v.1 x)) :
    oddFrame w ⟨x,hx⟩ = oddFrame v ⟨x,hv⟩ := by
  exact frame_pred_congr _ _ w.2 v.2 (funext fun x => propext (hp x)) x hx hv

omit [Fintype C] [DecidableEq C] [DecidableEq S] in
lemma oddPerm_parity_congr (g : Equiv.Perm S) (w v : Words (S := S) odd k)
    (hp : ∀ x, odd (w.1 x) ↔ odd (v.1 x)) : oddPerm g w = oddPerm g v := by
  apply Equiv.ext
  intro i
  have he : ((oddFrame w).symm i).val = ((oddFrame v).symm i).val := by
    have hh := oddFrame_parity_congr w v hp ((oddFrame w).symm i).val
      ((oddFrame w).symm i).property ((hp _).mp ((oddFrame w).symm i).property)
    rw [Equiv.apply_symm_apply] at hh
    have ht := congrArg (fun z => ((oddFrame v).symm z).val) hh
    simpa using ht.symm
  have ha : ∀ x, odd ((actWord g w).1 x) ↔ odd ((actWord g v).1 x) := fun x => hp _
  change oddFrame (actWord g w) ⟨g ((oddFrame w).symm i).val, _⟩ =
    oddFrame (actWord g v) ⟨g ((oddFrame v).symm i).val, _⟩
  have hw : odd ((actWord g w).1 (g ((oddFrame w).symm i).val)) := by
    simpa using ((oddFrame w).symm i).property
  calc
    _ = oddFrame (actWord g v) ⟨g ((oddFrame w).symm i).val, (ha _).mp hw⟩ :=
      oddFrame_parity_congr _ _ ha _ _ _
    _ = _ := congrArg (oddFrame (actWord g v)) (Subtype.ext (congrArg g he))
end RowColumn.Signed

noncomputable section
namespace RowColumn.FiniteStarAlgebra
variable {R A G : Type*} [CommSemiring R] [StarRing R] [Ring A] [Algebra R A]
  [StarRing A] [StarModule R A] [Group G]

def unitarySpan (u : G →* unitary A) : StarSubalgebra R A where
  __ := Algebra.adjoin R (Set.range fun g : G => (u g : A))
  star_mem' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨g,rfl⟩ := ha
      apply Algebra.subset_adjoin
      refine ⟨g⁻¹,?_⟩
      change (u g⁻¹ : A) = star (u g : A)
      rw [map_inv]
      rfl
    | algebraMap r => rw [← algebraMap_star_comm]; exact (Algebra.adjoin R _).algebraMap_mem _
    | add a b ha hb iha ihb => rw [star_add]; exact (Algebra.adjoin R _).add_mem iha ihb
    | mul a b ha hb iha ihb => rw [star_mul]; exact (Algebra.adjoin R _).mul_mem ihb iha

lemma unitarySpan_eq_span (u : G →* unitary A) :
    (unitarySpan (R := R) u).toSubmodule = Submodule.span R (Set.range fun g : G => (u g : A)) := by
  apply Algebra.adjoin_eq_span_of_subset
  intro a ha
  have hh : a ∈ Set.range (fun g : G => (u g : A)) := by
    induction ha using Submonoid.closure_induction with
    | mem a ha => exact ha
    | one => exact ⟨1,by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨g,rfl⟩ := iha
      obtain ⟨h,rfl⟩ := ihb
      exact ⟨g*h,by simp⟩
  exact Submodule.subset_span hh

lemma unitarySpan_mem (u : G →* unitary A) (g : G) : (u g : A) ∈ unitarySpan (R := R) u :=
  Algebra.subset_adjoin ⟨g,rfl⟩

def unitarySpanHom (u : G →* unitary A) : G →* unitary (unitarySpan (R := R) u) where
  toFun g := ⟨⟨(u g : A),unitarySpan_mem u g⟩,by
    constructor <;> apply Subtype.ext
    · exact (u g).property.1
    · exact (u g).property.2⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; change (u 1 : A)=1; simp
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; change (u (g*h) : A)=(u g : A)*(u h : A); simp

lemma unitarySpanHom_spans (u : G →* unitary A) :
    Submodule.span R (Set.range fun g : G => (unitarySpanHom (R := R) u g : unitarySpan (R := R) u))=⊤ := by
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (unitarySpan (R := R) u).toSubmodule)
  rw [Submodule.map_span, ← Set.range_comp]
  change Submodule.span R (Set.range fun g : G => (u g : A)) =
    Submodule.map (unitarySpan (R := R) u).toSubmodule.subtype ⊤
  rw [Submodule.map_top, Submodule.range_subtype]
  exact (unitarySpan_eq_span u).symm

end RowColumn.FiniteStarAlgebra

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
open ComplexConjugate
namespace RowColumn.MatrixState

def discreteContinuousHom (J : Type*) [TopologicalSpace J] [DiscreteTopology J] :
    (J → ℂ) →⋆ₐ[ℂ] C(J,ℂ) where
  toFun f := ⟨f,continuous_of_discreteTopology⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def precompFunctionHom {J K : Type*} (f : J → K) : (K → ℂ) →⋆ₐ[ℂ] (J → ℂ) where
  toFun g := g ∘ f
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma sum_single_function {J : Type*} [Fintype J] [DecidableEq J] (z : J → ℂ) :
    (∑ i : J, z i • (Pi.single i 1 : J → ℂ)) = z := by
  ext j
  simp [Pi.single_apply]

lemma function_unitary {J : Type*} (z : J → ℂ) (hz : ∀ i, ‖z i‖=1) : z ∈ unitary (J → ℂ) := by
  constructor <;> ext i
  · change conj (z i)*z i=1
    rw [Complex.conj_mul', hz i]
    norm_num
  · change z i*conj (z i)=1
    rw [Complex.mul_conj', hz i]
    norm_num

/-- A genuine finite spectral phase family inside the prescribed closed
star algebra. In the application this is the even one-slot matrix algebra. -/
theorem exists_spectral_phase_family {C : Type*} [Fintype C] [DecidableEq C]
    (M : Matrix C C ℂ) (hM : M.IsHermitian)
    (K : StarSubalgebra ℂ (Matrix C C ℂ)) (hK : IsClosed (K : Set (Matrix C C ℂ)))
    (hMK : M ∈ K) :
    ∃ (d : ℕ) (P : Fin d → Matrix C C ℂ) (z : Fin d → ℂ),
      (∑ i, z i • P i) = M ∧ (∀ i, P i ∈ K) ∧
      ∀ θ : Fin d → ℂ, (∀ i, ‖θ i‖=1) → (∑ i, θ i • P i) ∈ unitary (Matrix C C ℂ) := by
  have hfin : (spectrum ℂ M).Finite := by
    rw [hM.spectrum_eq_image_range]
    exact (Set.finite_range hM.eigenvalues).image _
  let J := spectrum ℂ M
  let : Fintype J := hfin.fintype
  let : DiscreteTopology J := inferInstance
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let ψ := (cfcHom hM.isSelfAdjoint.isStarNormal (R := ℂ)).comp
    ((discreteContinuousHom J).comp (precompFunctionHom e))
  let P (i : Fin (Fintype.card J)) : Matrix C C ℂ := ψ (Pi.single i 1)
  let z (i : Fin (Fintype.card J)) : ℂ := (e.symm i).val
  have hsum (f : Fin (Fintype.card J) → ℂ) : ∑ i, f i • P i = ψ f := by
    simp only [P, ← map_smul, ← map_sum, sum_single_function]
  refine ⟨Fintype.card J,P,z,?_,?_,?_⟩
  · rw [hsum]
    have he : ((discreteContinuousHom J).comp (precompFunctionHom e)) z =
        (ContinuousMap.id ℂ).restrict (spectrum ℂ M) := by
      ext j
      exact congrArg Subtype.val (e.symm_apply_apply j)
    change cfcHom hM.isSelfAdjoint.isStarNormal (((discreteContinuousHom J).comp (precompFunctionHom e)) z) = M
    rw [he]
    exact cfcHom_id _
  · intro i
    apply StarAlgebra.elemental.le_of_mem hK hMK
    exact cfcHom_mem_elemental hM.isSelfAdjoint.isStarNormal _
  · intro θ hθ
    rw [hsum]
    exact Unitary.map_mem ψ (function_unitary θ hθ)

end RowColumn.MatrixState

noncomputable section
open scoped BigOperators Classical
namespace RowColumn.MatrixState
open WordOrbits Postselection
variable {S C J : Type*} [Fintype S] [DecidableEq S]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

omit [Fintype C] [DecidableEq C] [DecidableEq J] in
lemma tensorMatrix_linear_combination (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) =
      ∑ w : S → J, (∏ i, z (w i)) • tensorMatrix (fun i => P (w i)) := by
  ext a b
  simp only [tensorMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_mul_distrib

def typeTensor (P : J → Matrix C C ℂ) (q : Types (S := S) (A := J)) :
    Matrix (S → C) (S → C) ℂ :=
  ∑ w : {w : S → J // counts w = q}, tensorMatrix (fun i => P (w.1 i))

omit [Fintype C] [DecidableEq C] in
lemma tensorMatrix_by_type (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) =
      ∑ q : Types (S := S) (A := J), typeAmplitude z q • typeTensor P q := by
  rw [tensorMatrix_linear_combination]
  simp_rw [prod_by_counts _ z]
  change (∑ w : S → J, typeAmplitude z (counts w) • tensorMatrix (fun i => P (w i))) = _
  rw [← Fintype.sum_fiberwise counts (fun w : S → J =>
    typeAmplitude z (counts w) • tensorMatrix (fun i => P (w i)))]
  apply Finset.sum_congr rfl
  intro q _
  simp only [show ∀ w : {w : S → J // counts w = q}, counts w.1=q from fun w => w.2]
  exact (Finset.smul_sum).symm

def phaseMatrix (P : J → Matrix C C ℂ) (θ : Phases J (Fintype.card S)) : Matrix C C ℂ :=
  ∑ j, ZMod.stdAddChar (θ j) • P j

omit [Fintype C] [DecidableEq C] in
lemma tensorMatrix_phase (P : J → Matrix C C ℂ) (θ : Phases J (Fintype.card S)) :
    tensorMatrix (fun _ : S => phaseMatrix P θ) =
      ∑ q : Types (S := S) (A := J), countCharacter q θ • typeTensor P q := by
  rw [phaseMatrix, tensorMatrix_by_type]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact (countCharacter_eq_prod q θ).symm

omit [Fintype C] [DecidableEq C] in
lemma typeTensor_fourier (P : J → Matrix C C ℂ) (q : Types (S := S) (A := J)) :
    (∑ θ : Phases J (Fintype.card S), star (countCharacter q θ) •
      tensorMatrix (fun _ : S => phaseMatrix P θ)) =
      (Fintype.card (Phases J (Fintype.card S)) : ℂ) • typeTensor P q := by
  simp_rw [tensorMatrix_phase, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have he (r : Types (S := S) (A := J)) :
      (∑ θ : Phases J (Fintype.card S), star (countCharacter q θ) * countCharacter r θ) =
        if r=q then (Fintype.card (Phases J (Fintype.card S)) : ℂ) else 0 := by
    simpa only [starRingEnd_apply, mul_comm] using character_orthogonality r q
  simp_rw [he]
  simp

omit [Fintype C] [DecidableEq C] in
/-- Every identical tensor of a linear combination of a finite family lies
in the span of its finite phase tensors. Applied to an even spectral family,
all the spanning tensors are genuine global even unitaries. -/
theorem tensorMatrix_mem_phase_span (P : J → Matrix C C ℂ) (z : J → ℂ) :
    tensorMatrix (fun _ : S => ∑ j, z j • P j) ∈
      Submodule.span ℂ (Set.range fun θ : Phases J (Fintype.card S) =>
        tensorMatrix (fun _ : S => phaseMatrix P θ)) := by
  let K := Submodule.span ℂ (Set.range fun θ : Phases J (Fintype.card S) =>
        tensorMatrix (fun _ : S => phaseMatrix P θ))
  have hm (q : Types (S := S) (A := J)) : typeTensor P q ∈ K := by
    have hcard : (Fintype.card (Phases J (Fintype.card S)) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [← one_smul ℂ (typeTensor P q), ← inv_mul_cancel₀ hcard, mul_smul,
      ← typeTensor_fourier P q]
    apply K.smul_mem
    apply K.sum_mem
    intro θ _
    exact K.smul_mem _ (Submodule.subset_span ⟨θ,rfl⟩)
  rw [tensorMatrix_by_type]
  exact K.sum_mem (fun q _ => K.smul_mem _ (hm q))

end RowColumn.MatrixState

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

abbrev Sector := EuclideanSpace ℂ (Words (S := S) odd k)

def sectorUnitary : unitary (evenAlgebra odd) →* unitary (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  ((Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)))).comp
    (Unitary.map (sectorPowerHom (S := S) odd k))).toMonoidHom

def sectorAlgebra : StarSubalgebra ℂ (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  unitarySpan (sectorUnitary (S := S) odd k)

lemma sectorUnitary_apply (U : unitary (evenAlgebra odd)) :
    (sectorUnitary (S := S) odd k U : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) =
      (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTensor odd k (fun _ : S => U.val.val)) := rfl

def tensorRestriction : Matrix (S → C) (S → C) ℂ →ₗ[ℂ]
    (Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) :=
  (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.comp
    ({ toFun M := M.submatrix Subtype.val Subtype.val
       map_add' _ _ := rfl
       map_smul' _ _ := by ext w v; rfl } :
        Matrix (S → C) (S → C) ℂ →ₗ[ℂ] Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ)

lemma tensorRestriction_apply (M : S → Matrix C C ℂ) :
    tensorRestriction (S := S) odd k (tensorMatrix M) = (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTensor odd k M) := rfl

/-- Identical even positive tensors really belong to the finite algebra of
actual global even unitary tensors. This is a proved phase-Fourier identity,
not a commutant-duality assumption. -/
theorem sectorTensor_mem_algebra (M : Matrix C C ℂ) (hM : M.IsHermitian) (heven : M ∈ evenAlgebra odd) :
    (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTensor odd k (fun _ : S => M)) ∈ sectorAlgebra (S := S) odd k := by
  have hclosed : IsClosed (evenAlgebra odd : Set (Matrix C C ℂ)) :=
    (evenAlgebra odd).toSubalgebra.toSubmodule.closed_of_finiteDimensional
  obtain ⟨d,P,z,he,hP,hU⟩ := exists_spectral_phase_family M hM (evenAlgebra odd) hclosed heven
  let F := tensorRestriction (S := S) odd k
  have ha (θ : Phases (Fin d) (Fintype.card S)) : F (tensorMatrix (fun _ : S => phaseMatrix (S := S) P θ)) ∈ sectorAlgebra (S := S) odd k := by
    have hphase : phaseMatrix (S := S) P θ ∈ evenAlgebra odd :=
      (evenAlgebra odd).sum_mem (fun i _ => (evenAlgebra odd).smul_mem (hP i) _)
    have hunit : phaseMatrix (S := S) P θ ∈ unitary (Matrix C C ℂ) :=
      hU _ (fun i => AddChar.norm_apply _ _)
    let U : unitary (evenAlgebra odd) := ⟨⟨phaseMatrix (S := S) P θ,hphase⟩,by
      constructor <;> apply Subtype.ext
      · exact hunit.1
      · exact hunit.2⟩
    exact unitarySpan_mem (R := ℂ) (sectorUnitary (S := S) odd k) U
  have hs : Submodule.span ℂ (Set.range fun θ : Phases (Fin d) (Fintype.card S) =>
      tensorMatrix (fun _ : S => phaseMatrix (S := S) P θ)) ≤
        (sectorAlgebra (S := S) odd k).toSubmodule.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨θ,rfl⟩
    exact ha θ
  have hh := hs (tensorMatrix_mem_phase_span (S := S) P z)
  rw [he] at hh
  exact hh

end RowColumn.MatrixState

namespace RowColumn.MatrixState
open Signed WordOrbits Postselection FiniteStarAlgebra
open scoped BigOperators Classical Matrix.Norms.L2Operator MatrixOrder
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  (odd : C → Prop) [DecidablePred odd] (k : ℕ)

abbrev GlobalTypes := Types (S := S) (A := C × C)

def sectorTypeMatrix (q : GlobalTypes (S := S) (C := C)) :
    Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ :=
  fun w v => if counts (fun i => (w.1 i,v.1 i))=q then 1 else 0

omit [DecidableEq S] in
lemma sectorTensor_type_expansion (M : Matrix C C ℂ) :
    sectorTensor odd k (fun _ : S => M) =
      ∑ q : GlobalTypes (S := S) (C := C),
        typeAmplitude (fun c : C × C => M c.1 c.2) q • sectorTypeMatrix odd k q := by
  ext w v
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sectorTypeMatrix]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact prod_by_counts (fun i => (w.1 i,v.1 i)) (fun c : C × C => M c.1 c.2)

lemma sectorAlgebra_le_type_span : (sectorAlgebra (S := S) odd k).toSubmodule ≤
    Submodule.span ℂ (Set.range fun q : GlobalTypes (S := S) (C := C) =>
      (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTypeMatrix odd k q)) := by
  rw [sectorAlgebra, unitarySpan_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨U,rfl⟩
  dsimp only
  rw [sectorUnitary_apply, sectorTensor_type_expansion]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q,rfl⟩)

/-- Polynomial Fourier algebra dimension, counted by joint word types.
No representation-theoretic carrier-dimension estimate is assumed. -/
theorem sectorAlgebra_finrank : Module.finrank ℂ (sectorAlgebra (S := S) odd k) ≤
    (Fintype.card S+1)^(Fintype.card C^2) := by
  have hh := Submodule.finrank_mono (sectorAlgebra_le_type_span (S := S) odd k)
  have hc := finrank_range_le_card (R := ℂ) (fun q : GlobalTypes (S := S) (C := C) =>
    (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)) (sectorTypeMatrix odd k q))
  exact hh.trans (by simpa only [Set.finrank, GlobalTypes, Types, CountIndex, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_prod, pow_two] using hc)

end RowColumn.MatrixState

end
end
end
end
end
end

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator
namespace RowColumn.MatrixState
open Signed FiniteStarAlgebra
variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (odd : C → Prop) [DecidablePred odd] (k : ℕ)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma sectorTensor_transport (M : Matrix C C ℂ) (g : Equiv.Perm S) (w v : Words (S := S) odd k) :
    sectorTensor odd k (fun _ : S => M) (actWord g w) (actWord g v) =
      sectorTensor odd k (fun _ : S => M) w v := by
  change (∏ i, M (w.1 (g⁻¹ i)) (v.1 (g⁻¹ i))) = ∏ i, M (w.1 i) (v.1 i)
  exact Equiv.prod_comp g.symm (fun i => M (w.1 i) (v.1 i))

lemma matrix_wordVector (M : Matrix (Words (S := S) odd k) (Words (S := S) odd k) ℂ)
    (w v : Words (S := S) odd k) :
    Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ) M (wordVector v) w = M w v := by
  change (∑ z, M w z * (if z=v then 1 else 0)) = M w v
  simp

lemma tensor_commutes_signed (M : Matrix C C ℂ) (heven : M ∈ evenAlgebra odd)
    (g : Equiv.Perm S) (x : Sector (S := S) odd k) :
    Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M)) (representation g x) =
    representation g (Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M)) x) := by
  let T := Matrix.toEuclideanCLM (n := Words (S := S) odd k) (𝕜 := ℂ)
      (sectorTensor odd k (fun _ : S => M))
  have hv (v : Words (S := S) odd k) : T (representation g (wordVector v)) = representation g (T (wordVector v)) := by
    ext z
    obtain ⟨w,rfl⟩ := (wordsEquiv g).surjective z
    change T (representation g (wordVector v)) (actWord g w) = representation g (T (wordVector v)) (actWord g w)
    rw [signedMap_wordVector, map_smul, signedMap_transport_apply]
    change CubeShuffle.Specht.permSign (oddPerm g v) * T (wordVector (actWord g v)) (actWord g w) =
      CubeShuffle.Specht.permSign (oddPerm g w) * T (wordVector v) w
    dsimp only [T]
    rw [matrix_wordVector, matrix_wordVector, sectorTensor_transport]
    by_cases hp : ∀ i, odd (w.1 i) ↔ odd (v.1 i)
    · rw [oddPerm_parity_congr g w v hp]
    · have hz : sectorTensor odd k (fun _ : S => M) w v=0 :=
        tensorMatrix_even_support odd _ (fun _ => heven) w.1 v.1 hp
      rw [hz, mul_zero, mul_zero]
  change T (representation g x) = representation g (T x)
  rw [← sum_wordVectors x]
  simp only [map_sum, map_smul, hv]

/-- The polynomial-dimensional tensor algebra commutes with the genuine
signed permutation representation, with no commutant-duality assumption. -/
theorem sectorAlgebra_commutes (a : sectorAlgebra (S := S) odd k)
    (g : Equiv.Perm S) (x : Sector (S := S) odd k) :
    (a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) (representation g x) = representation g ((a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) x) := by
  have ha := a.property
  change (a : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k) ∈
    (unitarySpan (R := ℂ) (sectorUnitary (S := S) odd k)).toSubmodule at ha
  rw [unitarySpan_eq_span] at ha
  suffices hh : ∀ b ∈ Submodule.span ℂ
      (Set.range fun U => ((sectorUnitary (S := S) odd k U).val : Sector (S := S) odd k →L[ℂ] Sector (S := S) odd k)),
      b (representation g x) = representation g (b x) from hh _ ha
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨U,rfl⟩ := hb
    dsimp only
    rw [sectorUnitary_apply]
    exact tensor_commutes_signed odd k U.val.val U.val.property g x
  | zero => simp
  | add b c hb hc ihb ihc => simp only [add_apply, map_add, ihb, ihc]
  | smul z b hb ih => simp only [smul_apply, map_smul, ih]
end RowColumn.MatrixState

end
end

end OAI

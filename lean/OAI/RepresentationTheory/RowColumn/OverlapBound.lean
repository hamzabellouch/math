import OAI.RepresentationTheory.RowColumn.Postselection
import OAI.RepresentationTheory.RowColumn.CopyOverlap

namespace OAI

section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.Signed
open MatrixState
variable {S C L K : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K]
    {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_toCLM (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (intertwinerMatrix l T) = T.toLinearMap.toContinuousLinearMap :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_trace (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l)) :
    (intertwinerMatrix l T).trace =
      LinearMap.trace ℂ (EuclideanSpace ℂ (Words (S := S) odd k)) T.toLinearMap := by
  rw [← trace_toEuclideanCLM, intertwinerMatrix_toCLM]
  rfl

omit [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
lemma intertwinerMatrix_product_trace (l : S → L) (r : S → K)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l))
    (U : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) r)
      (lineRepresentation (odd := odd) (k := k) r)) :
    (intertwinerMatrix l T * intertwinerMatrix r U).trace =
      LinearMap.trace ℂ (EuclideanSpace ℂ (Words (S := S) odd k)) (T.toLinearMap.comp U.toLinearMap) := by
  rw [← trace_toEuclideanCLM, map_mul, intertwinerMatrix_toCLM, intertwinerMatrix_toCLM]
  rfl

omit [Fintype L] [DecidableEq L] in
lemma intertwinerMatrix_filtered (l : S → L)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) l)
      (lineRepresentation (odd := odd) (k := k) l))
    (q : sectorAlgebra (S := S) odd k)
    (h : q.val * T.toLinearMap.toContinuousLinearMap=T.toLinearMap.toContinuousLinearMap) :
    algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix l T=intertwinerMatrix l T := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  rw [map_mul]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ)) (algebraMatrix (sectorAlgebra (S := S) odd k) q) *
    (Matrix.toEuclideanCLM (𝕜 := ℂ)) (intertwinerMatrix l T) =
    (Matrix.toEuclideanCLM (𝕜 := ℂ)) (intertwinerMatrix l T)
  rw [intertwinerMatrix_toCLM]
  change (Matrix.toEuclideanCLM (𝕜 := ℂ)) ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm q.val) * _ = _
  rw [StarAlgEquiv.apply_symm_apply]
  exact h

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.Signed
open MatrixState Postselection WordOrbits
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L]

def lineCost : ℕ := (Fintype.card S+1)^(Fintype.card L*Fintype.card C^2)
abbrev MixtureIndex := Types (S := S) (A := L × (C × C)) × Phases (L × (C × C)) (Fintype.card S)

omit [DecidableEq S] in
lemma phases_card : Fintype.card (Phases (L × (C × C)) (Fintype.card S)) = lineCost (S := S) (C := C) (L := L) := by
  simp only [Phases, Fintype.card_fun, ZMod.card, Fintype.card_prod, lineCost, pow_two]
omit [DecidableEq S] in
lemma types_card : Fintype.card (Types (S := S) (A := L × (C × C))) = lineCost (S := S) (C := C) (L := L) := by
  simp only [Types, CountIndex, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, lineCost, pow_two]
omit [DecidableEq S] in
lemma mixtureIndex_card : Fintype.card (MixtureIndex (S := S) (C := C) (L := L)) = lineCost (S := S) (C := C) (L := L)^2 := by
  simp only [MixtureIndex, Fintype.card_prod, types_card, phases_card, pow_two]
omit [DecidableEq S] [DecidableEq C] [DecidableEq L] in
lemma lineCost_pos : 0 < lineCost (S := S) (C := C) (L := L) := pow_pos (Nat.succ_pos _) _

variable (odd : C → Prop) [DecidablePred odd] (k : ℕ)

theorem signed_line_mixture (line : S → L) (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line)) (hT : T.toLinearMap.IsPositive) :
    intertwinerMatrix line T ≤
      ((lineCost (S := S) (C := C) (L := L) : ℝ) * (intertwinerMatrix line T).trace.re) •
        ∑ z : MixtureIndex (S := S) (C := C) (L := L),
          sectorTensor odd k (fun i => lineState line a₀ odd z.1 z.2 (line i)) := by
  have hz : (lineCost (S := S) (C := C) (L := L) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lineCost_pos (S := S) (C := C) (L := L)))
  have hh := signed_line_postselection odd k line a₀ hn T hT
  simp only [lineCost] at hz ⊢
  simpa only [Fintype.card_prod, ← pow_two, phases_card, lineCost, div_self hz, mul_one,
    Fintype.sum_prod_type] using hh

end RowColumn.Signed

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {I U V : Type*} [Fintype I] [DecidableEq I] [Fintype U] [Fintype V]

lemma filtered_trace_mono (A B A' B' Q : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hA' : A'.PosSemidef)
    (hQ : Q.IsHermitian) (hQA : Q*A=A) (hQB : Q*B=B)
    (hAA : A ≤ A') (hBB : B ≤ B') :
    (A*B).trace.re ≤ (A'*Q*B'*Q).trace.re := by
  have hAQ : A*Q=A := by
    have hh := congrArg Matrix.conjTranspose hQA
    simpa only [Matrix.conjTranspose_mul,hA.isHermitian.eq,hQ.eq] using hh
  have hBQ : B*Q=B := by
    have hh := congrArg Matrix.conjTranspose hQB
    simpa only [Matrix.conjTranspose_mul,hB.isHermitian.eq,hQ.eq] using hh
  have hp : (Q*A'*Q).PosSemidef := by
    simpa only [hQ.eq] using hA'.conjTranspose_mul_mul_same Q
  calc
    _ ≤ (A'*B).trace.re := trace_mul_mono A A' B hAA hB
    _ = (B*(Q*A'*Q)).trace.re := by
      symm
      simp only [← mul_assoc]
      rw [hBQ, Matrix.trace_mul_cycle, hQB, Matrix.trace_mul_comm]
    _ ≤ (B'*(Q*A'*Q)).trace.re := trace_mul_mono B B' _ hBB hp
    _ = _ := by
      calc
        _ = ((B'*Q)*(A'*Q)).trace.re := by simp only [mul_assoc]
        _ = ((A'*Q)*(B'*Q)).trace.re := congrArg Complex.re (Matrix.trace_mul_comm _ _)
        _ = _ := by simp only [mul_assoc]

lemma trace_filtered_smul_sum (a b : ℝ) (S : U → Matrix I I ℂ) (T : V → Matrix I I ℂ)
    (Q : Matrix I I ℂ) :
    ((a • ∑ i, S i)*Q*(b • ∑ j, T j)*Q).trace.re =
      a*b*∑ i, ∑ j, (S i*Q*T j*Q).trace.re := by
  simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum, Complex.re_sum, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_mixture_bound (A B Q : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hQ : Q.IsHermitian)
    (hQA : Q*A=A) (hQB : Q*B=B)
    (S : U → Matrix I I ℂ) (T : V → Matrix I I ℂ)
    (hS : ∀ i, (S i).PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAS : A ≤ a • ∑ i, S i) (hBT : B ≤ b • ∑ j, T j)
    (z : ℝ) (hz : ∀ i j, (S i*Q*T j*Q).trace.re ≤ z) :
    (A*B).trace.re ≤ a*b * ((Fintype.card U : ℝ)*Fintype.card V) * z := by
  have hS' : (∑ i, S i).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ => (hS i).nonneg)
  apply (filtered_trace_mono A B _ _ Q hA hB (hS'.smul ha)
    hQ hQA hQB hAS hBT).trans
  rw [trace_filtered_smul_sum]
  have hh := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hz i j
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg ha hb)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh'

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
open Signed Postselection WordOrbits FiniteStarAlgebra
variable {S C L K : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] [Nonempty S]

/-- Reconstruction of the occupied overlap for the actual signed row/column
commutants. The two trace factors retain every prescribed copy. -/
theorem occupied_commutant_trace (odd : C → Prop) [DecidablePred odd] (k : ℕ)
    (e : S ↪ L × K) (a₀ : S → C × C)
    (A : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) (fun i => (e i).1))
      (lineRepresentation (odd := odd) (k := k) (fun i => (e i).1)))
    (B : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) (fun i => (e i).2))
      (lineRepresentation (odd := odd) (k := k) (fun i => (e i).2)))
    (hA : A.toLinearMap.IsPositive) (hB : B.toLinearMap.IsPositive)
    (q : sectorAlgebra (S := S) odd k) (hqs : star q=q) (hqq : q*q=q) (hqc : ∀ a, q*a=a*q)
    (d : ℝ) (hd : 0<d)
    (hfilter : ∀ a : sectorAlgebra (S := S) odd k, a.val.IsPositive →
      ‖q*a‖ ≤ (physicalTrace (sectorAlgebra (S := S) odd k) a).re / d)
    (hQA : algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix (fun i => (e i).1) A =
      intertwinerMatrix (fun i => (e i).1) A)
    (hQB : algebraMatrix (sectorAlgebra (S := S) odd k) q * intertwinerMatrix (fun i => (e i).2) B =
      intertwinerMatrix (fun i => (e i).2) B) :
    (intertwinerMatrix (fun i => (e i).1) A * intertwinerMatrix (fun i => (e i).2) B).trace.re ≤
      16 * (lineCost (S := S) (C := C) (L := L) : ℝ)^3 *
        (lineCost (S := S) (C := C) (L := K) : ℝ)^3 *
        (Module.finrank ℂ (sectorAlgebra (S := S) odd k) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card K - Fintype.card S : ℕ) : ℝ) *
        (intertwinerMatrix (fun i => (e i).1) A).trace.re *
        (intertwinerMatrix (fun i => (e i).2) B).trace.re / d := by
  let l := fun i => (e i).1
  let r := fun i => (e i).2
  let M := fun z : MixtureIndex (S := S) (C := C) (L := L) => lineState l a₀ odd z.1 z.2
  let N := fun z : MixtureIndex (S := S) (C := C) (L := K) => lineState r a₀ odd z.1 z.2
  have hM z i : (M z i).PosSemidef := lineState_positive l a₀ odd z.1 z.2 i
  have hN z i : (N z i).PosSemidef := lineState_positive r a₀ odd z.1 z.2 i
  have heM z i : M z i ∈ evenAlgebra odd := lineState_even l a₀ odd z.1 z.2 i
  have heN z i : N z i ∈ evenAlgebra odd := lineState_even r a₀ odd z.1 z.2 i
  have htM z i : (M z i).trace.re ≤ 1 := lineState_trace l a₀ odd z.1 z.2 i
  have htN z i : (N z i).trace.re ≤ 1 := lineState_trace r a₀ odd z.1 z.2 i
  have hAp := intertwinerMatrix_positive l A hA
  have hBp := intertwinerMatrix_positive r B hB
  have hAS := signed_line_mixture odd k l a₀ Fintype.card_pos A hA
  have hBN := signed_line_mixture odd k r a₀ Fintype.card_pos B hB
  have hz z w := sector_filtered_trace_bound odd k e q hqs hqq hqc d hd hfilter
    (M z) (N w) (hM z) (hN w) (heM z) (heN w) (htM z) (htN w)
  have hh := trace_mixture_bound (intertwinerMatrix l A) (intertwinerMatrix r B)
    (algebraMatrix (sectorAlgebra (S := S) odd k) q) hAp hBp (algebraMatrix_hermitian _ q hqs)
    hQA hQB (fun z => sectorTensor odd k (fun i => M z (l i)))
    (fun w => sectorTensor odd k (fun i => N w (r i)))
    (fun z => sectorTensor_positive odd k _ (fun i => hM z (l i)))
    ((lineCost (S := S) (C := C) (L := L) : ℝ) * (intertwinerMatrix l A).trace.re)
    ((lineCost (S := S) (C := C) (L := K) : ℝ) * (intertwinerMatrix r B).trace.re)
    (mul_nonneg (Nat.cast_nonneg _) hAp.trace_nonneg.1)
    (mul_nonneg (Nat.cast_nonneg _) hBp.trace_nonneg.1) hAS hBN _ hz
  apply hh.trans_eq
  simp only [mixtureIndex_card, Nat.cast_pow]
  ring

end RowColumn.MatrixState

end
end


section

noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState FiniteStarAlgebra

variable {S L R V W : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] [Nonempty S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [DecidableEq S] in
/-- Actual hook-Specht all-copy overlap, with the concrete polynomial factors
before absorption into the one absolute constant. Orthogonality and completeness
are used later to bound the copy counts, not silently discarded from the main. -/
theorem actual_copy_overlap_bound (board : S ↪ L × R)
    (a : YoungDiagram) (e : S ≃ Cell a) (h : ℕ) (H : InHook a h) (c₀ : HookModel.Color h)
    {u v : ℕ}
    (ρ : Representation ℂ (lineGroup (fun i => (board i).1)) V)
    (τ : Representation ℂ (lineGroup (fun i => (board i).2)) W)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (I : Fin u → V →ₗᵢ[ℂ] hilbertSpace a) (J : Fin v → W →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := V) (W := hilbertSpace a) ρ
      ((relabelledUnitary a e).comp (lineGroup (fun i => (board i).1)).subtype) (I i).toLinearMap)
    (hJ : ∀ j, Intertwines (V := W) (W := hilbertSpace a) τ
      ((relabelledUnitary a e).comp (lineGroup (fun i => (board i).2)).subtype) (J j).toLinearMap) :
    allCopyOverlap (V := V) (W := W) (X := hilbertSpace a) I J ≤
      16 * (lineCost (S := Cell a) (C := HookModel.Color h) (L := L) : ℝ)^3 *
        (lineCost (S := Cell a) (C := HookModel.Color h) (L := R) : ℝ)^3 *
        (Module.finrank ℂ (sectorAlgebra (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) : ℝ)^2 *
        Real.exp ((Fintype.card L * Fintype.card R - Fintype.card S : ℕ) : ℝ) *
        (u * Module.finrank ℂ V : ℕ) * (v * Module.finrank ℂ W : ℕ) /
        Module.finrank ℂ (space a) := by
  let : Nonempty (Cell a) := ⟨e (Classical.choice (inferInstance : Nonempty S))⟩
  let := unitaryRepresentation_irreducible a
  obtain ⟨K,hK⟩ := exists_hook_isometry a h H
  let odd := HookModel.IsOdd (h := h)
  let k := HookModel.oddCount a h H
  let eb : Cell a ↪ L × R := e.symm.toEmbedding.trans board
  let KI := fun i => K.comp (I i)
  let KJ := fun j => K.comp (J j)
  have hr := hook_copy_projection_intertwines a e h H K hK (fun i => (board i).1) ρ hρ I hI
  have hc := hook_copy_projection_intertwines a e h H K hK (fun i => (board i).2) τ hτ J hJ
  let A : Representation.IntertwiningMap
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).1))
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).1)) :=
    { toLinearMap := (copyProjection KI).toLinearMap
      isIntertwining' g := by apply LinearMap.ext; intro x; exact hr g x }
  let B : Representation.IntertwiningMap
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).2))
      (lineRepresentation (odd := odd) (k := k) (fun i => (eb i).2)) :=
    { toLinearMap := (copyProjection KJ).toLinearMap
      isIntertwining' g := by apply LinearMap.ext; intro x; exact hc g x }
  have hAp : A.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr (copyProjection_positive KI)
  have hBp : B.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr (copyProjection_positive KJ)

  obtain ⟨q,hqs,hqq,hqc,hq,hfilter⟩ := exists_sector_isotypic_filter
    (V := hilbertSpace a) odd k (unitaryRepresentation a)

  rw [finrank_hilbertSpace] at hfilter
  have hd : (0 : ℝ) < Module.finrank ℂ (space a) := by
    have hdim : 0 < Module.finrank ℂ (space a) :=
      Submodule.one_le_finrank_iff.mpr (space_ne_bot a)
    exact_mod_cast hdim

  have filterCopies := isotypic_filter_copy_projection (G := Equiv.Perm (Cell a)) (V := V)
      (E := Sector (S := Cell a) odd k) (X := hilbertSpace a) (unitaryRepresentation a)
      (Signed.representation (S := Cell a) (odd := odd) (k := k)) K
  have filterCopiesIntertwining := filterCopies hK
  have filterCopiesOperator := filterCopiesIntertwining q.val
  have filterCopiesCarrier := filterCopiesOperator hq (u := u)
  have hKI := filterCopiesCarrier I
  have hA : A.toLinearMap.toContinuousLinearMap = copyProjection KI := by
    ext x
    rfl
  have hQA := intertwinerMatrix_filtered (fun i => (eb i).1) A q (by
    rw [hA]
    exact hKI)

  have filterColumnCopies := isotypic_filter_copy_projection (G := Equiv.Perm (Cell a)) (V := W)
      (E := Sector (S := Cell a) odd k) (X := hilbertSpace a) (unitaryRepresentation a)
      (Signed.representation (S := Cell a) (odd := odd) (k := k)) K
  have filterColumnIntertwining := filterColumnCopies hK
  have filterColumnOperator := filterColumnIntertwining q.val
  have filterColumnCarrier := filterColumnOperator hq (u := v)
  have hKJ := filterColumnCarrier J
  have hB : B.toLinearMap.toContinuousLinearMap = copyProjection KJ := by
    ext x
    rfl
  have hQB := intertwinerMatrix_filtered (fun i => (eb i).2) B q (by
    rw [hB]
    exact hKJ)


  have hh := occupied_commutant_trace odd k eb (fun _ => (c₀,c₀)) A B hAp hBp
    q hqs hqq hqc (Module.finrank ℂ (space a)) hd hfilter hQA hQB

  have hAt : (intertwinerMatrix (fun i => (eb i).1) A).trace = (u * Module.finrank ℂ V : ℕ) := by
    rw [intertwinerMatrix_trace]
    exact copyProjection_trace KI
  have hBt : (intertwinerMatrix (fun i => (eb i).2) B).trace = (v * Module.finrank ℂ W : ℕ) := by
    rw [intertwinerMatrix_trace]
    exact copyProjection_trace KJ
  rw [intertwinerMatrix_product_trace, hAt, hBt] at hh
  have hcard : Fintype.card (Cell a)=Fintype.card S := (Fintype.card_congr e).symm
  simp only [Complex.natCast_re, hcard] at hh
  have hinv := allCopyOverlap_comp_isometry (V := V) (W := W) (X := hilbertSpace a)
    (E := Sector (S := Cell a) odd k) I J K
  calc _ = allCopyOverlap (V := V) (W := W) (X := Sector (S := Cell a) odd k) KI KJ := hinv.symm
       _ ≤ _ := (allCopyOverlap_le_trace (V := V) (W := W)
         (X := Sector (S := Cell a) odd k) KI KJ).trans hh

end RowColumn

end
end

end OAI

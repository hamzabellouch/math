import OAI.RepresentationTheory.YoungSymmetry.UnitaryModel
import OAI.Probability.CubeShuffle.DimensionEstimates

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical

/-- Tail bound for any genuine factorial row-column lower bound. -/
theorem choose_tail_le_of_factorial (μ : YoungDiagram) (D : ℕ)
    (hd : μ.card.factorial ≤ D * Fintype.card (rowGroup μ) * Fintype.card (colGroup μ)) :
    μ.card.choose (μ.card-μ.rowLen 0) ≤ D * 2^(μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  have htail := card_fiberGroups_mul_le
    (fun x : Tail μ => rowIndex x.1) (fun x : Tail μ => colIndex x.1)
    (fun x y hr hc => Subtype.ext (Subtype.ext (Prod.ext (congrArg Fin.val hr) (congrArg Fin.val hc))))
  rw [tail_card] at htail
  have hc := column_group_le_tail μ
  have hr := tail_row_group μ
  simp only [←Nat.card_eq_fintype_card] at htail hc hr hd
  have hh : μ.card.factorial ≤ D * 2^j *
      ((μ.rowLen 0).factorial * j.factorial) := by
    calc
      _ ≤ _ := hd
      _ ≤ D * Nat.card (rowGroup μ) *
          (2^j * Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := Nat.mul_le_mul_left _ hc
      _ = D * 2^j * (μ.rowLen 0).factorial *
          (Nat.card (fiberGroup (fun x : Tail μ => rowIndex x.1)) *
           Nat.card (fiberGroup (fun x : Tail μ => colIndex x.1))) := by rw [←hr]; ring
      _ ≤ _ := by
        calc
          _ ≤ D * 2^j * (μ.rowLen 0).factorial * j.factorial :=
            Nat.mul_le_mul_left _ htail
          _ = _ := by ring
  have hj : j ≤ μ.card := Nat.sub_le _ _
  have hs : μ.card-j = μ.rowLen 0 := by dsimp [j]; have := rowLen_zero_le_card μ; omega
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  rw [hs] at hf
  rw [←hf] at hh
  have hpos : 0 < (μ.rowLen 0).factorial * j.factorial := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith


lemma card_rowGroup_transpose (μ : YoungDiagram) :
    Fintype.card (rowGroup μ.transpose) = Fintype.card (colGroup μ) := by
  rw [card_rowGroup,card_colGroup]
  apply Fintype.prod_equiv (finCongr (μ.colLen_transpose 0))
  intro i
  change (μ.transpose.rowLen i).factorial = (μ.colLen i).factorial
  rw [YoungDiagram.rowLen_transpose]

lemma card_colGroup_transpose (μ : YoungDiagram) :
    Fintype.card (colGroup μ.transpose) = Fintype.card (rowGroup μ) := by
  rw [card_colGroup,card_rowGroup]
  apply Fintype.prod_equiv (finCongr (μ.rowLen_transpose 0))
  intro i
  change (μ.transpose.colLen i).factorial = (μ.rowLen i).factorial
  rw [YoungDiagram.colLen_transpose]

lemma card_transpose (μ : YoungDiagram) : μ.transpose.card=μ.card := by
  unfold YoungDiagram.card YoungDiagram.transpose
  exact Finset.card_map _

/-- Near-column dimension without assuming transpose invariance of Specht dimensions. -/
theorem choose_column_tail_le_dimension (μ : YoungDiagram) :
    μ.card.choose (μ.card-μ.colLen 0) ≤ Module.finrank ℂ (space μ) * 2^(μ.card-μ.colLen 0) := by
  have hd := factorial_le_dimension_row_column μ
  have ht := choose_tail_le_of_factorial μ.transpose (Module.finrank ℂ (space μ))
  simp only [card_transpose,card_rowGroup_transpose,card_colGroup_transpose,YoungDiagram.rowLen_transpose] at ht
  apply ht
  nlinarith

end CubeShuffle.Specht
namespace CubeShuffle.Specht
open scoped BigOperators Classical
open DimensionEstimates Filter

lemma dimension_log_incidence (μ : YoungDiagram) (hμ : 0<μ.card) :
    (2*Real.log 2-1)*(μ.card:ℝ)-Real.log 2*((μ.rowLen 0:ℝ)+μ.colLen 0)+1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let : Nonempty (Cell μ) := Fintype.card_pos_iff.mp (by simpa only [card_cell] using hμ)
  have hd := factorial_le_dimension_row_column μ
  rw [card_rowGroup,card_colGroup] at hd
  have hr (i : Fin (μ.colLen 0)) : Nat.card {x : Cell μ // rowIndex x=i}=μ.rowLen i := by
    let e : {x : Cell μ // rowIndex x=i} ≃ {x : Cell μ // row x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (rowEquiv μ i),Nat.card_fin]
  have hc (i : Fin (μ.rowLen 0)) : Nat.card {x : Cell μ // colIndex x=i}=μ.colLen i := by
    let e : {x : Cell μ // colIndex x=i} ≃ {x : Cell μ // col x=i} :=
      Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
    rw [Nat.card_congr e,Nat.card_congr (columnEquiv μ i),Nat.card_fin]
  have hcell : Nat.card (Cell μ)=μ.card := by rw [Nat.card_eq_fintype_card,card_cell]
  have h := dimension_log_from_incidence (rowIndex (μ := μ)) (colIndex (μ := μ))
    (fun x y h => Subtype.ext (Prod.ext (congrArg (fun z => (z.1:ℕ)) h)
      (congrArg (fun z => (z.2:ℕ)) h))) (Module.finrank ℂ (space μ))
    (by simpa only [←Nat.card_eq_fintype_card,hr,hc,hcell] using hd)
  simpa only [card_cell,Fintype.card_fin,add_comm (μ.colLen 0:ℝ)] using h

/-- Uniform dimension dichotomy. The proof only uses the proved factorial
incidence bound and the proved tail binomial bound, not a tableau-count axiom. -/
lemma medium_dimension_raw (μ : YoungDiagram) (hμ : 0<μ.card) (δ : ℝ) (hδ : 0<δ)
    (hδ2 : δ≤1/2) (hrow : δ*(μ.card:ℝ)≤μ.card-μ.rowLen 0)
    (hcol : (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2) :
    min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)*(μ.card:ℝ)-2*Real.log μ.card-1≤
      Real.log (Module.finrank ℂ (space μ)) := by
  let c := (3/2:ℝ)*Real.log 2-1
  have hN : (0:ℝ)<μ.card := by exact_mod_cast hμ
  have hlog : 0≤Real.log μ.card := Real.log_nonneg (by exact_mod_cast hμ)
  have hc : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hr := rowLen_zero_le_card μ
  have hcl : μ.colLen 0≤μ.card := by
    simpa only [YoungDiagram.rowLen_transpose,card_transpose] using rowLen_zero_le_card μ.transpose
  by_cases hsum : (μ.rowLen 0:ℝ)+μ.colLen 0≤(μ.card:ℝ)/2
  · have hi := dimension_log_incidence μ hμ
    have hm := mul_le_mul_of_nonneg_right (min_le_left c (entropyGap*δ)) hN.le
    dsimp [c] at hm
    nlinarith
  · have hbig : (μ.card:ℝ)/4≤μ.rowLen 0 ∨ (μ.card:ℝ)/4≤μ.colLen 0 := by
      by_contra h
      push Not at h
      linarith
    rcases hbig with hrb | hcb
    · have hj : 0<μ.card-μ.rowLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hr]
        exact lt_of_lt_of_le (mul_pos hδ hN) hrow
      have hjN : μ.card-μ.rowLen 0<μ.card := by
        have : 0<μ.rowLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.rowLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.rowLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hr]; linarith) (choose_tail_le_dimension μ)
      rw [Nat.cast_sub hr] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      nlinarith [entropyGap_pos]
    · have hj : 0<μ.card-μ.colLen 0 := by
        rw [←Nat.cast_pos (α := ℝ),Nat.cast_sub hcl]
        linarith
      have hjN : μ.card-μ.colLen 0<μ.card := by
        have : 0<μ.colLen 0 := by exact_mod_cast (by linarith : (0:ℝ)<μ.colLen 0)
        omega
      have hi := log_dimension_from_binomial μ.card (μ.card-μ.colLen 0)
        (Module.finrank ℂ (space μ)) hj hjN
        (by rw [Nat.cast_sub hcl]; linarith) (choose_column_tail_le_dimension μ)
      rw [Nat.cast_sub hcl] at hi
      have hm := mul_le_mul_of_nonneg_right (min_le_right c (entropyGap*δ)) hN.le
      have ht := mul_le_mul_of_nonneg_left (show δ*(μ.card:ℝ)≤(μ.card:ℝ)-μ.colLen 0 by nlinarith) entropyGap_pos.le
      linarith

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open DimensionEstimates Filter

/-- Genuine uniform exponential dimension growth off the near-row regime;
tall columns are handled by the separate, exactly proved killing theorem. -/
theorem medium_dimension (δ : ℝ) (hδ : 0<δ) (hδ2 : δ≤1/2) :
    ∃ h : ℝ, 0<h ∧ ∀ᶠ N : ℕ in atTop, ∀ μ : YoungDiagram, μ.card=N →
      δ*(N:ℝ)≤N-μ.rowLen 0 → (μ.colLen 0:ℝ)≤(N:ℝ)/2 →
      h*(N:ℝ)≤Real.log (Module.finrank ℂ (space μ)) := by
  let a := min ((3/2:ℝ)*Real.log 2-1) (entropyGap*δ)
  have ha : 0<a := by
    apply lt_min
    · nlinarith [Real.log_two_gt_d9]
    · exact mul_pos entropyGap_pos hδ
  refine ⟨a/2,by positivity,?_⟩
  filter_upwards [log_error_eventually a ha,eventually_ge_atTop 1] with N hN hn
  intro μ hμ hr hc
  have hp : 0<μ.card := by omega
  have hh := medium_dimension_raw μ hp δ hδ hδ2 (by simpa only [hμ] using hr) (by simpa only [hμ] using hc)
  rw [hμ] at hh
  change a*(N:ℝ)-2*Real.log N-1≤_ at hh
  linarith

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical

lemma partition_count (N : ℕ) : Fintype.card (Nat.Partition N)≤2^N := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition N) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le N 1))

lemma shapes_count (N : ℕ) : Fintype.card (Shapes N)≤2^N := by
  rw [Fintype.card_congr (shapePartitionEquiv N)]
  exact partition_count N

lemma rowLens_headD (μ : YoungDiagram) : μ.rowLens.headD 0=μ.rowLen 0 := by
  cases he : μ.rowLens with
  | nil =>
    have hc := sum_rowLens μ
    rw [he,List.sum_nil] at hc
    have hr := rowLen_zero_le_card μ
    simp only [List.headD_nil]
    omega
  | cons a l =>
    have hh := YoungDiagram.get_rowLens (μ := μ) (i := 0) (h := by simp [he])
    simpa only [he,List.getElem_cons_zero,List.headD_cons] using hh

lemma rowLens_tail_sum (μ : YoungDiagram) : μ.rowLens.tail.sum=μ.card-μ.rowLen 0 := by
  have hh := rowLens_headD μ
  have hc := sum_rowLens μ
  cases he : μ.rowLens with
  | nil => simp only [he,List.headD_nil] at hh; simp only [he,List.sum_nil] at hc; simp [←hc]
  | cons a l =>
    simp only [he,List.headD_cons] at hh
    simp only [he,List.sum_cons] at hc
    simp only [List.tail_cons]
    omega

lemma positive_list_eq_of_tail_sum {a b : List ℕ}
    (ha : ∀ x∈a, 0<x) (hb : ∀ x∈b, 0<x) (ht : a.tail=b.tail) (hs : a.sum=b.sum) : a=b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x l =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := hb x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
  | cons x l =>
    cases b with
    | nil =>
      simp only [List.tail_nil,List.tail_cons] at ht
      subst l
      have hx := ha x (by simp)
      simp only [List.sum_nil,List.sum_cons,add_zero] at hs
      omega
    | cons y m =>
      simp only [List.tail_cons] at ht
      subst m
      simp only [List.sum_cons] at hs
      congr 1
      omega

abbrev TailShapes (N j : ℕ) := {μ : Shapes N // μ.1.card-μ.1.rowLen 0=j}

noncomputable def tailShapePartition (N j : ℕ) (μ : TailShapes N j) : Nat.Partition j where
  parts := μ.1.1.rowLens.tail
  parts_pos := fun {x} hx => μ.1.1.pos_of_mem_rowLens x (List.mem_of_mem_tail (by simpa using hx))
  parts_sum := by simpa using (rowLens_tail_sum μ.1.1).trans μ.2

lemma tailShapePartition_injective (N j : ℕ) : Function.Injective (tailShapePartition N j) := by
  intro μ ν he
  have hh : (μ.1.1.rowLens.tail : Multiset ℕ)=(ν.1.1.rowLens.tail : Multiset ℕ) :=
    congrArg Nat.Partition.parts he
  have ht : μ.1.1.rowLens.tail=ν.1.1.rowLens.tail := by
    have hm := congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·)) hh
    simpa only [Multiset.coe_sort,
      List.mergeSort_eq_self _ μ.1.1.rowLens_sorted.pairwise.tail,
      List.mergeSort_eq_self _ ν.1.1.rowLens_sorted.pairwise.tail] using hm
  have hl := positive_list_eq_of_tail_sum (μ.1.1.pos_of_mem_rowLens) (ν.1.1.pos_of_mem_rowLens)
    ht (by rw [sum_rowLens,sum_rowLens,μ.1.2,ν.1.2])
  apply Subtype.ext
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext hl

lemma tail_shapes_count (N j : ℕ) : Fintype.card (TailShapes N j)≤2^j := by
  exact (Fintype.card_le_of_injective _ (tailShapePartition_injective N j)).trans (partition_count j)

end CubeShuffle.Specht

end OAI

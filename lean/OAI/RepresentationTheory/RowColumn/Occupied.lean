import OAI.RepresentationTheory.RowColumn.OverlapBound
import OAI.Probability.CubeShuffle.FourierBound

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

/-- Absorption of the exact polynomial loss into the absolute occupied-board
constant. This is used for both halves of the min. -/
lemma occupied_numeric_absorb (m n h s : ℕ) (hh : 1 ≤ h) (hs : s ≤ m*n) :
    16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-s : ℕ) : ℝ) ≤
      Real.exp (128 * (((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 * Real.log ((m*n : ℕ)+2) +
        (m*n-s : ℕ))) := by
  let N : ℝ := (m*n : ℕ)+2
  let E : ℕ := (16*(m+n)+8)*h^2
  have hN : 2 ≤ N := by dsimp [N]; have := (Nat.cast_nonneg (m*n) : (0 : ℝ) ≤ (m*n : ℕ)); linarith
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hb : 0 ≤ (s : ℝ)+1 := by positivity
  have hbs : (s : ℝ)+1 ≤ N := by dsimp [N]; exact_mod_cast (by omega : s+1 ≤ m*n+2)
  have h16 : (16 : ℝ) ≤ N^4 := by
    calc 16 = (2 : ℝ)^4 := by norm_num
         _ ≤ N^4 := pow_le_pow_left₀ (by norm_num) hN _
  have hp : 16 * ((s : ℝ)+1)^E ≤ N^(E+4) := by
    calc _ ≤ N^4 * N^E := mul_le_mul h16 (pow_le_pow_left₀ hb hbs _) (by positivity) (by positivity)
         _ = N^(E+4) := by rw [pow_add]; ring
  have hh2 : (1 : ℝ) ≤ (h : ℝ)^2 := by exact_mod_cast (Nat.one_le_pow 2 h hh)
  have he : ((E+4 : ℕ) : ℝ) ≤ 128*((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 := by
    dsimp [E]
    push_cast
    nlinarith [sq_nonneg (h : ℝ), mul_nonneg (show 0 ≤ (m:ℝ)+(n:ℝ) by positivity) (sq_nonneg (h:ℝ))]
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht : (0 : ℝ) ≤ (m*n-s : ℕ) := Nat.cast_nonneg _
  have hexp : N^(E+4) = Real.exp (((E+4 : ℕ) : ℝ)*Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hNp]
  change 16 * ((s : ℝ)+1)^E * Real.exp ((m*n-s : ℕ) : ℝ) ≤ _
  calc
    _ ≤ N^(E+4) * Real.exp ((m*n-s : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (((E+4 : ℕ) : ℝ)*Real.log N + (m*n-s : ℕ)) := by rw [hexp, Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change ((E+4 : ℕ) : ℝ)*Real.log N + (m*n-s : ℕ) ≤
        128 * (((m+n+1 : ℕ) : ℝ)*(h : ℝ)^2 * Real.log N + (m*n-s : ℕ))
      nlinarith [mul_le_mul_of_nonneg_right he hl]

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

lemma occupied_factor_bound (s m n h u v D : ℕ) (t : ℝ)
    (hu : u ≤ (s+1)^(4*m*h^2)) (hv : v ≤ (s+1)^(4*n*h^2))
    (hD : D ≤ (s+1)^(4*h^2)) :
    16 * ((s+1 : ℕ) : ℝ)^(4*m*h^2*3) * ((s+1 : ℕ) : ℝ)^(4*n*h^2*3) *
      (D : ℝ)^2 * Real.exp t * u * v ≤
    16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp t := by
  have hu' : (u : ℝ) ≤ ((s : ℝ)+1)^(4*m*h^2) := by exact_mod_cast hu
  have hv' : (v : ℝ) ≤ ((s : ℝ)+1)^(4*n*h^2) := by exact_mod_cast hv
  have hD' : (D : ℝ) ≤ ((s : ℝ)+1)^(4*h^2) := by exact_mod_cast hD
  calc
    _ ≤ 16 * ((s : ℝ)+1)^(4*m*h^2*3) * ((s : ℝ)+1)^(4*n*h^2*3) *
      (((s : ℝ)+1)^(4*h^2))^2 * Real.exp t * ((s : ℝ)+1)^(4*m*h^2) *
      ((s : ℝ)+1)^(4*n*h^2) := by
        push_cast
        gcongr
    _ = _ := by
      rw [show (16*(m+n)+8)*h^2 = 4*m*h^2*3 + 4*n*h^2*3 + (4*h^2)*2 + 4*m*h^2 + 4*n*h^2 by ring]
      simp only [pow_add, pow_mul]
      ring

lemma occupied_count_bound (s m n h u v : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hu : u ≤ (s+1)^(4*m*h^2)) (hv : v ≤ (s+1)^(4*n*h^2)) :
    (u : ℝ)*v ≤ 16 * ((s : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp t := by
  have huv : (u : ℝ)*v ≤ ((s : ℝ)+1)^(4*(m+n)*h^2) := by
    have hu' : (u : ℝ) ≤ ((s : ℝ)+1)^(4*m*h^2) := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ ((s : ℝ)+1)^(4*n*h^2) := by exact_mod_cast hv
    calc _ ≤ ((s : ℝ)+1)^(4*m*h^2) * ((s : ℝ)+1)^(4*n*h^2) :=
            mul_le_mul hu' hv' (by positivity) (by positivity)
         _ = _ := by rw [← pow_add]; congr 1; ring
  have he : 4*(m+n)*h^2 ≤ (16*(m+n)+8)*h^2 := Nat.mul_le_mul_right _ (by omega)
  have hb : 1 ≤ (s : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) s; linarith
  have hp := pow_le_pow_right₀ hb he
  have hx : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hbase : 0 ≤ ((s : ℝ)+1)^((16*(m+n)+8)*h^2) := by positivity
  calc _ ≤ ((s : ℝ)+1)^((16*(m+n)+8)*h^2) := huv.trans hp
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hx hbase]

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht Signed MatrixState

lemma irreducible_nontrivial {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] : Nontrivial V := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  exact ρ.asModuleEquiv.symm.toEquiv.nontrivial

lemma empty_hook_dimension_le (a : YoungDiagram) (h : ℕ) (H : InHook a h)
    (ha : Fintype.card (Cell a)=0) : Module.finrank ℂ (space a) ≤ 1 := by
  have hi := LinearMap.finrank_le_finrank_of_injective (HookModel.hookEmbedding_injective a h H)
  change Module.finrank ℂ (space a) ≤
    Module.finrank ℂ (EuclideanSpace ℂ (Words (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))) at hi
  rw [finrank_euclideanSpace] at hi
  calc _ ≤ Fintype.card (Words (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H)) := hi
       _ ≤ Fintype.card (Cell a → HookModel.Color h) := Fintype.card_subtype_le _
       _ = 1 := by rw [Fintype.card_fun, ha, pow_zero]

lemma hook_lineCost {S L : Type*} [Fintype S] [Fintype L] (h : ℕ) :
    lineCost (S := S) (C := HookModel.Color h) (L := L) =
      (Fintype.card S+1)^(4*Fintype.card L*h^2) := by
  simp only [lineCost, HookModel.Color, Fintype.card_sum, Fintype.card_fin]
  congr 1
  ring

lemma hook_sectorAlgebra_bound {S : Type*} [Fintype S] [DecidableEq S] (h k : ℕ) :
    Module.finrank ℂ (sectorAlgebra (S := S) (HookModel.IsOdd (h := h)) k) ≤
      (Fintype.card S+1)^(4*h^2) := by
  have hh := sectorAlgebra_finrank (S := S) (HookModel.IsOdd (h := h)) k
  simpa only [HookModel.Color, Fintype.card_sum, Fintype.card_fin, show (h+h)^2=4*h^2 by ring] using hh

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

/-- The dimension-ratio half of the occupied main, now for the literal occupied
subset and all prescribed row and column embeddings. -/
theorem occupied_dimension_ratio (m n : ℕ) (Ω : Finset (Board m n)) [Nonempty Ω]
    (a : YoungDiagram) (e : Ω ≃ Cell a) (h : ℕ) (hh : 1 ≤ h) (H : InHook a h)
    (r c u v : ℕ)
    (ρ : Representation ℂ (rowGroup Ω) (EuclideanSpace ℂ (Fin r)))
    (τ : Representation ℂ (columnGroup Ω) (EuclideanSpace ℂ (Fin c)))
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ)
    (I : Fin u → EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] hilbertSpace a)
    (J : Fin v → EuclideanSpace ℂ (Fin c) →ₗᵢ[ℂ] hilbertSpace a)
    (hI : ∀ i, Intertwines (V := EuclideanSpace ℂ (Fin r)) (W := hilbertSpace a)
      ρ ((relabelledUnitary a e).comp (rowGroup Ω).subtype) (I i).toLinearMap)
    (hJ : ∀ i, Intertwines (V := EuclideanSpace ℂ (Fin c)) (W := hilbertSpace a)
      τ ((relabelledUnitary a e).comp (columnGroup Ω).subtype) (J i).toLinearMap)
    (hu : u ≤ (Ω.card+1)^(4*m*h^2)) (hv : v ≤ (Ω.card+1)^(4*n*h^2)) :
    allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤
      (16 * ((Ω.card : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-Ω.card : ℕ) : ℝ)) *
        ((r : ℝ)*c / Module.finrank ℂ (space a)) := by
  let board : Ω ↪ Fin m × Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  let c₀ : HookModel.Color h := Sum.inl ⟨0, by omega⟩
  have ha := actual_copy_overlap_bound (V := EuclideanSpace ℂ (Fin r))
    (W := EuclideanSpace ℂ (Fin c)) board a e h H c₀ ρ τ hρ hτ I J hI hJ
  have hc : Fintype.card (Cell a) = Ω.card := (Fintype.card_congr e).symm.trans (Fintype.card_coe Ω)
  have hD := hook_sectorAlgebra_bound (S := Cell a) h (HookModel.oddCount a h H)
  rw [hc] at hD
  let D := Module.finrank ℂ (sectorAlgebra (S := Cell a) (HookModel.IsOdd (h := h)) (HookModel.oddCount a h H))
  have hp := occupied_factor_bound Ω.card m n h u v D ((m*n-Ω.card : ℕ) : ℝ) hu hv hD
  have hratio : 0 ≤ (r : ℝ)*c / (Module.finrank ℂ (space a) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hp hratio
  simp only [hook_lineCost, hc, Fintype.card_fin, Fintype.card_coe, finrank_euclideanSpace,
    Nat.cast_mul, Nat.cast_pow, ← pow_mul] at ha
  apply ha.trans
  convert hmul using 1; dsimp [D]; ring

end RowColumn

end
end


section

noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.Specht CubeShuffle.UnitaryFinite Signed MatrixState

/-- `thm:occupied` (weighted.tex:76–84), including the empty occupied subset,
arbitrary deletion layout and every orthogonal multiplicity copy. The absolute
constant is 128; dimensions, unnormalized trace and operator norm are literal. -/
theorem occupied_overlap_endpoint : OccupiedOverlapEndpoint := by
  refine ⟨128, by norm_num, ?_⟩
  intro m n Ω a e h hh hN H r c u v ρ τ hirρ hirτ hρ hτ I J hI hJ
  let : Representation.IsIrreducible ρ := hirρ
  let : Representation.IsIrreducible τ := hirτ
  let : Nontrivial (EuclideanSpace ℂ (Fin r)) := irreducible_nontrivial ρ
  let : Nontrivial (EuclideanSpace ℂ (Fin c)) := irreducible_nontrivial τ

  have hu : u ≤ (Ω.card+1)^(4*m*h^2) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      hook_line_copy_count (V := EuclideanSpace ℂ (Fin r)) (fun x : Ω => x.1.1) a e h H ρ hρ I hI
  have hv : v ≤ (Ω.card+1)^(4*n*h^2) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      hook_line_copy_count (V := EuclideanSpace ℂ (Fin c)) (fun x : Ω => x.1.2) a e h H τ hτ J hJ

  let loss : ℝ := 16 * ((Ω.card : ℝ)+1)^((16*(m+n)+8)*h^2) * Real.exp ((m*n-Ω.card : ℕ) : ℝ)
  let ratio : ℝ := (r : ℝ)*c / Module.finrank ℂ (space a)
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity

  have hplain : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss :=
    (@allCopyOverlap_le_count (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin c))
      (hilbertSpace a) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance u v I J).trans
      (occupied_count_bound Ω.card m n h u v ((m*n-Ω.card : ℕ) : ℝ) (Nat.cast_nonneg _) hu hv)

  have hdim : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss * ratio := by
    by_cases hΩ : Ω.Nonempty
    · obtain ⟨x,hx⟩ := hΩ
      let : Nonempty Ω := ⟨⟨x,hx⟩⟩
      exact occupied_dimension_ratio m n Ω a e h hh H r c u v ρ τ hρ hτ I J hI.1 hJ.1 hu hv
    · have hempty : Ω=∅ := Finset.not_nonempty_iff_eq_empty.mp hΩ
      have ha : Fintype.card (Cell a)=0 := by
        rw [← Fintype.card_congr e, Fintype.card_coe, hempty, Finset.card_empty]
      have hd : (Module.finrank ℂ (space a) : ℝ) ≤ 1 := by exact_mod_cast empty_hook_dimension_le a h H ha
      have hdpos : (0 : ℝ) < Module.finrank ℂ (space a) := by exact_mod_cast dimension_pos a
      have hr : (1 : ℝ) ≤ r := by
        have hh : 0 < Module.finrank ℂ (EuclideanSpace ℂ (Fin r)) := Module.finrank_pos
        simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
        exact_mod_cast hh
      have hc : (1 : ℝ) ≤ c := by
        have hh : 0 < Module.finrank ℂ (EuclideanSpace ℂ (Fin c)) := Module.finrank_pos
        simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
        exact_mod_cast hh
      have hrc : 1 ≤ ratio := by
        dsimp [ratio]
        apply (le_div_iff₀ hdpos).mpr
        simp only [one_mul]
        exact hd.trans (one_le_mul_of_one_le_of_one_le hr hc)
      exact hplain.trans (by simpa using mul_le_mul_of_nonneg_left hrc hloss)

  have hmin : allCopyOverlap (V := EuclideanSpace ℂ (Fin r)) (W := EuclideanSpace ℂ (Fin c))
      (X := hilbertSpace a) I J ≤ loss * min 1 ratio := by
    by_cases hx : ratio ≤ 1
    · rw [min_eq_right hx]; exact hdim
    · rw [min_eq_left (le_of_not_ge hx), mul_one]; exact hplain

  have hs : Ω.card ≤ m*n := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Finset.card_le_univ Ω
  have hbound := occupied_numeric_absorb m n h Ω.card hh hs

  exact hmin.trans (mul_le_mul_of_nonneg_right hbound (le_min (by norm_num) hratio))

end RowColumn

end
end

/-- The occupied row-column overlap bound. -/
theorem RowColumn.occupied_overlap : RowColumn.OccupiedOverlapEndpoint :=
  RowColumn.occupied_overlap_endpoint

end OAI

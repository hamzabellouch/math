import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionRest

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.propDecidable
variable {E:Type} [Fintype E] [DecidableEq E] (m:E → ℕ)

lemma fusionWeight_split (e:E) (L:FusionLabel m) :
    fusionWeight m L = stringWeight (m e) (L e) *
      fusionWeight (fun f:FusionRest e=>m f) (restLabel m e L) :=
  Fintype.prod_eq_mul_prod_subtype_ne (fun f=>stringWeight (m f) (L f)) e

lemma fusionWeight_join (e:E) (r:FusionLabel (fun f:FusionRest e=>m f)) (j:StringLabel (m e)) :
    fusionWeight m ((labelSplit m e).symm (r,j)) =
      stringWeight (m e) j * fusionWeight (fun f:FusionRest e=>m f) r := by
  rw [fusionWeight_split m e]
  have h := (labelSplit m e).apply_symm_apply (r,j)
  change (restLabel m e ((labelSplit m e).symm (r,j)),((labelSplit m e).symm (r,j)) e)=(r,j) at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  rw [h₁,h₂]

lemma finitePi_update_constant {α:E → Type*} {B:Type*} (f:((i:E) → α i) → B)
    (hf:∀ x i a,f (Function.update x i a)=f x) (x y:(i:E) → α i) : f x=f y := by
  have hh (s:Finset E) : ∀ x y:(i:E) → α i, (∀ i,i ∉ s → x i=y i) → f x=f y := by
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      exact congrArg f (funext fun i=>h i (Finset.notMem_empty i))
    | @insert i s hi ih =>
      intro x y h
      calc
        f x = f (Function.update x i (y i)) := (hf x i (y i)).symm
        _ = f y := ih _ _ (by
          intro j hj
          by_cases he:j=i
          · subst j; exact Function.update_self _ _ _
          · rw [Function.update_of_ne he]
            exact h j (by simp [he,hj]))
  exact hh Finset.univ x y (by simp)

lemma fusion_slice_proportional (hm:∀ e,2 ≤ m e) (f:FusionLabel m → ℝ)
    (hf:∀ L,0≤f L)
    (hs:∀ e (r:FusionLabel (fun g:FusionRest e=>m g)), ∃ c:ℝ, ∀ j,
      f ((labelSplit m e).symm (r,j))=c*stringWeight (m e) j) :
    ∃ c:ℝ, 0≤c ∧ ∀ L,f L=c*fusionWeight m L := by
  let L₀ : FusionLabel m := fun e=>⟨0,by have := hm e; omega⟩
  let g (L:FusionLabel m) := f L / fusionWeight m L
  have hg (L:FusionLabel m) (i:E) (j:StringLabel (m i)) : g (Function.update L i j)=g L := by
    let r := restLabel m i L
    obtain ⟨c,hc⟩ := hs i r
    have he (a:StringLabel (m i)) :
        g ((labelSplit m i).symm (r,a)) = c / fusionWeight (fun t:FusionRest i=>m t) r := by
      dsimp [g]
      rw [hc,fusionWeight_join]
      have hw := ne_of_gt (stringWeight_pos (hm i) a)
      have hr := ne_of_gt (fusionWeight_pos (fun t:FusionRest i=>m t) (fun t=>hm t) r)
      field_simp
    have hx : (labelSplit m i).symm (r,L i)=L := (labelSplit m i).symm_apply_apply L
    have hy : (labelSplit m i).symm (r,j)=Function.update L i j := by
      apply (labelSplit m i).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · funext t
        exact (Function.update_of_ne t.property _ _).symm
      · change j = Function.update L i j i
        exact (Function.update_self i j L).symm
    exact (congrArg g hy.symm).trans ((he j).trans ((he (L i)).symm.trans (congrArg g hx)))
  refine ⟨g L₀,div_nonneg (hf L₀) (le_of_lt (fusionWeight_pos m hm L₀)),fun L=>?_⟩
  have h := finitePi_update_constant (E:=E) g hg L L₀
  dsimp [g] at h ⊢
  exact (div_eq_iff (ne_of_gt (fusionWeight_pos m hm L))).mp h

lemma fusion_weighted_matrix_proportional (hm:∀ e,2 ≤ m e)
    (B:FusionLabel m → FusionLabel m → ℕ)
    (hB:∀ e (r t:FusionLabel (fun g:FusionRest e=>m g)), ∃ c:ℝ, ∀ j,
      (∑ i, stringWeight (m e) i *
        (B ((labelSplit m e).symm (t,i)) ((labelSplit m e).symm (r,j)):ℝ))=
          c*stringWeight (m e) j) :
    ∃ c:ℝ,0≤c ∧ ∀ L,
      (∑ H,fusionWeight m H*(B H L:ℝ))=c*fusionWeight m L := by
  apply fusion_slice_proportional m hm (fun L=>∑ H,fusionWeight m H*(B H L:ℝ))
  · intro L
    exact Finset.sum_nonneg fun H _=>mul_nonneg (le_of_lt (fusionWeight_pos m hm H)) (Nat.cast_nonneg _)
  · intro e r
    choose c hc using hB e r
    refine ⟨∑ t,fusionWeight (fun g:FusionRest e=>m g) t*c t,fun j=>?_⟩
    rw [← (labelSplit m e).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [fusionWeight_join]
    calc
      _ = ∑ t,fusionWeight (fun g:FusionRest e=>m g) t *
          (∑ i,stringWeight (m e) i * (B ((labelSplit m e).symm (t,i)) ((labelSplit m e).symm (r,j)):ℝ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp_rw [hc]; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _; ring

end HarmonicArtin

end OAI

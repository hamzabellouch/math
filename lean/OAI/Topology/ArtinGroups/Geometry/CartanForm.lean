import Mathlib
import OAI.Topology.ArtinGroups.Geometry.CartanOffNonpos
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

noncomputable def cartanForm (M:CoxeterMatrix S) (x y:S→ℝ) : ℝ := x ⬝ᵥ (cartan M *ᵥ y)

lemma cartanForm_symm (M:CoxeterMatrix S) (x y:S→ℝ) : cartanForm M x y=cartanForm M y x := by
  simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma cartanForm_single_left (M:CoxeterMatrix S) (i:S) (x:S→ℝ) :
    cartanForm M (Pi.single i 1) x=(cartan M *ᵥ x) i := by
  simp [cartanForm]

lemma cartanForm_single_right (M:CoxeterMatrix S) (x:S→ℝ) (i:S) :
    cartanForm M x (Pi.single i 1)=(cartan M *ᵥ x) i := by
  rw [cartanForm_symm,cartanForm_single_left]

lemma cartanForm_reflection (M:CoxeterMatrix S) (i:S) (x y:S→ℝ) :
    cartanForm M (simpleReflection M i x) (simpleReflection M i y)=cartanForm M x y := by
  simp only [simpleReflection_apply,cartanForm,Matrix.mulVec_sub,Matrix.mulVec_smul,
    dotProduct_sub,sub_dotProduct,dotProduct_smul,smul_dotProduct,smul_eq_mul]
  change cartanForm M x y - (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) y -
    (cartan M *ᵥ y) i * (cartanForm M x (Pi.single i 1) -
      (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) (Pi.single i 1)) = _
  rw [cartanForm_single_right,cartanForm_single_left,cartanForm_single_left]
  have hd : (cartan M *ᵥ Pi.single i (1:ℝ)) i = 2 := by simp [Matrix.mulVec_single]
  rw [hd]
  change cartanForm M x y - _ - _ = cartanForm M x y
  ring

lemma cartanForm_invariant (w:W) (x y:S→ℝ) :
    cartanForm M (representation cs w x) (representation cs w y)=cartanForm M x y := by
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  rw [he]
  clear hu he w
  induction u with
  | nil => simp
  | cons i u ih =>
    simpa only [cs.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      cartanForm_reflection] using ih

lemma positive_root_sum_ge_one (w:W) (i:S)
    (h:∀j,0≤representation cs w (Pi.single i 1) j) :
    1≤∑j,representation cs w (Pi.single i 1) j := by
  let v:=representation cs w (Pi.single i 1)
  have hq:cartanForm M v v=2 := by
    rw [cartanForm_invariant,cartanForm_single_left]
    simp [Matrix.mulVec_single]
  have hb:∀j k,cartan M j k≤(2:ℝ) := by
    intro j k
    by_cases he:j=k
    · subst k; simp
    · exact (cartan_off_nonpos M j k he).trans (by norm_num)
  have hh:cartanForm M v v≤2*(∑j,v j)^2 := by
    calc
      cartanForm M v v = ∑j,∑k,v j*cartan M j k*v k := by
        simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      _ ≤ ∑j,∑k,v j*2*v k := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb j k) (h j)) (h k)
      _ = 2*(∑j,v j)^2 := by
        simp only [Finset.sum_mul,Finset.mul_sum,pow_two]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hn:0≤∑j,v j:=Finset.sum_nonneg (fun j _=>h j)
  change 1≤∑j,v j
  nlinarith

lemma length_sum_bound (x:S→ℝ) (hx:cartan M *ᵥ x=1) (w:W) :
    (cs.length w:ℝ)+(∑i,representation cs w x i)≤∑i,x i := by
  have H:∀u:List S,cs.IsReduced u→
      (u.length:ℝ)+(∑i,representation cs (cs.wordProd u) x i)≤∑i,x i := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u i ih =>
      intro hr
      have hru:cs.IsReduced u:=by simpa only [List.take_left] using hr.take u.length
      have hp:=ih hru
      have has:cs.length (cs.wordProd u*cs.simple i)=cs.length (cs.wordProd u)+1 := by
        simpa only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,
          List.length_singleton,hru.eq] using hr.eq
      have hroot:=positive_root_sum_ge_one cs (cs.wordProd u) i (root_nonneg_of_ascent cs _ _ has)
      have he:simpleReflection M i x=x-Pi.single i 1 := by
        rw [simpleReflection_apply,hx]
        simp only [Pi.one_apply,one_smul]
      simp only [cs.wordProd_append,cs.wordProd_singleton,map_mul,LinearEquiv.mul_apply,
        representation_simple,he,map_sub,Pi.sub_apply,Finset.sum_sub_distrib,
        List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      linarith
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  simpa only [←hu.eq,←he] using H u hu

include cs in

theorem finite_of_cartan_posDef (hC:(cartan M).PosDef) : Finite W := by
  let x: S→ℝ := (cartan M)⁻¹ *ᵥ 1
  have hx:cartan M *ᵥ x=1 := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit),
      Matrix.one_mulVec]
  have hs:∀v:S→ℝ,cartanForm M v x=∑i,v i := by
    intro v
    simp only [cartanForm,hx,dotProduct,Pi.one_apply,mul_one]
  have hl:∀w:W,-(∑i,x i)≤∑i,representation cs w x i := by
    intro w
    let v:=representation cs w x
    have hn:=hC.posSemidef.dotProduct_mulVec_nonneg (v+x)
    simp only [star_trivial] at hn
    have hq:cartanForm M v v=cartanForm M x x:=cartanForm_invariant cs w x x
    have he:cartanForm M (v+x) (v+x)=cartanForm M v v+cartanForm M v x+
        cartanForm M x v+cartanForm M x x := by
      simp only [cartanForm,Matrix.mulVec_add,dotProduct_add,add_dotProduct]
      ring
    change 0≤cartanForm M (v+x) (v+x) at hn
    rw [he,hq,cartanForm_symm M x v,hs,hs] at hn
    dsimp [v] at hn
    linarith
  obtain ⟨N,hN⟩:=exists_nat_ge (2*∑i,x i)
  have hb:∀w:W,cs.length w≤N := by
    intro w
    have h1:=length_sum_bound cs x hx w
    have h2:=hl w
    have h3:(cs.length w:ℝ)≤N:=by linarith
    exact_mod_cast h3
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S N).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length≤N
  rw [←hu.eq,←he]
  exact hb w

end HarmonicArtin.Geometric

end OAI

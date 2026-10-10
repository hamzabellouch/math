import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.FrobeniusTensor

namespace OAI

/-! Costandard socles and the digit factorization of simple SL₂ modules. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k] [Infinite k]

omit [Infinite k] in
lemma independent_sum_mem {ι T M : Type*} [AddCommGroup M] [Module k M]
    (f : ι → T → k) (hf : LinearIndependent k f) (s : Finset ι) (c : ι → M)
    (S : Submodule k M) (h : ∀ t, ∑ i ∈ s, f i t • c i ∈ S) :
    ∀ i ∈ s, c i ∈ S := by
  have hz : ∀ t, ∑ i ∈ s, f i t • S.mkQ (c i) = 0 := by
    intro t
    have hz : S.mkQ (∑ i ∈ s, f i t • c i) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h t)
    simpa only [map_sum, map_smul] using hz
  intro i hi
  have hi' := function_sum_eq_zero f hf s (fun i => S.mkQ (c i)) hz i hi
  exact (Submodule.Quotient.mk_eq_zero S).mp hi'

lemma costandard_weight_component_mem (n : ℕ) (S : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)))
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) k n) (hv : v ∈ S)
    (i : Fin (n+1)) : (binaryBasis k n).repr v i • binaryBasis k n i ∈ S := by
  have hinj : Function.Injective (fun j : Fin (n+1) => integerCharacter k (2*(j:ℤ)-n)) := by
    intro i j hij
    have := integerCharacter_injective k hij
    apply Fin.ext
    omega
  apply independent_sum_mem k
    (fun j : Fin (n+1) => fun t : kˣ => integerCharacter k (2*(j:ℤ)-n) t)
    ((linearIndependent_monoidHom kˣ k).comp _ hinj) Finset.univ
    (fun j => (binaryBasis k n).repr v j • binaryBasis k n j) S.toSubmodule ?_ i
    (Finset.mem_univ i)
  intro t
  let ρ : Representation k (SL2 k) (MvPolynomial.homogeneousSubmodule (Fin 2) k n) :=
    (homogeneousRepresentation n).comp (dualMatrix k)
  have he : ρ (diagonalTorus k t) v =
      ∑ j : Fin (n+1), integerCharacter k (2*(j:ℤ)-n) t •
        ((binaryBasis k n).repr v j • binaryBasis k n j) := by
    conv_lhs => rw [← (binaryBasis k n).sum_repr v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    have hj : ρ (diagonalTorus k t) (binaryBasis k n j) =
        integerCharacter k (2*(j:ℤ)-n) t • binaryBasis k n j :=
      costandard_basis_weight k n j t
    rw [hj, smul_comm]
  rw [← he]
  exact S.apply_mem_toSubmodule (diagonalTorus k t) hv

omit [Infinite k] in
lemma costandard_basis_upper_orbit (n : ℕ) (i : Fin (n+1)) (t : k) :
    ((homogeneousRepresentation n).comp (dualMatrix k))
      (unipotent k t) (binaryBasis k n i) =
      ∑ j : Fin (n-i.val+1), t^j.val •
        (((-1 : k)^j.val * ((n-i.val).choose j.val : k)) •
          binaryBasis k n ⟨i.val+j.val, by have := j.isLt; have := i.isLt; omega⟩) := by
  apply Subtype.ext
  change linearChange (dualMatrix k (unipotent k t)) (binaryBasis k n i).val = _
  rw [binaryBasis_apply]
  have hx : linearChange (dualMatrix k (unipotent k t)) (MvPolynomial.X 0) =
      (-MvPolynomial.C t * MvPolynomial.X 1 + MvPolynomial.X 0 : MvPolynomial (Fin 2) k) := by
    simp [linearChange_X, dualMatrix, unipotent, Matrix.transpose_apply, Fin.sum_univ_two, add_comm]
  have hy : linearChange (dualMatrix k (unipotent k t)) (MvPolynomial.X 1) =
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) := by
    simp [linearChange_X, dualMatrix, unipotent, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [map_mul, map_pow, map_pow, hx, hy, add_pow]
  rw [← Fin.sum_univ_eq_sum_range, Finset.sum_mul]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, binaryBasis_apply,
    MvPolynomial.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he : n-(i.val+j.val) = n-i.val-j.val := by omega
  rw [he]
  have hneg : (-MvPolynomial.C t : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (-1 : k) * MvPolynomial.C t := by simp
  rw [hneg]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_pow]
  rw [pow_add]
  ring

lemma costandardHighest_mem_of_basis_mem (n : ℕ)
    (S : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k))) (i : Fin (n+1))
    (hi : binaryBasis k n i ∈ S) : costandardHighest k n ∈ S := by
  have h := independent_sum_mem k
    (fun j : Fin (n-i.val+1) => fun t : k => t^j.val)
    ((linearIndependent_powerFunctions k).comp Fin.val Fin.val_injective) Finset.univ
    (fun j => ((-1 : k)^j.val * ((n-i.val).choose j.val : k)) •
      binaryBasis k n ⟨i.val+j.val, by have := j.isLt; have := i.isLt; omega⟩)
    S.toSubmodule (fun t => by
      have h := S.apply_mem_toSubmodule (unipotent k t) hi
      rw [costandard_basis_upper_orbit k n i t] at h
      exact h)
    (Fin.last (n-i.val)) (Finset.mem_univ _)
  have he : i.val+(n-i.val) = n := by have := i.isLt; omega
  have hind : (⟨i.val+(n-i.val), by omega⟩ : Fin (n+1)) = Fin.last n := Fin.ext he
  simp only [Fin.val_last, Nat.choose_self,Nat.cast_one,mul_one,hind] at h
  exact (Submodule.smul_mem_iff _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))).mp h


lemma costandardHighest_mem_of_ne_bot (n : ℕ)
    (S : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)))
    (hS : S ≠ ⊥) : costandardHighest k n ∈ S := by
  classical
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.ext h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'
  have hc : ∃ i, (binaryBasis k n).repr v i ≠ 0 := by
    by_contra! hh
    apply hv0
    apply (binaryBasis k n).repr.injective
    ext i
    simpa using hh i
  obtain ⟨i,hi⟩ := hc
  apply costandardHighest_mem_of_basis_mem k n S i
  exact (Submodule.smul_mem_iff S.toSubmodule hi).mp
    (costandard_weight_component_mem k n S v hv i)

noncomputable def standardCostandardMap (n : ℕ) :
    Representation.IntertwiningMap (standardRepresentation k n)
      ((homogeneousRepresentation n).comp (dualMatrix k)) :=
  (exists_standard_costandard_map k n).choose.intertwiningMap_of_isIntertwiningMap _ _
    (exists_standard_costandard_map k n).choose_spec.1

lemma standardCostandardMap_basis (n : ℕ) (i : Fin (n+1)) :
    standardCostandardMap k n (standardBasis k n i) =
    ((-1:k)^i.val * (n.choose i : k)) • binaryBasis k n i.rev :=
  (exists_standard_costandard_map k n).choose_spec.2 i

lemma standardCostandardMap_highest (n : ℕ) :
    standardCostandardMap k n (standardHighest k n) = costandardHighest k n := by
  change standardCostandardMap k n (standardBasis k n 0) = _
  rw [standardCostandardMap_basis]
  simp only [Fin.val_zero,pow_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,one_smul]
  rfl

 

noncomputable def costandardSocle (n : ℕ) :
    Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)) :=
  (standardCostandardMap k n).range

lemma costandardHighest_mem_socle (n : ℕ) :
    costandardHighest k n ∈ costandardSocle k n :=
  ⟨standardHighest k n, standardCostandardMap_highest k n⟩

lemma costandardSocle_le_of_highest_mem (n : ℕ)
    (S : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)))
    (hv : costandardHighest k n ∈ S) : costandardSocle k n ≤ S := by
  intro v hv'
  obtain ⟨x,rfl⟩ := hv'
  have hc : ∀ i : Fin (n+1),
      ((-1:k)^i.val * (n.choose i : k)) • binaryBasis k n i.rev ∈ S := by
    intro i
    apply independent_sum_mem k
      (fun j : Fin (n+1) => fun t : k => t^j.val)
      ((linearIndependent_powerFunctions k).comp Fin.val Fin.val_injective) Finset.univ
      (fun j => ((-1:k)^j.val * (n.choose j : k)) • binaryBasis k n j.rev)
      S.toSubmodule ?_ i (Finset.mem_univ _)
    intro t
    have ht := S.apply_mem_toSubmodule (lowerUnipotent k t) hv
    change (costandard k n).ρ (lowerUnipotent k t) (costandardHighest k n) ∈ S at ht
    rw [costandardHighest_lower_orbit] at ht
    exact ht
  rw [← (standardBasis k n).sum_repr x, map_sum]
  apply S.toSubmodule.sum_mem
  intro i _
  rw [map_smul]
  change _ • standardCostandardMap k n (standardBasis k n i) ∈ S.toSubmodule
  rw [standardCostandardMap_basis]
  exact S.toSubmodule.smul_mem _ (hc i)

lemma costandardSocle_le_of_ne_bot (n : ℕ)
    (S : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)))
    (hS : S ≠ ⊥) : costandardSocle k n ≤ S :=
  costandardSocle_le_of_highest_mem k n S (costandardHighest_mem_of_ne_bot k n S hS)

lemma costandardSocle_ne_bot (n : ℕ) : costandardSocle k n ≠ ⊥ := by
  intro h
  have hv := costandardHighest_mem_socle k n
  rw [h] at hv
  exact (binaryBasis k n).ne_zero (Fin.last n) hv

lemma binaryBasis_mem_costandardSocle (n : ℕ) (i : Fin (n+1))
    (hi : (n.choose i : k) ≠ 0) : binaryBasis k n i ∈ costandardSocle k n := by
  have hc : (n.choose i.rev : k) = (n.choose i : k) := by
    simpa only [Fin.val_rev,Nat.succ_sub_succ_eq_sub] using
      congrArg (fun m : ℕ => (m : k)) (Nat.choose_symm (Nat.le_of_lt_succ i.isLt))
  let c : k := (-1:k)^i.rev.val * (n.choose i.rev : k)
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hc ▸ hi)
  change binaryBasis k n i ∈ (standardCostandardMap k n).range
  refine ⟨c⁻¹ • standardBasis k n i.rev, ?_⟩
  rw [map_smul]
  change c⁻¹ • standardCostandardMap k n (standardBasis k n i.rev) = _
  rw [standardCostandardMap_basis, Fin.rev_rev, smul_smul, inv_mul_cancel₀ hc0,
    one_smul]

lemma costandardSocle_eq_top (n : ℕ) (hc : ∀ i : Fin (n+1), (n.choose i : k) ≠ 0) :
    costandardSocle k n = ⊤ := by
  apply Subrepresentation.ext
  apply top_unique
  rw [← (binaryBasis k n).span_eq]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact binaryBasis_mem_costandardSocle k n i (hc i))

 
noncomputable def simpleSL2 (n : ℕ) : FDRep k (SL2 k) :=
  FDRep.of (V := (costandardSocle k n).toSubmodule) (costandardSocle k n).toRepresentation

lemma simpleSL2_rational (n : ℕ) : IsRational k (simpleSL2 k n).ρ := by
  apply IsRational.of_injective k (simpleSL2 k n).ρ (costandard k n).ρ
    (costandardSocle k n).toSubmodule.subtype Subtype.val_injective (by intros; rfl)
  exact costandard_rational k n

noncomputable def simpleCostandardι (n : ℕ) : simpleSL2 k n ⟶ costandard k n :=
  fdrepHom k (costandardSocle k n).toSubmodule.subtype (by intros; rfl)

lemma simpleSL2_eq_costandard_of_choose (n : ℕ)
    (hc : ∀ i : Fin (n+1), (n.choose i : k) ≠ 0) :
    Nonempty (simpleSL2 k n ≅ costandard k n) := by
  have hs : Function.Surjective (costandardSocle k n).toSubmodule.subtype := by
    intro x
    refine ⟨⟨x,?_⟩, rfl⟩
    rw [costandardSocle_eq_top k n hc]
    trivial
  have : IsIso (simpleCostandardι k n) := fdrepHom_isIso_of_bijective k _
    ⟨Subtype.val_injective,hs⟩
  exact ⟨asIso (simpleCostandardι k n)⟩

lemma simpleSL2_irreducible (n : ℕ) : Representation.IsIrreducible (simpleSL2 k n).ρ := by
  let S := costandardSocle k n
  have hw : (⟨costandardHighest k n,costandardHighest_mem_socle k n⟩ : S.toSubmodule) ≠ 0 := by
    intro h
    exact (binaryBasis k n).ne_zero (Fin.last n) (congrArg Subtype.val h)
  let : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⟨⊥,⊤,by
      intro h
      have hz : (⟨costandardHighest k n,costandardHighest_mem_socle k n⟩ : S.toSubmodule) ∈
          (⊥ : Subrepresentation S.toRepresentation) := by rw [h]; trivial
      exact hw hz⟩⟩
  change IsSimpleOrder (Subrepresentation S.toRepresentation)
  apply IsSimpleOrder.of_forall_eq_top
  intro T hT
  let I : Subrepresentation ((homogeneousRepresentation n).comp (dualMatrix k)) :=
    { toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨x,hx,rfl⟩ := hv
        exact ⟨S.toRepresentation g x,T.apply_mem_toSubmodule g hx,rfl⟩ }
  have hI : I ≠ ⊥ := by
    intro hI
    apply hT
    apply Subrepresentation.ext
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : x.val ∈ I := ⟨x,hx,rfl⟩
    rw [hI] at hx'
    exact Subtype.ext hx'
  have hle : S ≤ I := costandardSocle_le_of_ne_bot k n I hI
  apply top_unique
  intro x _
  have hx := hle x.property
  obtain ⟨y,hy,he⟩ := hx
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy
end

section
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]

noncomputable def binaryDigitMultiply (p a b : ℕ) :
    Binary k a ⊗[k] Binary k b →ₗ[k] Binary k (a+p*b) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => ⟨f.val * MvPolynomial.expand p g.val,
            f.property.mul (expand_homogeneous k p g.val g.property)⟩
          map_add' := by intro g h; apply Subtype.ext; simp [mul_add]
          map_smul' := by intro c g; apply Subtype.ext; simp }
      map_add' := by intro f g; ext h : 1; apply Subtype.ext; simp [add_mul]
      map_smul' := by intro c f; ext g : 1; apply Subtype.ext; simp }

lemma binaryDigitMultiply_basis (p a b : ℕ) (i : Fin (a+1)) (j : Fin (b+1)) :
    binaryDigitMultiply k p a b (binaryBasis k a i ⊗ₜ[k] binaryBasis k b j) =
      binaryBasis k (a+p*b) ⟨i.val+p*j.val, by
        have := i.isLt; have := j.isLt; nlinarith⟩ := by
  apply Subtype.ext
  change (binaryBasis k a i).val * MvPolynomial.expand p (binaryBasis k b j).val = _
  simp only [binaryBasis_apply,map_mul,map_pow,MvPolynomial.expand_X,←pow_mul]
  rw [mul_mul_mul_comm,←pow_add,←pow_add]
  have he : a-i.val+p*(b-j.val) = a+p*b-(i.val+p*j.val) := by
    rw [Nat.mul_sub_left_distrib]
    have h₁ : i.val ≤ a := by omega
    have h₂ : j.val ≤ b := by omega
    have := Nat.mul_le_mul_left p h₂
    omega
  rw [he]

lemma digitIndex_injective (p a b : ℕ) (ha : a < p) :
    Function.Injective (fun ij : Fin (a+1) × Fin (b+1) => ij.1.val+p*ij.2.val) := by
  intro ⟨i,j⟩ ⟨i',j'⟩ h
  have hi : i.val < p := by omega
  have hi' : i'.val < p := by omega
  have hm := congrArg (fun n => n % p) h
  have hd := congrArg (fun n => n / p) h
  have hp : 0 < p := by omega
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hi'] at hm
  simp only [Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt hi,Nat.div_eq_of_lt hi',zero_add] at hd
  exact Prod.ext (Fin.ext hm) (Fin.ext hd)

lemma binaryDigitMultiply_injective (p a b : ℕ) (ha : a < p) :
    Function.Injective (binaryDigitMultiply k p a b) := by
  let B := (binaryBasis k a).tensorProduct (binaryBasis k b)
  apply LinearMap.injective_of_linearIndependent (R := k)
    (f := binaryDigitMultiply k p a b) (v := B) B.span_eq
  let idx : Fin (a+1) × Fin (b+1) → Fin (a+p*b+1) :=
    fun ij => ⟨ij.1.val+p*ij.2.val, by have := ij.1.isLt; have := ij.2.isLt; nlinarith⟩
  have hinj : Function.Injective idx := fun i j h =>
    digitIndex_injective p a b ha (congrArg Fin.val h)
  have he : (binaryDigitMultiply k p a b) ∘ B = (binaryBasis k (a+p*b)) ∘ idx := by
    funext ⟨i,j⟩
    simpa only [Function.comp_apply, B, idx, Module.Basis.tensorProduct_apply] using
      binaryDigitMultiply_basis k p a b i j
  rw [he]
  exact (binaryBasis k (a+p*b)).linearIndependent.comp idx hinj

variable (p : ℕ) [Fact p.Prime] [CharP k p]

lemma choose_digit_cast (a b i j : ℕ) (ha : a < p) (hi : i < p) :
    ((a+p*b).choose (i+p*j) : k) = (a.choose i : k) * (b.choose j : k) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := a+p*b) (k := i+p*j)
  have hp := (Fact.out : p.Prime).pos
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hi,
    Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt ha,Nat.div_eq_of_lt hi,zero_add] at h
  rw [← Nat.cast_mul]
  exact (CharP.cast_eq_iff_mod_eq k p).mpr h

lemma binaryDigitMultiply_intertwines (a b : ℕ) (g : SL2 k)
    (z : Binary k a ⊗[k] Binary k b) :
    binaryDigitMultiply k p a b
      (Representation.tprod (costandard k a).ρ
        ((costandard k b).ρ.comp (frobeniusSL2 k p)) g z) =
      (costandard k (a+p*b)).ρ g (binaryDigitMultiply k p a b z) := by
  change binaryDigitMultiply k p a b
    (TensorProduct.map (homogeneousRepresentation a (dualMatrix k g))
      (homogeneousRepresentation b (dualMatrix k (frobeniusSL2 k p g))) z) =
    homogeneousRepresentation (a+p*b) (dualMatrix k g) (binaryDigitMultiply k p a b z)
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul f h =>
    apply Subtype.ext
    change linearChange (dualMatrix k g) f.val *
      MvPolynomial.expand p (linearChange (dualMatrix k (frobeniusSL2 k p g)) h.val) =
      linearChange (dualMatrix k g) (f.val * MvPolynomial.expand p h.val)
    rw [map_mul,dualMatrix_frobeniusSL2,linearChange_expand]

end

open scoped TensorProduct
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

lemma binaryDigitMultiply_mem_socle (a b : ℕ) (ha : a < p)
    (f : Binary k a) (g : (costandardSocle k b).toSubmodule) :
    binaryDigitMultiply k p a b (f ⊗ₜ[k] g.val) ∈ costandardSocle k (a+p*b) := by
  obtain ⟨x,hx⟩ := g.property
  rw [← hx]
  rw [← (binaryBasis k a).sum_repr f]
  simp only [TensorProduct.sum_tmul,← TensorProduct.smul_tmul',map_sum,map_smul]
  apply (costandardSocle k (a+p*b)).toSubmodule.sum_mem
  intro i _
  apply (costandardSocle k (a+p*b)).toSubmodule.smul_mem
  rw [← (standardBasis k b).sum_repr x]
  simp only [map_sum,map_smul,TensorProduct.tmul_sum,TensorProduct.tmul_smul]
  apply (costandardSocle k (a+p*b)).toSubmodule.sum_mem
  intro j _
  apply (costandardSocle k (a+p*b)).toSubmodule.smul_mem
  change binaryDigitMultiply k p a b
    (binaryBasis k a i ⊗ₜ[k] standardCostandardMap k b (standardBasis k b j)) ∈ _
  rw [standardCostandardMap_basis,TensorProduct.tmul_smul,map_smul,binaryDigitMultiply_basis]
  by_cases hj : (b.choose j : k) = 0
  · simp [hj]
  · apply (costandardSocle k (a+p*b)).toSubmodule.smul_mem
    apply binaryBasis_mem_costandardSocle
    rw [choose_digit_cast k p a b i.val j.rev.val ha (by have := i.isLt; omega)]
    apply mul_ne_zero (choose_cast_ne_zero_of_lt_char k p ha (Nat.le_of_lt_succ i.isLt))
    simpa only [Fin.val_rev,Nat.succ_sub_succ_eq_sub,Nat.choose_symm (Nat.le_of_lt_succ j.isLt)] using hj

noncomputable def binarySocleDigitMultiply (a b : ℕ) :
    Binary k a ⊗[k] (costandardSocle k b).toSubmodule →ₗ[k] Binary k (a+p*b) :=
  (binaryDigitMultiply k p a b).comp
    ((costandardSocle k b).toSubmodule.subtype.lTensor (Binary k a))

omit [Fact p.Prime] [CharP k p] in
lemma binarySocleDigitMultiply_injective (a b : ℕ) (ha : a < p) :
    Function.Injective (binarySocleDigitMultiply k p a b) :=
  (binaryDigitMultiply_injective k p a b ha).comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (costandardSocle k b).toSubmodule.subtype Subtype.val_injective)

lemma binarySocleDigitMultiply_mem (a b : ℕ) (ha : a < p)
    (z : Binary k a ⊗[k] (costandardSocle k b).toSubmodule) :
    binarySocleDigitMultiply k p a b z ∈ costandardSocle k (a+p*b) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    rw [map_add]
    exact (costandardSocle k (a+p*b)).toSubmodule.add_mem hz hw
  | tmul f g => exact binaryDigitMultiply_mem_socle k p a b ha f g

lemma binarySocleDigitMultiply_intertwines (a b : ℕ) (g : SL2 k)
    (z : Binary k a ⊗[k] (costandardSocle k b).toSubmodule) :
    binarySocleDigitMultiply k p a b
      (Representation.tprod ((homogeneousRepresentation a).comp (dualMatrix k))
        ((costandardSocle k b).toRepresentation.comp (frobeniusSL2 k p)) g z) =
      ((homogeneousRepresentation (a+p*b)).comp (dualMatrix k)) g
        (binarySocleDigitMultiply k p a b z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul f h =>
    exact binaryDigitMultiply_intertwines k p a b g (f ⊗ₜ[k] h.val)

lemma binarySocleDigitMultiply_range (a b : ℕ) (ha : a < p) :
    LinearMap.range (binarySocleDigitMultiply k p a b) =
      (costandardSocle k (a+p*b)).toSubmodule := by
  let f := (binarySocleDigitMultiply k p a b).intertwiningMap_of_isIntertwiningMap _ _
    (binarySocleDigitMultiply_intertwines k p a b)
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact binarySocleDigitMultiply_mem k p a b ha x
  · have h : costandardHighest k (a+p*b) ∈ f.range := by
      refine ⟨costandardHighest k a ⊗ₜ[k]
        ⟨costandardHighest k b,costandardHighest_mem_socle k b⟩, ?_⟩
      change binaryDigitMultiply k p a b
        (binaryBasis k a (Fin.last a) ⊗ₜ[k] binaryBasis k b (Fin.last b)) = _
      rw [binaryDigitMultiply_basis]
      rfl
    exact costandardSocle_le_of_highest_mem k (a+p*b) f.range h

 

noncomputable def simpleDigitIso (a b : ℕ) (ha : a < p) :
    costandard k a ⊗ (Action.res (FGModuleCat k) (frobeniusSL2 k p)).obj (simpleSL2 k b) ≅
      simpleSL2 k (a+p*b) := by
  let l := (binarySocleDigitMultiply k p a b).codRestrict
    (costandardSocle k (a+p*b)).toSubmodule (binarySocleDigitMultiply_mem k p a b ha)
  let f : costandard k a ⊗
      (Action.res (FGModuleCat k) (frobeniusSL2 k p)).obj (simpleSL2 k b) ⟶
      simpleSL2 k (a+p*b) := fdrepHom k l (by
    intro g z
    apply Subtype.ext
    exact binarySocleDigitMultiply_intertwines k p a b g z)
  have hinj : Function.Injective l := fun x y h =>
    binarySocleDigitMultiply_injective k p a b ha (congrArg Subtype.val h)
  have hsurj : Function.Surjective l := by
    intro x
    have hx : x.val ∈ LinearMap.range (binarySocleDigitMultiply k p a b) := by
      rw [binarySocleDigitMultiply_range k p a b ha]
      exact x.property
    obtain ⟨z,hz⟩ := hx
    exact ⟨z,Subtype.ext hz⟩
  have : IsIso f := fdrepHom_isIso_of_bijective k f ⟨hinj,hsurj⟩
  exact asIso f
end FiberFunctorProof
end

end OAI

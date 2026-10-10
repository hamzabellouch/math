import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.ColumnCertificates
import OAI.RepresentationTheory.UniversalSquare.Balance.PackingPlans

namespace OAI

/-! Domain Contractions. -/

section

open scoped BigOperators
namespace Saxl.Columns

def Domains : List ℕ → Type
  | [] => Unit
  | r :: rs => Finset (Equiv.Perm (Fin r)) × Domains rs

def Domains.full : (rs : List ℕ) → Domains rs
  | [] => ()
  | _ :: rs => (Finset.univ, full rs)

def Domains.weight : {rs : List ℕ} → Domains rs → Perms rs → ℤ
  | [], _, _ => 1
  | _ :: _, (s,D), (π,σ) => (if π ∈ s then (Equiv.Perm.sign π : ℤ) else 0) * weight D σ

lemma Domains.full_weight {rs : List ℕ} (σ : Perms rs) :
    (full rs).weight σ = sgInteger σ := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [full, weight, sgInteger, Finset.mem_univ, ite_true, ih]

def Domains.atValue : {rs : List ℕ} → Domains rs → Cells rs → ℕ → Domains rs
  | _ :: _, (s,D), .inl i, j => (s.filter (fun π => (π i).val = j),D)
  | _ :: _, (s,D), .inr c, j => (s,atValue D c j)

lemma Domains.atValue_weight {rs : List ℕ} (D : Domains rs) (c : Cells rs)
    (j : ℕ) (σ : Perms rs) :
    (D.atValue c j).weight σ = D.weight σ *
      (if row (perm σ c) = j then 1 else 0) := by
  induction rs with
  | nil => exact c.elim
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    cases c with
    | inl i =>
      simp only [atValue, weight, Finset.mem_filter, perm, Equiv.sumCongr_apply,
        Sum.map_inl, row]
      split_ifs <;> simp_all
    | inr c =>
      simp only [atValue, weight, perm, Equiv.sumCongr_apply, Sum.map_inr, row, ih,
        mul_assoc]

def Domains.vanished : {rs : List ℕ} → Domains rs → Bool
  | [], _ => false
  | _ :: _, (s,D) => decide (s = ∅) || vanished D

lemma Domains.weight_eq_zero {rs : List ℕ} (D : Domains rs)
    (h : D.vanished = true) (σ : Perms rs) : D.weight σ = 0 := by
  induction rs with
  | nil => simp [vanished] at h
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    rcases σ with ⟨π,σ⟩
    simp only [vanished, Bool.or_eq_true] at h
    rcases h with h | h
    · have hs : s = ∅ := of_decide_eq_true h
      simp [weight, hs]
    · simp only [weight, ih D h σ, mul_zero]

def Domains.mass : {rs : List ℕ} → Domains rs → ℤ
  | [], _ => 1
  | _ :: _, (s,D) => (∑ π ∈ s, (Equiv.Perm.sign π : ℤ)) * mass D

lemma Domains.mass_eq_sum {rs : List ℕ} (D : Domains rs) :
    D.mass = ∑ σ : Perms rs, D.weight σ := by
  classical
  induction rs with
  | nil => simp [mass, weight, Perms]
  | cons r rs ih =>
    rcases D with ⟨s,D⟩
    simp only [Perms, Fintype.sum_prod_type, weight, ← Finset.mul_sum, ← ih,
      ← Finset.sum_mul, mass]
    congr 1
    simp

abbrev Edge (rsT rsA rsB : List ℕ) := Cells rsT × Cells rsA × Cells rsB

def domainContraction {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ)) : ℤ :=
  ∑ π : Perms rsT, ∑ σ : Perms rsA, ∑ τ : Perms rsB,
    D.weight π * E.weight σ * F.weight τ *
      (edges.map (fun c => if (row (perm π c.1), row (perm σ c.2.1),
        row (perm τ c.2.2)) ∈ flag then (1 : ℤ) else 0)).prod

lemma domainContraction_nil {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F [] flag = D.mass * E.mass * F.mass := by
  simp only [domainContraction, List.map_nil, List.prod_nil, mul_one,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Domains.mass_eq_sum]

lemma domainContraction_zero {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (edges : List (Edge rsT rsA rsB)) (flag : Finset (ℕ × ℕ × ℕ))
    (h : (D.vanished || E.vanished || F.vanished) = true) :
    domainContraction D E F edges flag = 0 := by
  rw [domainContraction]
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp only [Domains.weight_eq_zero D h, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero E h, mul_zero, zero_mul, Finset.sum_const_zero]
  · simp only [Domains.weight_eq_zero F h, mul_zero, zero_mul, Finset.sum_const_zero]

lemma triple_indicator_sum (flag : Finset (ℕ × ℕ × ℕ)) (a b c : ℕ) :
    (∑ v ∈ flag, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0)) =
      if (a,b,c) ∈ flag then 1 else 0 := by
  have hh : ∀ v : ℕ × ℕ × ℕ, (if a = v.1 then (1 : ℤ) else 0) *
      (if b = v.2.1 then 1 else 0) * (if c = v.2.2 then 1 else 0) =
      if (a,b,c) = v then 1 else 0 := by
    rintro ⟨x,y,z⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [hh]
  rw [Finset.sum_ite_eq]

lemma domainContraction_cons {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    (c : Edge rsT rsA rsB) (edges : List (Edge rsT rsA rsB))
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F (c::edges) flag =
      ∑ v ∈ flag, domainContraction (D.atValue c.1 v.1)
        (E.atValue c.2.1 v.2.1) (F.atValue c.2.2 v.2.2) edges flag := by
  classical
  simp only [domainContraction, List.map_cons, List.prod_cons, Domains.atValue_weight]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  trans (D.weight π * E.weight σ * F.weight τ) *
    (∑ v ∈ flag, (if row (perm π c.1) = v.1 then (1 : ℤ) else 0) *
      (if row (perm σ c.2.1) = v.2.1 then 1 else 0) *
      (if row (perm τ c.2.2) = v.2.2 then 1 else 0)) *
    (edges.map (fun e => if (row (perm π e.1), row (perm σ e.2.1),
      row (perm τ e.2.2)) ∈ flag then (1 : ℤ) else 0)).prod
  · rw [triple_indicator_sum]
    ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring

lemma domainContraction_perm {rsT rsA rsB : List ℕ}
    (D : Domains rsT) (E : Domains rsA) (F : Domains rsB)
    {cs es : List (Edge rsT rsA rsB)} (hp : cs.Perm es)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    domainContraction D E F cs flag = domainContraction D E F es flag := by
  simp only [domainContraction]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  exact congrArg (_ * ·) ((hp.map _).prod_eq)

end Saxl.Columns
end

end OAI

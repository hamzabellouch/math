import OAI.RingTheory.DirectFiniteness.ShortIndependence

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure DirectionFrame (Q : Type u_5) (A : Type u_6) (R : Type u_7) (E : Type u_8) [Field Q] [AddCommGroup A] [Module Q A]
    [AddCommGroup E] [Module Q E] where
  w : R → (Q × Q) →ₗ[Q] A
  e : (R × Q) → E →ₗ[Q] A
  winj : ∀ r, Function.Injective (w r)
  einj : ∀ j, Function.Injective (e j)
  direct : ShortDirect 10 (Sum.elim (fun r => (w r).range) (fun j => (e j).range))

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def d (j : R × Q) : Q →ₗ[Q] A :=
  (F.w j.1).comp
    ({ toFun := fun t => (t, t * j.2)
       map_add' := by intro x y; simp [add_mul]
       map_smul' := by intro x y; simp [mul_assoc] } : Q →ₗ[Q] Q × Q)

def exc (r : R) : Q →ₗ[Q] A := (F.w r).comp (LinearMap.inr Q Q Q)

def u (j : R × Q) : (Q × E) →ₗ[Q] A := (F.d j).coprod (F.e j)

def W (r : R) : Submodule Q A := (F.w r).range

def D (j : R × Q) : Submodule Q A := (F.d j).range

def U (j : R × Q) : Submodule Q A := (F.u j).range

def exceptional (r : R) : Submodule Q A := (F.exc r).range

@[simp] lemma d_apply (j : R × Q) (t : Q) : F.d j t = F.w j.1 (t, t * j.2) := rfl
@[simp] lemma exc_apply (r : R) (t : Q) : F.exc r t = F.w r (0,t) := rfl
@[simp] lemma u_apply (j : R × Q) (x : Q × E) : F.u j x = F.d j x.1 + F.e j x.2 := rfl

lemma d_injective (j : R × Q) : Function.Injective (F.d j) := by
  intro x y he
  exact congrArg Prod.fst (F.winj _ he)

lemma exc_injective (r : R) : Function.Injective (F.exc r) := by
  intro x y he
  exact congrArg Prod.snd (F.winj _ he)

lemma w_e_disjoint (r : R) (j : R × Q) : Disjoint (F.W r) (F.e j).range :=
  F.direct.disjoint (by decide) (Sum.inl_ne_inr)

lemma u_injective (j : R × Q) : Function.Injective (F.u j) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  rintro ⟨t,x⟩ he
  have hw : F.d j t ∈ F.W j.1 := ⟨(t,t*j.2),rfl⟩
  have hE : F.d j t ∈ (F.e j).range := by
    refine ⟨-x, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he).symm
  have hz := (Submodule.disjoint_def.mp (F.w_e_disjoint j.1 j)) _ hw hE
  have ht : t = 0 := F.d_injective j (hz.trans (F.d j).map_zero.symm)
  have hx : x = 0 := F.einj j (by simpa only [u_apply, ht, map_zero, zero_add] using he)
  simp [ht,hx]

/-- Coordinate separation for the sum of two generic vectors. -/
lemma two_generic_E {j k : R × Q} (a b : Q × E)
    (he : F.u j a + F.u k b = 0) :
    F.e j a.2 + (if k = j then F.e k b.2 else 0) = 0 := by
  let labels : Fin 4 → R ⊕ (R × Q) := ![.inl j.1, .inr j, .inl k.1, .inr k]
  let v : Fin 4 → A := ![F.d j a.1, F.e j a.2, F.d k b.1, F.e k b.2]
  have hz : ∑ i : Fin 4, v i = 0 := by
    simpa [v, Fin.sum_univ_succ, u_apply, add_assoc] using he
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 4)), v i ∈
      Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (labels i) := by
    intro i _
    fin_cases i
    · exact ⟨(a.1,a.1*j.2),rfl⟩
    · exact ⟨a.2,rfl⟩
    · exact ⟨(b.1,b.1*k.2),rfl⟩
    · exact ⟨b.2,rfl⟩
  have hh := F.direct.grouped_sum Finset.univ (by simp) labels v hm hz (.inr j)
  simpa [labels, v, Finset.sum_filter, Fin.sum_univ_succ] using hh

lemma U_disjoint {j k : R × Q} (hjk : j ≠ k) : Disjoint (F.U j) (F.U k) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have he : F.u j a + F.u k (-b) = 0 := by rw [map_neg, hb, add_neg_cancel]
  have hE := F.two_generic_E a (-b) he
  simp only [ite_eq_right hjk.symm, add_zero] at hE
  have ha : a.2 = 0 := F.einj j (by simpa using hE)
  have hE' := F.two_generic_E (-b) a (by simpa [add_comm] using he)
  simp only [ite_eq_right hjk, add_zero] at hE'
  have hb0 : b.2 = 0 := by
    have hh : (-b).2 = 0 := F.einj k (by simpa using hE')
    simpa using hh
  have hw : F.d k b.1 = F.d j a.1 := by simpa [u_apply, ha, hb0] using hb
  by_cases hr : j.1 = k.1
  · have hcoord := F.winj j.1 (by simpa [hr] using hw.symm)
    have ht := congrArg Prod.fst hcoord
    change a.1 = b.1 at ht
    have hs := congrArg Prod.snd hcoord
    change a.1 * j.2 = b.1 * k.2 at hs
    have hv : j.2 ≠ k.2 := fun h => hjk (Prod.ext hr h)
    have hat : a.1 = 0 := by
      by_contra hn
      exact hv (mul_left_cancel₀ hn (by rw [← ht] at hs; exact hs))
    simp only [u_apply, ha, hat, map_zero, add_zero]
  · have hd := F.direct.disjoint (by decide : 2 ≤ 10)
      (show Sum.inl j.1 ≠ (Sum.inl k.1 : R ⊕ (R × Q)) from fun h => hr (Sum.inl.inj h))
    have hz : F.d j a.1 = 0 := (Submodule.disjoint_def.mp hd) _
      ⟨(a.1,a.1*j.2),rfl⟩ ⟨(b.1,b.1*k.2),hw⟩
    simpa only [u_apply,ha,map_zero,add_zero] using hz

lemma generic_eq_w_E_zero {j : R × Q} {r : R} (a : Q × E) (b : Q × Q)
    (he : F.u j a = F.w r b) : a.2 = 0 := by
  let labels : Fin 3 → R ⊕ (R × Q) := ![.inl j.1, .inr j, .inl r]
  let v : Fin 3 → A := ![F.d j a.1, F.e j a.2, -(F.w r b)]
  have hz : ∑ i : Fin 3, v i = 0 := by
    simpa [v, Fin.sum_univ_succ, u_apply, sub_eq_add_neg, add_assoc] using sub_eq_zero.mpr he
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), v i ∈
      Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (labels i) := by
    intro i _
    fin_cases i
    · exact ⟨(a.1,a.1*j.2),rfl⟩
    · exact ⟨a.2,rfl⟩
    · exact ⟨-b, by simp [v]⟩
  have hh := F.direct.grouped_sum Finset.univ (by simp) labels v hm hz (.inr j)
  apply F.einj j
  simpa [labels,v,Finset.sum_filter,Fin.sum_univ_succ] using hh

lemma W_disjoint {r t : R} (hrt : r ≠ t) : Disjoint (F.W r) (F.W t) :=
  F.direct.disjoint (by decide) (fun h => hrt (Sum.inl.inj h))

lemma U_inf_W_same (j : R × Q) : F.U j ⊓ F.W j.1 = F.D j := by
  apply le_antisymm
  · rintro x ⟨⟨a,rfl⟩,⟨b,hb⟩⟩
    have ha := F.generic_eq_w_E_zero a b hb.symm
    exact ⟨a.1, by simp only [u_apply,ha,map_zero,add_zero]⟩
  · rintro x ⟨a,rfl⟩
    exact ⟨⟨(a,0), by simp only [u_apply,map_zero,add_zero]⟩,⟨(a,a*j.2),rfl⟩⟩

lemma U_W_disjoint {j : R × Q} {r : R} (hjr : j.1 ≠ r) :
    Disjoint (F.U j) (F.W r) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have ha := F.generic_eq_w_E_zero a b hb.symm
  have hx : F.u j a = F.d j a.1 := by simp only [u_apply,ha,map_zero,add_zero]
  rw [hx] at hb ⊢
  exact Submodule.disjoint_def.mp (F.W_disjoint hjr) _ ⟨(a.1,a.1*j.2),rfl⟩ ⟨b,hb⟩

lemma U_exceptional_disjoint (j : R × Q) (r : R) :
    Disjoint (F.U j) (F.exceptional r) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have ha := F.generic_eq_w_E_zero a (0,b) hb.symm
  have hx : F.u j a = F.d j a.1 := by simp only [u_apply,ha,map_zero,add_zero]
  rw [hx] at hb ⊢
  by_cases hr : j.1 = r
  · have hc := F.winj r (by simpa [hr] using hb)
    have ht : a.1 = 0 := (congrArg Prod.fst hc).symm
    rw [ht,map_zero]
  · exact Submodule.disjoint_def.mp (F.W_disjoint hr) _
      ⟨(a.1,a.1*j.2),rfl⟩ ⟨(0,b),hb⟩

lemma exceptional_disjoint {r t : R} (hrt : r ≠ t) :
    Disjoint (F.exceptional r) (F.exceptional t) := by
  apply (F.W_disjoint hrt).mono
  · rintro x ⟨a,rfl⟩
    exact ⟨(0,a),rfl⟩
  · rintro x ⟨a,rfl⟩
    exact ⟨(0,a),rfl⟩

lemma card_U [Fintype Q] [Fintype E] [Fintype A] (j : R × Q) :
    Fintype.card (F.U j) = Fintype.card Q * Fintype.card E := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (LinearEquiv.ofInjective (F.u j) (F.u_injective j)).toEquiv.symm

lemma card_D [Fintype Q] [Fintype A] (j : R × Q) :
    Fintype.card (F.D j) = Fintype.card Q :=
  Fintype.card_congr (LinearEquiv.ofInjective (F.d j) (F.d_injective j)).toEquiv.symm

lemma card_W [Fintype Q] [Fintype A] (r : R) :
    Fintype.card (F.W r) = Fintype.card Q ^ 2 := by
  have hc := Fintype.card_congr (LinearEquiv.ofInjective (F.w r) (F.winj r)).toEquiv.symm
  simpa [W,pow_two] using hc

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI

import OAI.RingTheory.DirectFiniteness.CharacterIdempotents

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open MultipleHNN CharacterIdempotents
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} [CommGroup A] [Group N] [CommGroup C]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C)

abbrev H := N × C

def src (v : V) : (A × C) →* H (N := N) (C := C) :=
  (ι v).prodMap (MonoidHom.id C)

def dst (v : V) : (A × C) →* H (N := N) (C := C) where
  toFun a := (ι v₀ a.1, a.2 * α v a.1)
  map_one' := by simp
  map_mul' a b := by ext <;> simp [map_mul]; ac_rfl

include hi in
lemma src_injective (v : V) : Function.Injective (src (C := C) ι v) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  exact Prod.ext (hi v (congrArg Prod.fst h)) (congrArg (fun p : N × C => p.2) h)

include hi in
lemma dst_injective (v : V) : Function.Injective (dst ι v₀ α v) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ h
  have hab : a = b := hi v₀ (congrArg Prod.fst h)
  subst b
  exact Prod.ext rfl (mul_right_cancel (congrArg (fun p : N × C => p.2) h))

abbrev source (v : V) := (src (C := C) ι v).range
abbrev target (v : V) := (dst ι v₀ α v).range

def edgeIso (v : V) : source (C := C) ι v ≃* target ι v₀ α v :=
  (MonoidHom.ofInjective (src_injective ι hi v)).symm.trans
    (MonoidHom.ofInjective (dst_injective ι hi v₀ α v))

abbrev L := Extension (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
abbrev emb : H (N := N) (C := C) →* L ι hi v₀ α :=
  of (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
abbrev τ (v : V) : L ι hi v₀ α :=
  letter (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α) v

lemma emb_injective [Fintype V] : Function.Injective (emb ι hi v₀ α) :=
  of_injective _ _ _

lemma conjugacy (v : V) (a : A) (c : C) :
    τ ι hi v₀ α v * emb ι hi v₀ α (ι v a, c) =
      emb ι hi v₀ α (ι v₀ a, c * α v a) * τ ι hi v₀ α v := by
  have h := letter_mul_of (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α)
    v (MonoidHom.ofInjective (src_injective ι hi v) (a,c))
  have he : edgeIso ι hi v₀ α v (MonoidHom.ofInjective (src_injective ι hi v) (a,c)) =
      MonoidHom.ofInjective (dst_injective ι hi v₀ α v) (a,c) := by
    exact congrArg (MonoidHom.ofInjective (dst_injective ι hi v₀ α v))
      ((MonoidHom.ofInjective (src_injective ι hi v)).symm_apply_apply (a,c))
  rw [he] at h
  exact h

lemma central_cyclic (c : C) (x : L ι hi v₀ α) :
    Commute (emb ι hi v₀ α (1,c)) x := by
  apply Commute.symm
  exact of_central (source (C := C) ι) (target ι v₀ α) (edgeIso ι hi v₀ α) (1,c)
    (by
      rintro ⟨n,d⟩
      change (n,d) * (1,c) = (1,c) * (n,d)
      ext <;> simp [mul_comm]) (by
      intro v
      exact ⟨(1,c), by simp [src]⟩) (by
      intro v
      change (dst ι v₀ α v) ((MonoidHom.ofInjective (src_injective ι hi v)).symm _) = _
      have he : (⟨(1,c), ⟨(1,c), by simp [src]⟩⟩ : source (C := C) ι v) =
          MonoidHom.ofInjective (src_injective ι hi v) (1,c) := by
        apply Subtype.ext
        change (1,c) = (src (C := C) ι v) (1,c)
        simp [src]
      rw [he, MulEquiv.symm_apply_apply]
      simp [dst]) x

variable {K : Type u_5} [Field K] [Fintype A] [Fintype C]
variable (ξ : C →* Kˣ)

def zHom : C →* L ι hi v₀ α := (emb ι hi v₀ α).comp (MonoidHom.inr N C)
def localHom (v : V) : A →* L ι hi v₀ α :=
  (emb ι hi v₀ α).comp ((MonoidHom.inl N C).comp (ι v))
def e : MonoidAlgebra K (L ι hi v₀ α) := pushed (zHom ι hi v₀ α) ξ
def P (v : V) : MonoidAlgebra K (L ι hi v₀ α) := pushed (localHom ι hi v₀ α v) 1
def Q (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  pushed (localHom ι hi v₀ α v₀) (ξ.comp (α v))⁻¹

def u (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  MonoidAlgebra.of K _ (τ ι hi v₀ α v)
def uInv (v : V) : MonoidAlgebra K (L ι hi v₀ α) :=
  MonoidAlgebra.of K _ (τ ι hi v₀ α v)⁻¹

omit [Fintype A] [Fintype C] in
lemma uInv_mul_u (v : V) : uInv (K := K) ι hi v₀ α v * u ι hi v₀ α v = 1 := by
  simp [uInv, u, ← MonoidAlgebra.one_def]
omit [Fintype A] [Fintype C] in
lemma u_mul_uInv (v : V) : u (K := K) ι hi v₀ α v * uInv ι hi v₀ α v = 1 := by
  simp [uInv, u, ← MonoidAlgebra.one_def]

omit [Fintype A] in
lemma e_central (x : MonoidAlgebra K (L ι hi v₀ α)) : Commute (e ι hi v₀ α ξ) x :=
  pushed_central _ _ (central_cyclic ι hi v₀ α) x

omit [Fintype A] in
lemma cyclic_weight (n : N) (c : C) :
    e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,c)) =
      (ξ c : K) • (e ι hi v₀ α ξ * MonoidAlgebra.of K _ (emb ι hi v₀ α (n,1))) := by
  have hfac : emb ι hi v₀ α (n,c) =
      zHom ι hi v₀ α c * emb ι hi v₀ α (n,1) := by
    change _ = emb ι hi v₀ α (1,c) * _
    rw [← map_mul]
    congr 1
    ext <;> simp
  rw [hfac, map_mul, ← mul_assoc]
  rw [show e ι hi v₀ α ξ * MonoidAlgebra.of K _ (zHom ι hi v₀ α c) =
    (ξ c : K) • e ι hi v₀ α ξ from pushed_mul_single _ _ c]
  rw [smul_mul_assoc]

omit [Fintype A] [Fintype C] in
lemma twisted_single (v : V) (a : A) :
    u (K := K) ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
        uInv ι hi v₀ α v =
      MonoidAlgebra.of K _ (emb ι hi v₀ α (ι v₀ a, α v a)) := by
  simp only [u, uInv, localHom, MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul]
  congr 1
  rw [conjugacy, mul_assoc, mul_inv_cancel, mul_one, one_mul]

lemma twisted_average (v : V) :
    e ι hi v₀ α ξ * (u ι hi v₀ α v * P (K := K) ι hi v₀ α v * uInv ι hi v₀ α v) =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  unfold P Q
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [MonoidHom.one_apply, Units.val_one, inv_one, MonoidHom.inv_apply,
    MonoidHom.comp_apply, Units.val_inv_eq_inv_val, inv_inv]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change e ι hi v₀ α ξ * (u ι hi v₀ α v * MonoidAlgebra.of K _ (localHom ι hi v₀ α v a) *
      uInv ι hi v₀ α v) = _
  rw [twisted_single, cyclic_weight]
  simp [localHom, MonoidAlgebra.of_apply, ← mul_smul_comm]

lemma conjugate_projection (v : V) :
    u ι hi v₀ α v * (e ι hi v₀ α ξ * P (K := K) ι hi v₀ α v) * uInv ι hi v₀ α v =
      e ι hi v₀ α ξ * Q ι hi v₀ α ξ v := by
  rw [← mul_assoc, (e_central ι hi v₀ α ξ (u ι hi v₀ α v)).eq.symm,
    mul_assoc, mul_assoc, ← mul_assoc (u ι hi v₀ α v)]
  exact twisted_average ι hi v₀ α ξ v

end KaplanskyCounterexample.CharacterTwist

end

end OAI

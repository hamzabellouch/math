import OAI.RepresentationTheory.Saxl.PositionTensor

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

@[simp] lemma sumPerm_mul {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g g' : Equiv.Perm (Fin a)) (h h' : Equiv.Perm (Fin b)) :
    sumPerm e (g*g') (h*h') = sumPerm e g h * sumPerm e g' h' := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left, sumPerm_right, Equiv.Perm.mul_apply]

@[simp] lemma sumPerm_one {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    sumPerm e 1 1 = 1 := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j <;> simp only [sumPerm_left,sumPerm_right,Equiv.Perm.one_apply]

lemma sumPerm_inv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    sumPerm e g⁻¹ h⁻¹ = (sumPerm e g h)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [← sumPerm_mul, inv_mul_cancel, inv_mul_cancel, sumPerm_one]

def bandOrbitMap {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) :
    X →ₗ[ℂ] ((Fin b → Fin k) → Y) where
  toFun x w := ∑ g : Equiv.Perm (Fin b),
    ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) w) • F (ρ (sumPerm e 1 g⁻¹) x)
  map_add' x y := by ext w; simp only [map_add,smul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' c x := by
    ext w
    simp only [map_smul,Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    exact smul_comm _ _ _

lemma bandOrbitMap_base {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x)
    (x : X) : bandOrbitMap e ρ c F x c =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) => c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) • F x := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = _
  have hh (g : Equiv.Perm (Fin b)) :
      ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) c) • F (ρ (sumPerm e 1 g⁻¹) x) =
      if c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c then F x else 0 := by
    by_cases h : c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c
    · rw [ite_eq_left h, h, Pi.single_eq_same, one_smul, hF g⁻¹ h]
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h), zero_smul]
  simp only [hh]
  simp [Finset.sum_ite,Nat.cast_smul_eq_nsmul]

lemma bandOrbitMap_nonzero {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (hF0 : F ≠ 0)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x) :
    bandOrbitMap e ρ c F ≠ 0 := by
  classical
  intro hz
  apply hF0
  ext x
  have hh := bandOrbitMap_base e ρ c F hF x
  rw [hz] at hh
  change 0 = _ at hh
  have hc : ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) =>
      c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (smul_eq_zero.mp hh.symm).resolve_left hc

lemma bandOrbitMap_equivariant {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ h : Equiv.Perm (Fin a), ∀ x, F (ρ (sumPerm e h 1) x) = τ h (F x))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) (w : Fin b → Fin k) :
    bandOrbitMap e ρ c F (ρ (sumPerm e h q) x) w =
      τ h (bandOrbitMap e ρ c F x (w ∘ q)) := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = τ h (∑ g : Equiv.Perm (Fin b), _)
  rw [map_sum]
  apply (Equiv.sum_comp (Equiv.mulLeft q) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  have he : sumPerm e 1 (q*g)⁻¹ * sumPerm e h q = sumPerm e h 1 * sumPerm e 1 g⁻¹ := by
    rw [← sumPerm_mul, ← sumPerm_mul]
    simp only [one_mul,mul_one,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  change _ • F (ρ (sumPerm e 1 (q*g)⁻¹) (ρ (sumPerm e h q) x)) = _
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hF, map_smul]
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hh
    funext i
    have hi := congrFun hh (q i)
    simpa using hi
  · intro hh
    funext i
    have hi := congrFun hh (q⁻¹ i)
    simpa using hi

end Saxl

end

end OAI

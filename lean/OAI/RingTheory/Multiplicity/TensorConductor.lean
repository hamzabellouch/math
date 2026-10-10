import Mathlib
import OAI.RingTheory.Multiplicity.PerfectDomainStagesTensorTo

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorConductor

section Map
variable {D R M N X : Type*} [CommRing D] [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup X]
  [Module D M] [Module D N] [Module D X]
  [Module R M] [Module R N] [SMulCommClass D R M] [SMulCommClass D R N]

def mapLeft (f : M →ₗ[D] N) (hf : ∀ (r : R) x, f (r • x) = r • f x) :
    M ⊗[D] X →ₗ[R] N ⊗[D] X where
  __ := (f.rTensor X).toAddHom
  map_smul' r t := by
    induction t using TensorProduct.inductionOn with
    | tmul m x => simp [TensorProduct.smul_tmul', hf]
    | add x y hx hy =>
      change (f.rTensor X) (r • (x + y)) = r • ((f.rTensor X) (x + y))
      rw [smul_add, map_add, map_add, smul_add]
      exact congrArg₂ (·+·) hx hy

@[simp] lemma mapLeft_tmul (f : M →ₗ[D] N) (hf : ∀ (r : R) x, f (r • x) = r • f x)
    (m : M) (x : X) : mapLeft f hf (m ⊗ₜ x) = f m ⊗ₜ x := rfl
end Map

section Conductor
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) (hf : ∀ d : D, algebraMap D C d ∈ B)

def toStage : D →+* B := (algebraMap D C).codRestrict B.toSubring hf

variable [Algebra D B] [IsScalarTower D B C]

variable (M : Type*) [AddCommGroup M] [Module D M]

def inclusion : B ⊗[D] M →ₗ[R] C ⊗[D] M :=
  mapLeft ((Algebra.linearMap B C).restrictScalars D)
    (fun _ _ => rfl)

@[simp] lemma inclusion_tmul (b : B) (m : M) :
    inclusion (D := D) B M (b ⊗ₜ m) = (b : C) ⊗ₜ m := rfl

def conductor (g : R) (hg : ∀ c : C, g • c ∈ B) :
    C ⊗[D] M →ₗ[R] B ⊗[D] M :=
  mapLeft ((Lech.Conductor.linearMap B g hg).restrictScalars D) (by
    intro r c
    apply Subtype.ext
    exact smul_comm g r c)

lemma conductor_composition (g : R) (hg : ∀ c : C, g • c ∈ B) :
    (conductor (D := D) B M g hg).comp (inclusion (D := D) B M) = g • (LinearMap.id : B ⊗[D] M →ₗ[R] B ⊗[D] M) := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (·+·) hx hy

lemma kernel_killed (g : R) (hg : ∀ c : C, g • c ∈ B)
    (x : (inclusion (D := D) B M).ker) : g • x = 0 := by
  apply Subtype.ext
  have h := LinearMap.congr_fun (conductor_composition (D := D) B M g hg) x
  change conductor (D := D) B M g hg (inclusion (D := D) B M x) = g • (x : B ⊗[D] M) at h
  rw [x.property, map_zero] at h
  exact h.symm
end Conductor
section Stages
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : ℕ → Subalgebra R C) [∀ n, Algebra D (B n)]
  [∀ n, IsScalarTower D (B n) C]
  (M : Type*) [AddCommGroup M] [Module D M]

lemma ranges_mono (hm : Monotone B) :
    Monotone (fun n => (inclusion (D := D) (B n) M).range) := by
  intro n m hnm y hy
  obtain ⟨t,rfl⟩ := hy
  induction t using TensorProduct.inductionOn with
  | tmul b x => exact ⟨(⟨b,hm hnm b.property⟩ : B m) ⊗ₜ[D] x,rfl⟩
  | add t u ht hu =>
    simpa only [map_add] using (inclusion (D := D) (B m) M).range.add_mem ht hu

lemma ranges_exhaustive (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n) :
    ∀ x : C ⊗[D] M, ∃ n, x ∈ (inclusion (D := D) (B n) M).range := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨n,hn⟩ := hex c
    exact ⟨n,⟨c,hn⟩ ⊗ₜ[D] x,rfl⟩
  | add x y hx hy =>
    obtain ⟨n,hn⟩ := hx
    obtain ⟨m,hm'⟩ := hy
    exact ⟨max n m,(inclusion (D := D) (B (max n m)) M).range.add_mem
      (ranges_mono (D := D) B M hm (le_max_left _ _) hn)
      (ranges_mono (D := D) B M hm (le_max_right _ _) hm')⟩

open Filter
open scoped Topology
 

theorem length_tendsto (T : NormalizedLength.Tower R)
    (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n)
    (g : ℕ → R) (hg : ∀ n c, g n • c ∈ B n)
    (hfinite : ∀ n, T.length ((B n) ⊗[D] M) ≠ ⊤)
    (herr : Tendsto (fun n => T.length (((B n) ⊗[D] M) ⧸
      (LinearMap.lsmul R ((B n) ⊗[D] M) (g n)).range)) atTop (𝓝 0)) :
    Tendsto (fun n => T.length ((B n) ⊗[D] M)) atTop
      (𝓝 (T.length (C ⊗[D] M))) := by
  apply T.length_stage_tendsto (fun n => (B n) ⊗[D] M)
    (fun n => inclusion (D := D) (B n) M) (ranges_mono (D := D) B M hm)
    (ranges_exhaustive (D := D) B M hm hex) _ herr
  intro n
  let F := inclusion (D := D) (B n) M
  have hs : Function.Surjective (LinearMap.id : F.ker →ₗ[R] F.ker) := fun x => ⟨x,rfl⟩
  exact T.length_torsion_subquotient_le (M := (B n) ⊗[D] M) (N := F.ker) (P := F.ker)
    F.ker.subtype (LinearMap.id : F.ker →ₗ[R] F.ker) (Submodule.subtype_injective _) hs
    (g n) (kernel_killed (D := D) (B n) M (g n) (hg n)) (hfinite n)
end Stages
end Lech.TensorConductor

end

end OAI

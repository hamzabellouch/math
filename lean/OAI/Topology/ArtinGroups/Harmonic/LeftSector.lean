import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Crossing

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]
  (N : J → J → Prop) [DecidableRel N] (hN : ∀ ⦃left right⦄, N left right → N right left)

abbrev LeftSector (marked : Bool) (b c : J) :=
  {a : J // (if marked then N a b else a=b) ∧ N a c}

abbrev RightSector (marked : Bool) (b c : J) :=
  {d : J // N b d ∧ (if marked then N c d else c=d)}

noncomputable def sectorEquiv (marked : Bool) (b c : J) :
    LeftSector N marked b c ≃ RightSector N marked b c := by
  cases marked
  · exact {
      toFun a := ⟨c,⟨by
        have ha : a.val=b := by simpa using a.property.1
        simpa only [ha] using a.property.2,by simp⟩⟩
      invFun d := ⟨b,⟨by simp,by
        have hd : c=d.val := by simpa using d.property.2
        simpa only [hd] using d.property.1⟩⟩
      left_inv a := Subtype.ext (by simpa using a.property.1.symm)
      right_inv d := Subtype.ext (by simpa using d.property.2) }
  · exact {
      toFun a := ⟨a,⟨hN (by simpa using a.property.1),hN a.property.2⟩⟩
      invFun d := ⟨d,⟨hN d.property.1,hN (by simpa using d.property.2)⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }

lemma scalar_sector_inverse (b c : J) (r : K) (hr : r ≠ 0) :
    Matrix.of (fun (_ : LeftSector N false b c) (_ : RightSector N false b c) => r) *
      Matrix.of (fun (_ : RightSector N false b c) (_ : LeftSector N false b c) => r⁻¹) =
      (1 : Matrix (LeftSector N false b c) (LeftSector N false b c) K) := by
  classical
  ext a a'
  have hea : a=a' := Subtype.ext (a.property.1.trans a'.property.1.symm)
  subst a'
  have ha : a.val = b := by simpa using a.property.1
  let d : RightSector N false b c := ⟨c,⟨by simpa only [ha] using a.property.2,rfl⟩⟩
  rw [Matrix.mul_apply,Finset.sum_eq_single d]
  · simpa only [Matrix.of_apply, Matrix.one_apply_eq] using mul_inv_cancel₀ hr
  · intro e he hed
    exact (hed (Subtype.ext e.property.2.symm)).elim
  · simp

include hN in
lemma marked_sector_inverse (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a) (b c : J) :
    Matrix.of (fun (a : LeftSector N true b c) (d : RightSector N true b c) => crossing μ A a b c d) *
      Matrix.of (fun (d : RightSector N true b c) (a : LeftSector N true b c) =>
        crossing μ A b a d c * (μ a / μ c)) =
      (1 : Matrix (LeftSector N true b c) (LeftSector N true b c) K) := by
  classical
  ext a a'
  simp only [Matrix.mul_apply, Matrix.of_apply,← mul_assoc,← Finset.sum_mul]
  have hs : (∑ d : RightSector N true b c, crossing μ A a b c d * crossing μ A b a' d c) =
      if a.val=a'.val then μ c / μ a else 0 := by
    rw [← crossing_square N μ hμ δ A hA hroot hPF a a' b c
      (hN a.property.1) (hN a'.property.1) (hN a.property.2) (hN a'.property.2)]
    exact (Finset.sum_subtype (neighbors N b ∩ neighbors N c)
      (fun d => show d ∈ neighbors N b ∩ neighbors N c ↔ N b d ∧ N c d by simp)
      (fun d => crossing μ A a b c d * crossing μ A b a' d c)).symm
  rw [hs]
  by_cases he : a=a'
  · subst a'
    simp only [↓reduceIte,Matrix.one_apply_eq]
    field_simp [hμ]
  · rw [ite_eq_right (fun equality => he (Subtype.ext equality)),zero_mul,Matrix.one_apply_ne he]

def sectorSwitch (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool) :
    Matrix (LeftSector N marked b c) (RightSector N marked b c) K :=
  match marked with
  | false => Matrix.of fun _ _ => r
  | true => Matrix.of fun a d => crossing μ A a b c d

omit [Fintype J] [DecidableRel N] in
lemma sectorSwitch_apply (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool)
    (a : LeftSector N marked b c) (d : RightSector N marked b c) :
    sectorSwitch N μ A b c r marked a d =
      if marked then crossing μ A a b c d else r := by
  cases marked <;> rfl

def sectorUnswitch (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool) :
    Matrix (RightSector N marked b c) (LeftSector N marked b c) K :=
  match marked with
  | false => Matrix.of fun _ _ => r⁻¹
  | true => Matrix.of fun d a => crossing μ A b a d c * (μ a / μ c)

include hN in
lemma sector_inverse (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (b c : J) (r : K) (hr : r ≠ 0) (marked : Bool) :
    sectorSwitch N μ A b c r marked * sectorUnswitch N μ A b c r marked=1 := by
  cases marked
  · exact scalar_sector_inverse N b c r hr
  · exact marked_sector_inverse N hN μ hμ δ A hA hroot hPF b c

end HarmonicArtin.GraphConnection

end OAI

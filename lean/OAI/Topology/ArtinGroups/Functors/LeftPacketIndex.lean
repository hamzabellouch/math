import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.FiniteSum
import OAI.Topology.ArtinGroups.Quivers.PacketIndex
import OAI.Topology.ArtinGroups.Functors.LeftHomPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "F" => linearMap Q step hstep N hN orient μ A

abbrev LeftPacketIndex (p : T → GeneratorPlacement (V × J)) (u:V) :=
  (c:J) × LeftHomIndex Q step hstep N hN p u c
abbrev RightPacketIndex (p : T → GeneratorPlacement (V × J)) (u:V) :=
  (c:J) × RightHomIndex Q step hstep N hN p u c

def leftPacketEquiv (p : T → GeneratorPlacement (V × J)) (u:V) :
    LeftPacketIndex Q step hstep N hN p u ≃
      Index N (Zigzag.packetPlacement U p (fun a:J => (u,a))) where
  toFun x := ⟨⟨x.2.2.1.val,⟨x.2.1,x.2.2.2⟩⟩,⟨x.1,x.2.2.1.property⟩⟩
  invFun x := ⟨x.2.val,⟨x.1.2.1,⟨⟨x.1.1,x.2.property⟩,x.1.2.2⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightPacketEquiv (p : T → GeneratorPlacement (V × J)) (u:V) :
    RightPacketIndex Q step hstep N hN p u ≃
      Zigzag.PacketIndex U (placement N p) (fun a:J => (u,a)) where
  toFun x := ⟨x.1,rightHomEquiv Q step hstep N hN p u x.1 x.2⟩
  invFun x := ⟨x.1,(rightHomEquiv Q step hstep N hN p u x.1).symm x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma linearMap_scalarVertex (v : V × J) (z:K) (i j : StringIndex (V := V) N) :
    F (z • Zigzag.vertexId U v) i j =
      if i=j ∧ i.old=v then z • Zigzag.vertexId U i.new else 0 := by
  rw [map_smul,← Zigzag.pathBasis_vertex,linearMap_pathBasis]
  change z • (if i=j ∧ i.old=v then Zigzag.vertexId U i.new else 0) = _
  split_ifs <;> simp

lemma leftPacket_differential [Fintype T]
    (p : T → GeneratorPlacement (V × J)) (u:V) (M : Matrix T T (Zigzag U K)) :
    (matrix Q step hstep N hN orient μ A
      (Zigzag.packetPlacement U p (fun a:J => (u,a)))
      (Zigzag.packetPlacement U p (fun a:J => (u,a)))
      (Zigzag.packetDifferential U p (fun a:J => (u,a)) M)).submatrix
      (leftPacketEquiv Q step hstep N hN p u) (leftPacketEquiv Q step hstep N hN p u) =
    Matrix.blockDiagonal' (fun c => Zigzag.scalarCornerMatrix U (u,c)
      (leftHomMatrix Q step hstep N hN p p u c M)) := by
  apply Matrix.ext
  rintro ⟨c,i,⟨a,ha⟩,x⟩ ⟨d,j,⟨b,hb⟩,y⟩
  by_cases hab : a=b
  · subst b
    by_cases hcd : c=d
    · subst d
      change F (Zigzag.packetDifferential U p (fun a:J => (u,a)) M ⟨a,⟨i,x⟩⟩ ⟨a,⟨j,y⟩⟩)
        (evaluationSource N u c ⟨a,ha⟩) (evaluationSource N u c ⟨a,hb⟩) = _
      rw [Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_eq,
        Matrix.blockDiagonal'_apply_eq]
      simp only [Zigzag.scalarCornerMatrix,linearMap_scalarVertex,leftHomMatrix,ite_true,
        evaluationSource,StringIndex.old,StringIndex.new,StringIndex.label,and_self]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcd]
      simp only [Matrix.submatrix_apply,matrix,leftPacketEquiv,Equiv.coe_fn_mk,
        Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_eq,Zigzag.scalarCornerMatrix,
        linearMap_scalarVertex]
      apply ite_eq_right
      intro h
      exact hcd (congrArg StringIndex.label h.1)
  · have hba := Ne.symm hab
    simp only [Matrix.submatrix_apply,matrix,leftPacketEquiv,Equiv.coe_fn_mk,
      Zigzag.packetDifferential,Matrix.blockDiagonal'_apply_ne _ _ _ hab,map_zero,
      Matrix.zero_apply]
    by_cases hcd : c=d
    · subst d
      rw [Matrix.blockDiagonal'_apply_eq]
      simp only [Zigzag.scalarCornerMatrix,leftHomMatrix,Subtype.mk.injEq,ite_eq_right hab,zero_smul]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hcd]

section Complex
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "L" => leftHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "R" => rightHomComplex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma leftPacketComplex_eq (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    (C (E.packetTest U (fun a:J => (u,a)))).reindex U
      (leftPacketEquiv Q step hstep N hN E.placement u) =
      Zigzag.BasedComplex.finiteSum U (fun c => L E u c) := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · rfl
  · exact leftPacket_differential Q step hstep N hN orient μ A _ _ _

omit [DecidableEq T] in
lemma rightPacketComplex_eq (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    ((C E).packetTest U (fun a:J => (u,a))).reindex U
      (rightPacketEquiv Q step hstep N hN E.placement u) =
      Zigzag.BasedComplex.finiteSum U (fun c => R E u c) := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · rfl
  · apply Matrix.ext
    rintro ⟨c,x⟩ ⟨d,y⟩
    change Matrix.blockDiagonal' (fun a => Zigzag.scalarCornerMatrix U (u,a)
        (Zigzag.testMatrix U (placement N E.placement) (placement N E.placement) (u,a)
          (matrix Q step hstep N hN orient μ A E.placement E.placement E.differential)))
        ⟨c,rightHomEquiv Q step hstep N hN E.placement u c x⟩
        ⟨d,rightHomEquiv Q step hstep N hN E.placement u d y⟩ =
      Matrix.blockDiagonal' (fun a => (R E u a).differential) ⟨c,x⟩ ⟨d,y⟩
    by_cases h : c=d
    · subst d
      rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
      rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

end Complex
end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI

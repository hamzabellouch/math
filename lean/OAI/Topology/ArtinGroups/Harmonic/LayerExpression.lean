import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.StringAdjacent
import OAI.Topology.ArtinGroups.Functors.TruncationIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.LowerTruncationSum

namespace OAI

namespace HarmonicArtin

inductive LayerExpression (V:Type*) where
  | input : LayerExpression V
  | word : List (V × Bool) → LayerExpression V → LayerExpression V
  | low : ℤ → LayerExpression V → LayerExpression V
  | layer : ℤ → LayerExpression V → LayerExpression V

namespace ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V B J:Type u} {K:Type*} (Q:ReversibleQuiver V B)
  (step:B→Bool) (hstep:∀ b,step (Q.reverse b)=step b)
  (N:J→J→Prop) (hN:∀ ⦃first second : J⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (hn:∀ b,Q.source b≠Q.target b)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

local notation "W" => wordPacketPerm Q step hstep N hN (K:=K) hn

noncomputable def expressionAction : LayerExpression V →
    FiniteHomotopyClass U (K:=K) → FiniteHomotopyClass U (K:=K)
  | .input,x=>x
  | .word w t,x=>W w (expressionAction t x)
  | .low d t,x=>classLowerTruncation U d (expressionAction t x)
  | .layer d t,x=>classLayer U d (expressionAction t x)

lemma expressionAction_sum {I:Type u} [Fintype I] [DecidableEq I]
    (t:LayerExpression V) (x:I→FiniteHomotopyClass U (K:=K)) :
    expressionAction Q step hstep N hN hn t (classSum U x)=
      classSum U (fun i=>expressionAction Q step hstep N hN hn t (x i)) := by
  induction t with
  | input => rfl
  | word w t ih => exact (congrArg (W w) ih).trans (wordPacketPerm_sum Q step hstep N hN hn w _)
  | low d t ih => exact (congrArg (classLowerTruncation U d) ih).trans (classLowerTruncation_sum U d _)
  | layer d t ih => exact (congrArg (classLayer U d) ih).trans (classLayer_sum U d _)

variable (orient:B→Bool) (μ:J→K) (A:K)
  (ho:∀ b,orient (Q.reverse b)=!(orient b))
  (hμ:∀ a,μ a≠0) (δ:K) (hA:A≠0) (hroot:A^2+A⁻¹^2+δ=0)
  (hPF:∀ a,∑ b∈GraphConnection.neighbors N a,μ b=δ*μ a)
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "T" => expressionAction Q step hstep N hN (K:=K) hn

lemma classLabel_expression (t:LayerExpression V) (x:FiniteHomotopyClass U (K:=K)) :
    F (T t x)=T t (F x) := by
  induction t with
  | input => rfl
  | word w t ih =>
    change F (W w (T t x))=W w (T t (F x))
    rw [classLabel_wordPacket,ih]
  | low d t ih =>
    change F (classLowerTruncation U d (T t x))=classLowerTruncation U d (T t (F x))
    rw [← classLabel_truncation,ih]
  | layer d t ih =>
    change F (classLayer U d (T t x))=classLayer U d (T t (F x))
    rw [← classLabel_layer,ih]

lemma classLabel_expressionOrbit (t:LayerExpression V) (s:V) (i:J) :
    F (T t (initialClass U (s,i)))=
      classSum U (fun a:{a:J // N i a}=>T t (initialClass U (s,a))) := by
  rw [classLabel_expression,classLabel_initial,expressionAction_sum]

include ho hμ hA hroot hPF
lemma expressionOrbit_count_adjacency (t:LayerExpression V) (s v:V) (d:ℤ) (i j:J) :
    (∑ a:{a // N a j},classLevelArray U (T t (initialClass U (s,i))) ((v,a),d))=
      ∑ a:{a // N i a},classLevelArray U (T t (initialClass U (s,a))) ((v,j),d) := by
  rw [← classLevelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_expressionOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLevelArray_sum]
  simp

variable [Nonempty J] (hconn:∀ a b,Relation.ReflTransGen N a b)
  (ρ:J→ℝ) (hρ:∀ a,0<ρ a) (θ:ℝ)
  (hρPF:∀ a,∑ b∈GraphConnection.neighbors N a,ρ b=θ*ρ a)
include hconn hρ hρPF

theorem expressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (d:ℤ) :
    ∃ r:ℝ,0≤r ∧ ∀ j,
      (∑ i,ρ i*(classLevelArray U (T t (initialClass U (s,i))) ((v,j),d):ℝ))=r*ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (expressionOrbit_count_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF t s v d)
  · intro j
    exact Finset.sum_nonneg fun i _=>mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end ReversibleQuiver.StringFunctor

namespace ReversibleQuiver.StringFunctor
open Zigzag.BasedComplex

variable {V B:Type} (Q:ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
  (step:B→Bool) (hstep:∀ b,step (Q.reverse b)=step b)
  (hn:∀ b,Q.source b≠Q.target b) (m:ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "T" => expressionAction Q step hstep N hN (K:=ℂ) hn

include hm

theorem string_expressionOrbit_count_proportional (t:LayerExpression V) (s v:V) (d:ℤ) :
    ∃ r:ℝ,0≤r ∧ ∀ j,
      (∑ i,stringWeight m i*(classLevelArray U (T t (initialClass U (s,i))) ((v,j),d):ℝ))=
        r*stringWeight m j := by
  have : NeZero (m-1):=⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩:=string_connection_exists m hm
  exact expressionOrbit_count_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a=>(stringWeight m a:ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2*Real.cos (Real.pi/m):ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) t s v d

end ReversibleQuiver.StringFunctor
end HarmonicArtin

end OAI

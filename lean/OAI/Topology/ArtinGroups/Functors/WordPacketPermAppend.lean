import Mathlib
import OAI.Topology.ArtinGroups.Functors.SignedPacketPerm

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
open Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (hn : ∀ b, Q.source b ≠ Q.target b)
local notation "W" => wordPacketPerm Q step hstep N hN (K:=K) hn

lemma wordPacketPerm_append (w z:List (V × Bool)) : W (w++z)=W w * W z := by
  induction w with
  | nil => exact (_root_.one_mul _).symm
  | cons a w ih => simp only [List.cons_append,wordPacketPerm,ih,_root_.mul_assoc]

lemma wordPacketPerm_positive (w:List V) :
    W (w.map fun v=>(v,true)) = (w.map (colorPacketPerm Q step hstep N hN hn)).prod := by
  induction w with
  | nil => rfl
  | cons v w ih => simp only [List.map_cons,List.prod_cons,wordPacketPerm,ih,signedPacketPerm,↓reduceIte]

lemma signedPacketPerm_inverse (a:V × Bool) :
    signedPacketPerm Q step hstep N hN (K:=K) hn (a.1,!a.2) =
      (signedPacketPerm Q step hstep N hN hn a)⁻¹ := by
  cases a with | mk v b => cases b <;> rfl

lemma wordPacketPerm_inverse (w:List (V × Bool)) :
    W (w.reverse.map fun a=>(a.1,!a.2))=(W w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      wordPacketPerm_append,wordPacketPerm,_root_.mul_one,ih,
      signedPacketPerm_inverse,mul_inv_rev]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI

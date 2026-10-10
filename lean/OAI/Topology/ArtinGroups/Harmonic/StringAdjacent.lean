import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.QuantumNumber
import OAI.Topology.ArtinGroups.Functors.WordOrbitSocleAdjacency
import OAI.Topology.ArtinGroups.Functors.WordOrbitCountAdjacency

namespace OAI

namespace HarmonicArtin

def stringAdjacent (m : ℕ) (a b : StringLabel m) : Prop :=
  a.val+1=b.val ∨ b.val+1=a.val

instance (m : ℕ) : DecidableRel (stringAdjacent m) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma stringAdjacent_symm (m : ℕ) :
    ∀ ⦃first second : StringLabel m⦄, stringAdjacent m first second → stringAdjacent m second first :=
  fun _ _ h => h.symm

lemma stringAdjacent_connected (m : ℕ) (a b : StringLabel m) :
    Relation.ReflTransGen (stringAdjacent m) a b := by
  have ascending (a b : StringLabel m) (h : a.val ≤ b.val) :
      Relation.ReflTransGen (stringAdjacent m) a b := by
    induction n : b.val-a.val generalizing b with
    | zero =>
      have : a=b := Fin.ext (by omega)
      subst b
      exact .refl
    | succ n ih =>
      let c : StringLabel m := ⟨b.val-1,by have := b.isLt; omega⟩
      have hb : c.val+1=b.val := by dsimp [c]; omega
      exact (ih c (by dsimp [c]; omega) (by dsimp [c]; omega)).tail (Or.inl hb)
  by_cases h : a.val ≤ b.val
  · exact ascending a b h
  · have hp := ascending b a (by omega)
    clear h
    induction hp with
    | refl => exact .refl
    | tail hp hbc ih => exact .head hbc.symm ih

lemma stringAdjacent_weight (m : ℕ) (hm : 2 ≤ m) (a : StringLabel m) :
    ∑ b ∈ GraphConnection.neighbors (stringAdjacent m) a, stringWeight m b =
      (2 * Real.cos (Real.pi/m)) * stringWeight m a := by
  rw [← string_dimension_identity hm]
  simp only [GraphConnection.neighbors,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [stringAdjacent,stringMultiplicity]
  by_cases h₁ : a.val+1=b.val
  · have h₂ : ¬ b.val+1=a.val := by omega
    simp [h₁,h₂]
  · by_cases h₂ : b.val+1=a.val <;> simp [h₁,h₂]

namespace ReversibleQuiver
variable {V B : Type} (Q : ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

noncomputable def fixedOrientation (b : B) : Bool :=
  decide (Fintype.equivFin B b < Fintype.equivFin B (Q.reverse b))

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
lemma fixedOrientation_reverse (hn : ∀ b, Q.source b ≠ Q.target b) (b:B) :
    Q.fixedOrientation (Q.reverse b) = !(Q.fixedOrientation b) := by
  have hne : Q.reverse b ≠ b := by
    intro h
    have hs := Q.source_reverse b
    rw [h] at hs
    exact hn b hs
  have hc : Fintype.equivFin B b ≠ Fintype.equivFin B (Q.reverse b) :=
    fun h => hne ((Fintype.equivFin B).injective h).symm
  by_cases h : Fintype.equivFin B b < Fintype.equivFin B (Q.reverse b)
  · have h' := not_lt_of_ge (le_of_lt h)
    simp [fixedOrientation,Q.reverse_reverse,h,h']
  · have h' : Fintype.equivFin B (Q.reverse b) < Fintype.equivFin B b :=
      lt_of_le_of_ne (le_of_not_gt h) hc.symm
    simp [fixedOrientation,Q.reverse_reverse,h,h']

namespace StringFunctor
open Zigzag.BasedComplex

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (hn : ∀ b, Q.source b ≠ Q.target b) (m : ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m
local notation "hN" => stringAdjacent_symm m
local notation "U" => Q.stringQuiver step hstep N hN
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : StringLabel m) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := ℂ) (s,a)))

include hm

lemma string_connection_exists : ∃ A : ℂ, A ≠ 0 ∧
    A^2+A⁻¹^2+(2 * Real.cos (Real.pi/m) : ℝ)=0 ∧
    (∀ a : StringLabel m, (stringWeight m a : ℂ) ≠ 0) ∧
    ∀ a, (∑ b ∈ GraphConnection.neighbors N a, (stringWeight m b : ℂ)) =
      (2 * Real.cos (Real.pi/m) : ℝ) * (stringWeight m a : ℂ) := by
  obtain ⟨A,hA,hr⟩ := GraphConnection.exists_crossing_parameter
    (2 * Real.cos (Real.pi/m) : ℝ)
  refine ⟨A,hA,hr,?_,?_⟩
  · intro a
    exact_mod_cast ne_of_gt (stringWeight_pos hm a)
  · intro a
    exact_mod_cast stringAdjacent_weight m hm a

include hn hm

theorem string_wordOrbit_socle_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLayerSocleDimension U d (v,j) b (O w s i) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_socle_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d b

theorem string_wordOrbit_top_proportional (w : List (V × Bool)) (s v : V) (d b : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLayerTopDimension U d (v,j) b (O w s i) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_top_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d b

theorem string_wordOrbit_count_proportional (w : List (V × Bool)) (s v : V) (d : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, stringWeight m i * (classLevelArray U (O w s i) ((v,j),d) : ℝ)) =
        r * stringWeight m j := by
  have : NeZero (m-1) := ⟨by omega⟩
  obtain ⟨A,hA,hr,hμ,hPF⟩ := string_connection_exists m hm
  exact wordOrbit_count_proportional Q step hstep N hN hn Q.fixedOrientation
    (fun a => (stringWeight m a : ℂ)) A (Q.fixedOrientation_reverse hn) hμ
    (2 * Real.cos (Real.pi/m) : ℝ) hA hr hPF (stringAdjacent_connected m)
    (stringWeight m) (stringWeight_pos hm) _ (stringAdjacent_weight m hm) w s v d

end StringFunctor
end ReversibleQuiver
end HarmonicArtin

end OAI

import Mathlib
import OAI.Topology.ArtinGroups.Functors.Evaluation

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma coordinate_expansion {s t : V × J} (x : Zigzag U K)
    (hl : Zigzag.vertexId U s * x = x) (hr : x * Zigzag.vertexId U t = x)
    (i j : I) (q : Path (V × J) (StringArrow step N)) :
    ∑ p : Zigzag.CornerPath U s t, Zigzag.pathCoordinates U x p.val *
      Zigzag.pathCoordinates U (F (Zigzag.pathBasis U p.val) i j) q =
        Zigzag.pathCoordinates U (F x i j) q := by
  conv_rhs => rw [← Zigzag.sum_cornerPath U x hl hr]
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,
    Zigzag.coordinates_sum,Zigzag.coordinates_smul]

lemma hom_naturality
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t r : V) (a b c e : J) (hac : N a c)
    (x : Zigzag.CornerPath U (u,a) (t,b)) (y : Zigzag U K)
    (hy : y * Zigzag.vertexId U (r,e) = y)
    (j : I) (w : Path (V × J) (StringArrow step N)) :
    (∑ z : Zigzag.CornerPath U (u,a) (r,e),
      Zigzag.pathCoordinates U (Zigzag.pathBasis U x.val * y) z.val *
        Zigzag.pathCoordinates U (F (Zigzag.pathBasis U z.val)
          (evaluationSource N u c ⟨a,hac⟩) j) w) =
    ∑ d : {d : J // N b d}, ∑ z : Zigzag.CornerPath U (u,c) (t,d),
      Zigzag.pathCoordinates U (F (Zigzag.pathBasis U x.val)
        (evaluationSource N u c ⟨a,hac⟩) (evaluationTarget N t b d)) z.val *
      Zigzag.pathCoordinates U (Zigzag.pathBasis U z.val *
        F y (evaluationTarget N t b d) j) w := by
  rw [coordinate_expansion Q step hstep N hN orient μ A _ (by
    rw [← mul_assoc,Zigzag.cornerPath_left]) (by rw [mul_assoc,hy])]
  rw [linearMap_mul_corner Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
    _ y (u,a) (t,b) (Zigzag.cornerPath_left U x) (Zigzag.cornerPath_right U x)]
  rw [Zigzag.coordinates_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Zigzag.coordinates_mul_expansion U _ _
    (linearMap_left Q step hstep N hN orient μ A _ _ _)
    (linearMap_right Q step hstep N hN orient μ A _ _ _) w).symm

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI

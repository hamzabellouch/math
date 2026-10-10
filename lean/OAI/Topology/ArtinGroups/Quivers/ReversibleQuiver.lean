import Mathlib

namespace OAI

namespace HarmonicArtin

structure ReversibleQuiver (V A : Type*) where
  source : A → V
  target : A → V
  reverse : A ≃ A
  reverse_reverse : ∀ a, reverse (reverse a) = a
  source_reverse : ∀ a, source (reverse a) = target a
  target_reverse : ∀ a, target (reverse a) = source a

namespace ReversibleQuiver

variable {V A K : Type*} (Q : ReversibleQuiver V A)

@[simp] theorem reverse_reverse_apply (a : A) : Q.reverse (Q.reverse a) = a :=
  Q.reverse_reverse a

def Zigzag (_Q : ReversibleQuiver V A) (K : Type*) := (V → K) × (A → K) × (V → K)

namespace Zigzag

variable {Q}

instance [AddCommGroup K] : AddCommGroup (Q.Zigzag K) :=
  inferInstanceAs (AddCommGroup ((V → K) × (A → K) × (V → K)))

instance [CommRing K] : Module K (Q.Zigzag K) :=
  inferInstanceAs (Module K ((V → K) × (A → K) × (V → K)))

def vertex (x : Q.Zigzag K) : V → K := x.1
def arrow (x : Q.Zigzag K) : A → K := x.2.1
def token (x : Q.Zigzag K) : V → K := x.2.2

@[ext] theorem ext {x y : Q.Zigzag K} (h₀ : x.vertex = y.vertex)
    (h₁ : x.arrow = y.arrow) (h₂ : x.token = y.token) : x = y :=
  Prod.ext h₀ (Prod.ext h₁ h₂)

@[simp] theorem vertex_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).vertex = x.vertex + y.vertex := rfl
@[simp] theorem arrow_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).arrow = x.arrow + y.arrow := rfl
@[simp] theorem token_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).token = x.token + y.token := rfl
@[simp] theorem vertex_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).vertex = c • x.vertex := rfl
@[simp] theorem arrow_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).arrow = c • x.arrow := rfl
@[simp] theorem token_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).token = c • x.token := rfl
@[simp] theorem vertex_zero [AddCommGroup K] : (0 : Q.Zigzag K).vertex = 0 := rfl
@[simp] theorem arrow_zero [AddCommGroup K] : (0 : Q.Zigzag K).arrow = 0 := rfl
@[simp] theorem token_zero [AddCommGroup K] : (0 : Q.Zigzag K).token = 0 := rfl

end Zigzag

section Multiplication

variable [CommRing K] [Fintype A] [DecidableEq V]

def leftScale (v : V → K) (a : A → K) : A → K := fun e => v (Q.source e) * a e

def rightScale (a : A → K) (v : V → K) : A → K := fun e => a e * v (Q.target e)

def backtrack (a b : A → K) : V → K :=
  fun i => ∑ e, if Q.source e = i then a e * b (Q.reverse e) else 0

@[simp] theorem backtrack_add_left (a b c : A → K) :
    Q.backtrack (a + b) c = Q.backtrack a c + Q.backtrack b c := by
  ext i
  simp only [backtrack, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

@[simp] theorem backtrack_add_right (a b c : A → K) :
    Q.backtrack a (b + c) = Q.backtrack a b + Q.backtrack a c := by
  ext i
  simp only [backtrack, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

@[simp] theorem backtrack_zero_left (a : A → K) : Q.backtrack 0 a = 0 := by
  ext i
  simp [backtrack]

@[simp] theorem backtrack_zero_right (a : A → K) : Q.backtrack a 0 = 0 := by
  ext i
  simp [backtrack]

theorem backtrack_leftScale (v : V → K) (a b : A → K) :
    Q.backtrack (Q.leftScale v a) b = v * Q.backtrack a b := by
  ext i
  simp only [backtrack, leftScale, Pi.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp [he, mul_assoc]
  · simp

theorem backtrack_rightScale (v : V → K) (a b : A → K) :
    Q.backtrack a (Q.rightScale b v) = Q.backtrack a b * v := by
  ext i
  simp only [backtrack, rightScale, Pi.mul_apply, Finset.sum_mul, Q.target_reverse]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp [he, mul_assoc]
  · simp

theorem backtrack_balance (v : V → K) (a b : A → K) :
    Q.backtrack (Q.rightScale a v) b = Q.backtrack a (Q.leftScale v b) := by
  ext i
  simp only [backtrack, rightScale, leftScale, Q.source_reverse, mul_assoc]

namespace Zigzag

instance : Mul (Q.Zigzag K) where
  mul x y := (x.vertex * y.vertex,
    Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex,
    x.vertex * y.token + x.token * y.vertex + Q.backtrack x.arrow y.arrow)

instance : One (Q.Zigzag K) := ⟨(1, 0, 0)⟩

@[simp] theorem vertex_mul (x y : Q.Zigzag K) :
    (x * y).vertex = x.vertex * y.vertex := rfl
@[simp] theorem arrow_mul (x y : Q.Zigzag K) :
    (x * y).arrow = Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex := rfl
@[simp] theorem token_mul (x y : Q.Zigzag K) :
    (x * y).token = x.vertex * y.token + x.token * y.vertex + Q.backtrack x.arrow y.arrow := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem vertex_one : (1 : Q.Zigzag K).vertex = 1 := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem arrow_one : (1 : Q.Zigzag K).arrow = 0 := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem token_one : (1 : Q.Zigzag K).token = 0 := rfl

theorem mul_assoc (x y z : Q.Zigzag K) : (x * y) * z = x * (y * z) := by
  apply ext
  · simp only [vertex_mul, _root_.mul_assoc]
  · ext e
    simp only [arrow_mul, vertex_mul, leftScale, rightScale, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [token_mul, vertex_mul, arrow_mul, Q.backtrack_add_left,
      Q.backtrack_add_right, Q.backtrack_leftScale, Q.backtrack_rightScale,
      Q.backtrack_balance]
    ring

theorem one_mul (x : Q.Zigzag K) : 1 * x = x := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_one (x : Q.Zigzag K) : x * 1 = x := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_add (x y z : Q.Zigzag K) : x * (y + z) = x * y + x * z := by
  apply ext
  · simp [_root_.mul_add]
  · ext e
    simp only [arrow_mul, vertex_add, arrow_add, leftScale, rightScale, Pi.add_apply]
    ring
  · simp only [token_mul, vertex_add, arrow_add, token_add, Q.backtrack_add_right]
    ring

theorem add_mul (x y z : Q.Zigzag K) : (x + y) * z = x * z + y * z := by
  apply ext
  · simp [_root_.add_mul]
  · ext e
    simp only [arrow_mul, vertex_add, arrow_add, leftScale, rightScale, Pi.add_apply]
    ring
  · simp only [token_mul, vertex_add, arrow_add, token_add, Q.backtrack_add_left]
    ring

theorem zero_mul (x : Q.Zigzag K) : 0 * x = 0 := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_zero (x : Q.Zigzag K) : x * 0 = 0 := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

instance : Ring (Q.Zigzag K) where
  mul_assoc := mul_assoc Q
  one_mul := one_mul Q
  mul_one := mul_one Q
  left_distrib := mul_add Q
  right_distrib := add_mul Q
  zero_mul := zero_mul Q
  mul_zero := mul_zero Q

section Trace

variable [Fintype V]

def trace (x : Q.Zigzag K) : K := ∑ i, x.token i

@[simp] theorem trace_add (x y : Q.Zigzag K) :
    trace Q (x + y) = trace Q x + trace Q y := by
  simp only [trace, token_add, Pi.add_apply, Finset.sum_add_distrib]

@[simp] theorem trace_zero : trace Q (0 : Q.Zigzag K) = 0 := by
  simp only [trace, token_zero, Pi.zero_apply, Finset.sum_const_zero]

theorem sum_backtrack (a b : A → K) :
    ∑ i, Q.backtrack a b i = ∑ e, a e * b (Q.reverse e) := by
  simp only [backtrack]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem trace_mul_expression (x y : Q.Zigzag K) :
    trace Q (x * y) = (∑ i, (x.vertex i * y.token i + x.token i * y.vertex i)) +
      ∑ e, x.arrow e * y.arrow (Q.reverse e) := by
  simp only [trace, token_mul, Pi.add_apply, Pi.mul_apply, Finset.sum_add_distrib,
    sum_backtrack]

theorem trace_mul_comm (x y : Q.Zigzag K) : trace Q (x * y) = trace Q (y * x) := by
  rw [trace_mul_expression, trace_mul_expression]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Fintype.sum_equiv Q.reverse
    intro e
    simp [_root_.mul_comm]

def vertexBasis (i : V) : Q.Zigzag K := (Pi.single i 1, 0, 0)

def tokenBasis (i : V) : Q.Zigzag K := (0, 0, Pi.single i 1)

def arrowBasis [DecidableEq A] (e : A) : Q.Zigzag K := (0, Pi.single e 1, 0)

@[simp] theorem trace_mul_tokenBasis (x : Q.Zigzag K) (i : V) :
    trace Q (x * tokenBasis Q i) = x.vertex i := by
  rw [trace_mul_expression]
  simp [tokenBasis, vertex, token, arrow, Pi.single_apply]

@[simp] theorem trace_mul_vertexBasis (x : Q.Zigzag K) (i : V) :
    trace Q (x * vertexBasis Q i) = x.token i := by
  rw [trace_mul_expression]
  simp [vertexBasis, vertex, token, arrow, Pi.single_apply]

@[simp] theorem trace_mul_arrowBasis [DecidableEq A] (x : Q.Zigzag K) (e : A) :
    trace Q (x * arrowBasis Q (Q.reverse e)) = x.arrow e := by
  rw [trace_mul_expression]
  simp [arrowBasis, vertex, token, arrow, Pi.single_apply]

theorem trace_nondegenerate_left (x : Q.Zigzag K)
    (hx : ∀ y : Q.Zigzag K, trace Q (x * y) = 0) : x = 0 := by
  classical
  apply ext
  · funext i
    simpa using hx (tokenBasis Q i)
  · funext e
    simpa using hx (arrowBasis Q (Q.reverse e))
  · funext i
    simpa using hx (vertexBasis Q i)

theorem trace_nondegenerate_right (x : Q.Zigzag K)
    (hx : ∀ y : Q.Zigzag K, trace Q (y * x) = 0) : x = 0 := by
  apply trace_nondegenerate_left Q x
  intro y
  rw [trace_mul_comm]
  exact hx y

theorem trace_smul_mul (c : K) (x y : Q.Zigzag K) :
    trace Q ((c • x) * y) = c * trace Q (x * y) := by
  rw [trace_mul_expression, trace_mul_expression]
  simp only [vertex_smul, arrow_smul, token_smul, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc, ← _root_.mul_add, ← Finset.mul_sum]

theorem trace_mul_smul (c : K) (x y : Q.Zigzag K) :
    trace Q (x * (c • y)) = c * trace Q (x * y) := by
  rw [trace_mul_comm, trace_smul_mul, trace_mul_comm Q y x]

def tracePairing : LinearMap.BilinForm K (Q.Zigzag K) where
  toFun x :=
    { toFun y := trace Q (x * y)
      map_add' := fun y z => by rw [mul_add, trace_add]
      map_smul' := fun c y => by simpa using trace_mul_smul Q c x y }
  map_add' x y := by
    ext z
    exact (congrArg (trace Q) (add_mul Q x y z)).trans (trace_add Q _ _)
  map_smul' c x := by
    ext y
    simpa using trace_smul_mul Q c x y

@[simp] theorem tracePairing_apply (x y : Q.Zigzag K) :
    tracePairing Q x y = trace Q (x * y) := rfl

theorem tracePairing_symmetric : (tracePairing (K := K) Q).IsSymm :=
  ⟨trace_mul_comm Q⟩

theorem tracePairing_nondegenerate : (tracePairing (K := K) Q).Nondegenerate := by
  exact ⟨trace_nondegenerate_left Q, trace_nondegenerate_right Q⟩

theorem annihilate_positive_iff (x : Q.Zigzag K) :
    (∀ y : Q.Zigzag K, y.vertex = 0 → x * y = 0) ↔ x.vertex = 0 ∧ x.arrow = 0 := by
  classical
  constructor
  · intro hx
    constructor
    · funext i
      have h := congrArg (trace Q) (hx (tokenBasis Q i) rfl)
      simpa using h
    · funext e
      have h := congrArg (trace Q) (hx (arrowBasis Q (Q.reverse e)) rfl)
      simpa using h
  · rintro ⟨h₀, h₁⟩ y hy
    apply ext
    · simp [h₀]
    · ext e
      simp [h₀, h₁, hy, leftScale, rightScale]
    · simp [h₀, h₁, hy]

end Trace

theorem positive_triple_mul (x y z : Q.Zigzag K)
    (hx : x.vertex = 0) (hy : y.vertex = 0) (hz : z.vertex = 0) : x * y * z = 0 := by
  have harrow : (x * y).arrow = 0 := by
    ext e
    simp [hx, hy, leftScale, rightScale]
  apply ext
  · simp [hx]
  · ext e
    simp [hx, hz, harrow, leftScale, rightScale]
  · simp [hx, hz, harrow]

end Zigzag
end Multiplication
end ReversibleQuiver
end HarmonicArtin

end OAI

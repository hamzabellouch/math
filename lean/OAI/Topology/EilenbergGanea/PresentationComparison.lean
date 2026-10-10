import OAI.Topology.EilenbergGanea.SmallHolonomy
import Mathlib.Topology.Algebra.Star.Unitary

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
section NaturalPath
variable {Γ S H K : Type*} [Group Γ] [Group H] [Group K]

theorem pathProduct_map (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S)
    (g : Γ) (f : H →* K) :
    pathProduct v (fun p s => f (a p s)) w g = f (pathProduct v a w g) := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of s => simp
  | inv_of s => simp only [pathProduct_inv, pathProduct_of, map_inv]
  | mul w z hw hz => simp only [pathProduct_mul, hw, hz, map_mul]

/-- The literal edge word traversed by a generator word. Free reduction of
this word is harmless for all nonabelian edge labelings. -/
def pathSpelling (v : S → Γ) (w : FreeGroup S) (g : Γ) : FreeGroup (Γ × S) :=
  pathProduct v (fun p s => FreeGroup.of (p,s)) w g

theorem pathSpelling_eval (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) :
    FreeGroup.lift (fun i : Γ × S => a i.1 i.2) (pathSpelling v w g) =
      pathProduct v a w g := by
  symm
  simpa only [FreeGroup.lift_apply_of, pathSpelling] using
    pathProduct_map v (fun p s => FreeGroup.of (p,s)) w g
      (FreeGroup.lift (fun i : Γ × S => a i.1 i.2))

/-- Abelianizing the literal edge word gives exactly the integral edge chain. -/
theorem pathSpelling_abelianization (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    FreeGroup.lift (fun i : Γ × S => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)))
      (pathSpelling v w g) = Multiplicative.ofAdd (pathChain v w g) := by
  exact pathSpelling_eval v (fun p s => Multiplicative.ofAdd (Finsupp.single (p,s) (1 : ℤ))) w g

/-- Naturality in the target additive free module; used when projecting to
extra generators and when tensoring with a finite quotient. -/
theorem pathChain_pairing {M : Type*} [AddCommGroup M]
    (v : S → Γ) (b : Γ × S → M) (w : FreeGroup S) (g : Γ) :
    Finsupp.linearCombination ℤ b (pathChain v w g) =
      (pathProduct v (fun p s => Multiplicative.ofAdd (b (p,s))) w g).toAdd := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of s => simp [pathChain_of, Finsupp.linearCombination_single, pathProduct_of]
  | inv_of s hs =>
      simpa only [pathChain_inv, map_neg, pathProduct_inv, toAdd_inv] using congrArg Neg.neg (hs _)
  | mul w z hw hz => simp only [pathChain_mul, map_add, pathProduct_mul,
      toAdd_mul, hw, hz]

end NaturalPath
end EilenbergGanea

namespace EilenbergGanea
section NormalExpressions
variable {S R : Type*}

def inverseNormalFactor (f : NormalFactor S R) : NormalFactor S R :=
  (f.1, f.2.1, !f.2.2)

theorem normalFactor_inverse (r : R → FreeGroup S) (f : NormalFactor S R) :
    normalFactorWord r (inverseNormalFactor f) = (normalFactorWord r f)⁻¹ := by
  rcases f with ⟨u, i, ε⟩
  cases ε <;> simp [normalFactorWord, inverseNormalFactor, mul_assoc]

/-- Every element of a normal closure admits one finite product of conjugates,
including for arbitrary (possibly uncountable) index types. -/
theorem exists_normalExpression (r : R → FreeGroup S) {w : FreeGroup S}
    (hw : w ∈ Subgroup.normalClosure (Set.range r)) :
    ∃ l : List (NormalFactor S R), w = (l.map (normalFactorWord r)).prod := by
  change w ∈ Subgroup.closure (Group.conjugatesOfSet (Set.range r)) at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨y, ⟨i, rfl⟩, hy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨u, hu⟩ := isConj_iff.mp hy
      refine ⟨[(u,i,true)], ?_⟩
      simpa [normalFactorWord] using hu.symm
  | one => exact ⟨[], by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨l, rfl⟩ := ihx
      obtain ⟨k, rfl⟩ := ihy
      exact ⟨l ++ k, by simp⟩
  | inv x hx ih =>
      obtain ⟨l, rfl⟩ := ih
      refine ⟨(l.map inverseNormalFactor).reverse, ?_⟩
      simp only [List.map_reverse, List.prod_inv_reverse, List.map_map]
      congr 2
      apply List.map_congr_left
      intro f _
      exact (normalFactor_inverse r f).symm

end NormalExpressions
end EilenbergGanea

namespace EilenbergGanea
section WordNorm
open scoped Quaternion
variable {Γ S : Type*} [Group Γ]

theorem su2_mul_distance (a b : SU2) :
    ‖((a*b : SU2) : ℍ) - 1‖ ≤ ‖(a : ℍ) - 1‖ + ‖(b : ℍ) - 1‖ := by
  have he : ((a*b : SU2) : ℍ) - 1 = ((a : ℍ) - 1) * (b : ℍ) + ((b : ℍ) - 1) := by
    change (a : ℍ) * (b : ℍ) - 1 = _
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, su2_norm, mul_one])

/-- A finite control set for a word, uniform over all base vertices and all
labelings. Both the set and the coefficient are chosen before any quotient. -/
theorem finite_word_control (v : S → Γ) (w : FreeGroup S) :
    ∃ (P : Finset S) (n : ℕ), ∀ (ε : ℝ), 0 ≤ ε → ∀ (a : Γ → S → SU2),
      (∀ g, ∀ s ∈ P, ‖(a g s : ℍ) - 1‖ ≤ ε) →
      ∀ g, ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ ≤ n * ε := by
  classical
  induction w using FreeGroup.induction_on with
  | one => exact ⟨∅, 0, fun ε _ a _ g => by simp⟩
  | of s =>
      refine ⟨{s}, 1, fun ε _ a ha g => ?_⟩
      simpa using ha g s (by simp)
  | inv_of s ih =>
      obtain ⟨P, n, hn⟩ := ih
      refine ⟨P, n, fun ε hε a ha g => ?_⟩
      rw [pathProduct_inv, su2_inverse_distance]
      exact hn ε hε a ha _
  | mul w z hw hz =>
      obtain ⟨P, n, hn⟩ := hw
      obtain ⟨Q, m, hm⟩ := hz
      refine ⟨P ∪ Q, n+m, fun ε hε a ha g => ?_⟩
      rw [pathProduct_mul]
      calc
        _ ≤ ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ +
            ‖((pathProduct v a z (g * wordValue v w) : SU2) : ℍ) - 1‖ := su2_mul_distance _ _
        _ ≤ n * ε + m * ε := add_le_add
          (hn ε hε a (fun p s hs => ha p s (Finset.mem_union_left _ hs)) _)
          (hm ε hε a (fun p s hs => ha p s (Finset.mem_union_right _ hs)) _)
        _ = _ := by push_cast; ring

/-- A finite control set for a word, uniform over all base vertices and all
labelings. Both the set and the coefficient are chosen before any quotient. -/
theorem finite_word_control_universal (w : FreeGroup S) :
    ∃ (P : Finset S) (n : ℕ), ∀ {D : Type u} [Group D] (v : S → D) (ε : ℝ), 0 ≤ ε → ∀ (a : D → S → SU2),
      (∀ g, ∀ s ∈ P, ‖(a g s : ℍ) - 1‖ ≤ ε) →
      ∀ g, ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ ≤ n * ε := by
  classical
  induction w using FreeGroup.induction_on with
  | one => exact ⟨∅, 0, fun v ε _ a _ g => by simp⟩
  | of s =>
      refine ⟨{s}, 1, fun v ε _ a ha g => ?_⟩
      simpa using ha g s (by simp)
  | inv_of s ih =>
      obtain ⟨P, n, hn⟩ := ih
      refine ⟨P, n, fun v ε hε a ha g => ?_⟩
      rw [pathProduct_inv, su2_inverse_distance]
      exact hn v ε hε a ha _
  | mul w z hw hz =>
      obtain ⟨P, n, hn⟩ := hw
      obtain ⟨Q, m, hm⟩ := hz
      refine ⟨P ∪ Q, n+m, fun v ε hε a ha g => ?_⟩
      rw [pathProduct_mul]
      calc
        _ ≤ ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ +
            ‖((pathProduct v a z (g * wordValue v w) : SU2) : ℍ) - 1‖ := su2_mul_distance _ _
        _ ≤ n * ε + m * ε := add_le_add
          (hn v ε hε a (fun p s hs => ha p s (Finset.mem_union_left _ hs)) _)
          (hm v ε hε a (fun p s hs => ha p s (Finset.mem_union_right _ hs)) _)
        _ = _ := by push_cast; ring

end WordNorm
end EilenbergGanea

namespace EilenbergGanea
section EvaluatedNormalExpression
open scoped Quaternion
variable {Γ D S R : Type*} [Group Γ] [Group D]

theorem wordValue_quotient (v : S → Γ) (q : Γ →* D) (w : FreeGroup S) :
    wordValue (fun s => q (v s)) w = q (wordValue v w) := by
  have he : wordValue (fun s => q (v s)) = q.comp (wordValue v) := by
    apply FreeGroup.ext_hom
    intro s
    simp [wordValue]
  exact congrArg (fun f : FreeGroup S →* D => f w) he

def evaluatedNormalFactor (v : S → Γ) (a : Γ → S → SU2)
    (f : NormalFactor S R) (g : Γ) : RelatorFactor (Γ × R) :=
  (pathProduct v a f.1 g, (g * wordValue v f.1, f.2.1), f.2.2)

theorem evaluatedNormalFactor_value (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (f : NormalFactor S R) (g : Γ) :
    relatorFactorValue (fun i : Γ × R => pathProduct v a (r i.2) i.1)
      (evaluatedNormalFactor v a f g) = pathProduct v a (normalFactorWord r f) g := by
  rcases f with ⟨u, i, σ⟩
  cases σ <;>
    simp [relatorFactorValue, evaluatedNormalFactor, signedUnit, normalFactorWord,
      pathProduct_conjugate_loop, hr, pathProduct_inv]

theorem pathProduct_normalProduct (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (l : List (NormalFactor S R)) (g : Γ) :
    ((l.map (fun f => evaluatedNormalFactor v a f g)).map
      (relatorFactorValue (fun i : Γ × R => pathProduct v a (r i.2) i.1))).prod =
      pathProduct v a (l.map (normalFactorWord r)).prod g := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, pathProduct_mul,
        normalFactor_value v r hr, mul_one, evaluatedNormalFactor_value v a r hr, ih]

/-- Exact translated signed counts are preserved upon passage to every quotient.
No flatness, finiteness, or injectivity of the quotient is used. -/
theorem quotient_evaluated_counts (v : S → Γ) (q : Γ →* D)
    (a : D → S → SU2) (l : List (NormalFactor S R)) (ρ : R)
    (hc : (l.map (fun f => normalFactorCount v f 1)).sum = Finsupp.single (1,ρ) 1)
    (g : D) :
    relatorSignedCounts (l.map (fun f => evaluatedNormalFactor (fun s => q (v s)) a f g)) =
      Finsupp.single (g,ρ) 1 := by
  let T : ((Γ × R) →₀ ℤ) →ₗ[ℤ] ((D × R) →₀ ℤ) :=
    Finsupp.lmapDomain ℤ ℤ (fun i => (g * q i.1, i.2))
  have hs : relatorSignedCounts
      (l.map (fun f => evaluatedNormalFactor (fun s => q (v s)) a f g)) =
      T (l.map (fun f => normalFactorCount v f 1)).sum := by
    simp only [relatorSignedCounts, List.map_map, map_list_sum]
    congr 1
    apply List.map_congr_left
    intro f _
    simp [T, evaluatedNormalFactor, normalFactorCount, wordValue_quotient]
  rw [hs, hc]
  simp [T]

/-- The actual relator expression, evaluated by arbitrary edge labels on a
quotient graph, has the uniform quadratic error predicted by its exact chain
counts. -/
theorem normalExpression_quadratic (v : S → Γ) (q : Γ →* D)
    (a : D → S → SU2) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (z : FreeGroup S)
    (l : List (NormalFactor S R)) (he : z = (l.map (normalFactorWord r)).prod)
    (ρ : R) (hc : (l.map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,ρ) 1)
    (h ε K : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hb : ∀ f ∈ l, ∀ g, ‖((pathProduct (fun s => q (v s)) a (r f.2.1) g : SU2) : ℍ) - 1‖ ≤ h)
    (ha : ∀ f ∈ l, ∀ g, ‖((pathProduct (fun s => q (v s)) a f.1 g : SU2) : ℍ) - 1‖ ≤ K * (ε+h))
    (g : D) :
    ‖((pathProduct (fun s => q (v s)) a z g : SU2) : ℍ) -
      ((pathProduct (fun s => q (v s)) a (r ρ) g : SU2) : ℍ)‖ ≤
      ((l.length : ℝ)^2 + l.length + 2*l.length*K) * (ε+h)*h := by
  let v' := fun s => q (v s)
  let L := l.map (fun f => evaluatedNormalFactor v' a f g)
  let x := fun i : D × R => pathProduct v' a (r i.2) i.1
  have hp := relator_product_quadratic L x (g,ρ)
    (quotient_evaluated_counts v q a l ρ hc g) h ε K hh hε hK
    (by intro f hf; obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hf; exact hb b hb' _)
    (by intro f hf; obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hf; exact ha b hb' _)
  have hprod : (L.map (fun f => (relatorFactorValue x f : ℍ))).prod =
      ((pathProduct v' a z g : SU2) : ℍ) := by
    have hz := pathProduct_normalProduct v' a r
      (fun i => by simp [v', wordValue_quotient, hr]) l g
    rw [← he] at hz
    have hco (ll : List SU2) : ((ll.prod : SU2) : ℍ) = (ll.map (fun b : SU2 => (b : ℍ))).prod := by
      induction ll with
      | nil => rfl
      | cons b ll ih => simp only [List.prod_cons, Submonoid.coe_mul, List.map_cons, ih]
    have hz' := congrArg (fun x : SU2 => (x : ℍ)) hz
    rw [hco] at hz'
    simpa only [L, x, List.map_map, Function.comp_def] using hz' 
  simpa only [hprod, L, List.length_map, x, v'] using hp

end EvaluatedNormalExpression
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section NormalProductSize
variable {Γ S R : Type*} [Group Γ]

 theorem normalFactor_product_distance (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (f : NormalFactor S R) (g : Γ) :
    ‖((pathProduct v a (normalFactorWord r f) g : SU2) : ℍ) - 1‖ =
      ‖((pathProduct v a (r f.2.1) (g * wordValue v f.1) : SU2) : ℍ) - 1‖ := by
  rw [← evaluatedNormalFactor_value v a r hr]
  exact (su2_conjugation_distance _ _).trans (signedUnit_distance _ _)

/-- Unlike the quadratic estimate, this linear bound needs no information
whatever about the conjugating words. It controls the finitely many auxiliary
loop labels before any bound on the conjugators is obtained. -/
theorem normalProduct_distance (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (l : List (NormalFactor S R)) (h : ℝ)
    (hb : ∀ f ∈ l, ∀ g, ‖((pathProduct v a (r f.2.1) g : SU2) : ℍ) - 1‖ ≤ h)
    (g : Γ) :
    ‖((pathProduct v a (l.map (normalFactorWord r)).prod g : SU2) : ℍ) - 1‖ ≤ l.length * h := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, pathProduct_mul, normalFactor_value v r hr, mul_one]
      calc
        _ ≤ ‖((pathProduct v a (normalFactorWord r f) g : SU2) : ℍ) - 1‖ +
            ‖((pathProduct v a (l.map (normalFactorWord r)).prod g : SU2) : ℍ) - 1‖ := su2_mul_distance _ _
        _ ≤ h + l.length * h := add_le_add
          (by rw [normalFactor_product_distance v a r hr]; exact hb f (by simp) _)
          (ih (fun b hb' => hb b (by simp [hb'])))
        _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

end NormalProductSize
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section FiniteControl
variable {S T H : Type*} [Group H]

 theorem pathProduct_map_alphabet {Γ : Type*} [Group Γ]
    (f : S → T) (v : T → Γ) (a : Γ → T → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v a (FreeGroup.map f w) g =
      pathProduct (v ∘ f) (fun p s => a p (f s)) w g := by
  have he : (labelLift v a).comp (FreeGroup.map f) =
      labelLift (v ∘ f) (fun p s => a p (f s)) := by
    apply FreeGroup.ext_hom
    intro s
    simp [labelLift]
  exact congrArg (fun l : FreeGroup S →* ((Γ → H) ⋊[functionShift Γ H] Γ) => (l w).left g) he

 theorem finite_word_family_control (W : Finset (FreeGroup S)) :
    ∃ (P : Finset S) (n : ℕ), ∀ w ∈ W,
      ∀ {D : Type u} [Group D] (v : S → D) (ε : ℝ), 0 ≤ ε → ∀ (a : D → S → SU2),
      (∀ g, ∀ s ∈ P, ‖(a g s : ℍ) - 1‖ ≤ ε) →
      ∀ g, ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ ≤ n * ε := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨∅,0, by simp⟩
  | @insert w W _ ih =>
      obtain ⟨P,n,hn⟩ := finite_word_control_universal w
      obtain ⟨Q,m,hm⟩ := ih
      refine ⟨P ∪ Q, n+m, ?_⟩
      intro z hz D _ v ε hε a ha g
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hn v ε hε a (fun p s hs => ha p s (Finset.mem_union_left _ hs)) g).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n m) hε)
      · exact (hm z hz v ε hε a (fun p s hs => ha p s (Finset.mem_union_right _ hs)) g).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left m n) hε)

end FiniteControl
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion BigOperators
section UniformComparison
variable {Γ S T Z R : Type*} [Group Γ] [Fintype Z]

/-- All constants and all ordinary relators needed by the quadratic estimate
are chosen before the group quotient and before the edge labels. The normal
expressions are literal finite words, while the ambient alphabets may have any
cardinality. -/
theorem finite_normal_comparison
    (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T))
    (hr : ∀ i, wordValue v (r i) = 1) (z : Z → FreeGroup S)
    (lz : Z → List (NormalFactor (S ⊕ T) (Z ⊕ R)))
    (lt : T → List (NormalFactor (S ⊕ T) (Z ⊕ R)))
    (hz : ∀ i, FreeGroup.map Sum.inl (z i) = ((lz i).map (normalFactorWord r)).prod)
    (ht : ∀ t, FreeGroup.of (Sum.inr t) = ((lt t).map (normalFactorWord r)).prod)
    (hc : ∀ i, ((lz i).map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,Sum.inl i) 1) :
    ∃ (A : Finset R) (C : ℝ), 1 ≤ C ∧
      ∀ {F : Type u} [Group F] (q : Γ →* F) (a : F → S ⊕ T → SU2)
        (ε h : ℝ), 0 ≤ ε → 0 ≤ h →
      (∀ g s, ‖(a g (.inl s) : ℍ) - 1‖ ≤ ε) →
      (∀ i ∈ A, ∀ g, pathProduct (fun s => q (v s)) a (r (.inr i)) g = 1) →
      (∀ i g, ‖((pathProduct (fun s => q (v s)) a (r (.inl i)) g : SU2) : ℍ) - 1‖ ≤ h) →
      ∀ i g,
        ‖((pathProduct (fun s => q (v s)) a (FreeGroup.map Sum.inl (z i)) g : SU2) : ℍ) -
          ((pathProduct (fun s => q (v s)) a (r (.inl i)) g : SU2) : ℍ)‖ ≤ C * (ε+h)*h ∧
        ‖((pathProduct (fun s => q (v s)) a (FreeGroup.map Sum.inl (z i)) g : SU2) : ℍ) - 1‖ ≤ C*ε := by
  classical
  let W : Finset (FreeGroup (S ⊕ T)) := Finset.univ.biUnion fun i =>
    (lz i).toFinset.image Prod.fst
  obtain ⟨P,n,hn⟩ := finite_word_family_control W
  obtain ⟨_,nz,hnz⟩ := finite_word_family_control (Finset.univ.image z)
  let U : Finset (Z ⊕ R) :=
    (Finset.univ.biUnion fun i => (lz i).toFinset.image (fun f => f.2.1)) ∪
    (P.toRight.biUnion fun t => (lt t).toFinset.image (fun f => f.2.1))
  let M : ℕ := 1 + P.toRight.sup (fun t => (lt t).length)
  let N : ℕ := Finset.univ.sup (fun i => (lz i).length)
  let K : ℝ := n * M
  let C : ℝ := 1 + nz + (N : ℝ)^2 + N + 2*N*K
  have hM : 1 ≤ M := Nat.le_add_right 1 _
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcoef : 0 ≤ (2 : ℝ)*N*K := by positivity
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hnzr : (0 : ℝ) ≤ nz := Nat.cast_nonneg _
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N : ℝ)]
  have hnzC : (nz : ℝ) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N : ℝ)]
  have hNC : (N : ℝ)^2 + N + 2*N*K ≤ C := by dsimp [C]; linarith
  refine ⟨U.toRight,C,hC,?_⟩
  intro F _ q a ε h hε hh ha hordinary hdist i g
  let v' := fun s => q (v s)
  have hr' (j) : wordValue v' (r j) = 1 := by simp [v', wordValue_quotient, hr]
  have hused (j : Z ⊕ R) (hj : j ∈ U) (p : F) :
      ‖((pathProduct v' a (r j) p : SU2) : ℍ)-1‖ ≤ h := by
    rcases j with j | j
    · exact hdist j p
    · rw [hordinary j (Finset.mem_toRight.mpr hj) p]
      simpa using hh
  have hZ (j : Z) (f : NormalFactor (S ⊕ T) (Z ⊕ R)) (hf : f ∈ lz j) (p : F) :
      ‖((pathProduct v' a (r f.2.1) p : SU2) : ℍ)-1‖ ≤ h := by
    apply hused _ _ p
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩)
  have hT (t : T) (htP : t ∈ P.toRight) (p : F) : ‖(a p (.inr t) : ℍ)-1‖ ≤ M*h := by
    have hb := normalProduct_distance v' a r hr' (lt t) h
      (fun f hf p => hused _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨t,htP,Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩)) p) p
    rw [← ht t, pathProduct_of] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (lt t).length ≤ M from
        (Finset.le_sup (f := fun t => (lt t).length) htP).trans (Nat.le_add_left _ 1))) hh)
  have hsize : 0 ≤ (M : ℝ)*(ε+h) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg hε hh)
  have hP (p : F) (s : S ⊕ T) (hs : s ∈ P) : ‖(a p s : ℍ)-1‖ ≤ M*(ε+h) := by
    rcases s with s | t
    · calc
        _ ≤ ε := ha p s
        _ ≤ (M : ℝ)*ε := by nlinarith
        _ ≤ (M : ℝ)*(ε+h) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    · exact (hT t (Finset.mem_toRight.mpr hs) p).trans
        (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  have hconj (j : Z) (f : NormalFactor (S ⊕ T) (Z ⊕ R)) (hf : f ∈ lz j) (p : F) :
      ‖((pathProduct v' a f.1 p : SU2) : ℍ)-1‖ ≤ K*(ε+h) := by
    have hW : f.1 ∈ W := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩
    simpa only [K, mul_assoc] using hn f.1 hW v' _ hsize a hP p
  constructor
  · have hb := normalExpression_quadratic v q a r hr _ (lz i) (hz i) (.inl i) (hc i)
      h ε K hh hε hK (hZ i) (hconj i) g
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hh
    apply mul_le_mul_of_nonneg_right _ (add_nonneg hε hh)
    have hl : ((lz i).length : ℝ) ≤ N := by
      exact_mod_cast (show (lz i).length ≤ N from
        Finset.le_sup (f := fun j => (lz j).length) (Finset.mem_univ i))
    have h0 : (0 : ℝ) ≤ (lz i).length := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hp := mul_le_mul_of_nonneg_right hl hK
    nlinarith [sq_nonneg ((N : ℝ) - (lz i).length)]
  · rw [pathProduct_map_alphabet]
    exact (hnz (z i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      _ ε hε (fun p s => a p (.inl s)) (fun p s _ => ha p s) g).trans
      (mul_le_mul_of_nonneg_right hnzC hε)

end UniformComparison
end EilenbergGanea

namespace EilenbergGanea

section QuotientChains
variable {Γ F R S T : Type*} [Group Γ] [Group F]

abbrev BasedChains (Γ S : Type*) := (Γ × S) →₀ ℤ

def translateChains (g : Γ) : BasedChains Γ S →ₗ[ℤ] BasedChains Γ S :=
  Finsupp.lmapDomain ℤ ℤ (fun i => (g*i.1, i.2))

def quotientChains (q : Γ →* F) : BasedChains Γ S →ₗ[ℤ] BasedChains F S :=
  Finsupp.lmapDomain ℤ ℤ (fun i => (q i.1, i.2))

@[simp] theorem translateChains_single (g h : Γ) (s : S) (n : ℤ) :
    translateChains g (Finsupp.single (h,s) n) = Finsupp.single (g*h,s) n := by
  simp [translateChains]

@[simp] theorem quotientChains_single (q : Γ →* F) (g : Γ) (s : S) (n : ℤ) :
    quotientChains q (Finsupp.single (g,s) n) = Finsupp.single (q g,s) n := by
  simp [quotientChains]

theorem translateChains_mul (g h : Γ) (c : BasedChains Γ S) :
    translateChains (g*h) c = translateChains g (translateChains h c) := by
  have he : (translateChains (g*h) : BasedChains Γ S →ₗ[ℤ] _) =
      (translateChains g).comp (translateChains h) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,s⟩ n
    simp [mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem translateChains_one (c : BasedChains Γ S) : translateChains (1 : Γ) c = c := by
  have he : (translateChains (1 : Γ) : BasedChains Γ S →ₗ[ℤ] _) = LinearMap.id := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s⟩ n
    simp
  exact LinearMap.congr_fun he c

theorem quotientChains_translate (q : Γ →* F) (g : Γ) (c : BasedChains Γ S) :
    quotientChains q (translateChains g c) = translateChains (q g) (quotientChains q c) := by
  have he : (quotientChains q).comp (translateChains g) =
      ((translateChains (q g)).comp (quotientChains q) : BasedChains Γ S →ₗ[ℤ] _) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,s⟩ n
    simp
  exact LinearMap.congr_fun he c

/-- The elementary equivariance expressing a left integral group-ring map. -/
def ChainsEquivariant (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) : Prop :=
  ∀ g c, A (translateChains g c) = translateChains g (A c)

/-- Base change of a translation-equivariant matrix, directly on its finitely
supported columns. Its definition needs neither finite index sets nor flatness. -/
def quotientMatrix (q : Γ →* F) (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) :
    BasedChains F R →ₗ[ℤ] BasedChains F S :=
  Finsupp.linearCombination ℤ (fun i =>
    translateChains i.1 (quotientChains q (A (Finsupp.single (1,i.2) 1))))

@[simp] theorem quotientMatrix_single (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) (f : F) (r : R) (n : ℤ) :
    quotientMatrix q A (Finsupp.single (f,r) n) =
      n • translateChains f (quotientChains q (A (Finsupp.single (1,r) 1))) := by
  simp [quotientMatrix]

theorem quotientMatrix_equivariant (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) : ChainsEquivariant (quotientMatrix q A) := by
  intro f c
  have he : (quotientMatrix q A).comp (translateChains f) =
      (translateChains f).comp (quotientMatrix q A) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,r⟩ n
    simp only [LinearMap.comp_apply, translateChains_single, quotientMatrix_single,
      map_smul, translateChains_mul]
  exact LinearMap.congr_fun he c

theorem quotientMatrix_natural (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S) (hA : ChainsEquivariant A)
    (c : BasedChains Γ R) :
    quotientMatrix q A (quotientChains q c) = quotientChains q (A c) := by
  have he : (quotientMatrix q A).comp (quotientChains q) = (quotientChains q).comp A := by
    apply Finsupp.lhom_ext
    rintro ⟨g,r⟩ n
    have hb : Finsupp.single (g,r) n =
        n • translateChains g (Finsupp.single (1,r) (1 : ℤ)) := by simp
    simp only [LinearMap.comp_apply, quotientChains_single, quotientMatrix_single]
    rw [hb, map_smul, map_smul, hA, quotientChains_translate]
  exact LinearMap.congr_fun he c

theorem quotientMatrix_comp (q : Γ →* F)
    (A : BasedChains Γ R →ₗ[ℤ] BasedChains Γ S)
    (B : BasedChains Γ S →ₗ[ℤ] BasedChains Γ T) (hB : ChainsEquivariant B) :
    quotientMatrix q (B.comp A) = (quotientMatrix q B).comp (quotientMatrix q A) := by
  apply Finsupp.lhom_ext
  rintro ⟨f,r⟩ n
  simp only [LinearMap.comp_apply, quotientMatrix_single, map_smul]
  rw [quotientMatrix_equivariant q B f, quotientMatrix_natural q B hB]

theorem quotientMatrix_id (q : Γ →* F) :
    quotientMatrix q (LinearMap.id : BasedChains Γ R →ₗ[ℤ] _) = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨f,r⟩ n
  simp

theorem ChainsEquivariant.symm (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ S)
    (hA : ChainsEquivariant A.toLinearMap) : ChainsEquivariant A.symm.toLinearMap := by
  intro g c
  apply A.injective
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using (hA g (A.symm c)).symm

/-- Tensoring an isomorphism is an isomorphism. This finite-column proof makes
no assertion that the quotient group ring is a flat module. -/
def quotientChainEquiv (q : Γ →* F) (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ S)
    (hA : ChainsEquivariant A.toLinearMap) : BasedChains F R ≃ₗ[ℤ] BasedChains F S where
  __ := quotientMatrix q A.toLinearMap
  invFun := quotientMatrix q A.symm.toLinearMap
  left_inv c := by
    have he := quotientMatrix_comp q A.toLinearMap A.symm.toLinearMap (ChainsEquivariant.symm A hA)
    have hi : A.symm.toLinearMap.comp A.toLinearMap = LinearMap.id := by ext; simp
    rw [hi, quotientMatrix_id] at he
    exact (LinearMap.congr_fun he c).symm
  right_inv c := by
    have he := quotientMatrix_comp q A.symm.toLinearMap A.toLinearMap hA
    have hi : A.toLinearMap.comp A.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [hi, quotientMatrix_id] at he
    exact (LinearMap.congr_fun he c).symm

end QuotientChains
end EilenbergGanea



namespace EilenbergGanea
open scoped BigOperators

/-- A finite family with an integral left inverse has a nonzero square minor.
Expansion of the alternating determinant avoids a flatness or rationalization
assumption, and also covers the empty row family. -/
theorem nonsingular_minor_of_left_inverse {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (v : J → I → ℤ) (b : I → J → ℤ)
    (hb : ∀ i, ∑ j, b i j • v j = Pi.single i 1) :
    ∃ e : I → J, Function.Injective e ∧ Matrix.det (fun i k => v (e i) k) ≠ 0 := by
  classical
  have hex : ∃ e : I → J, Matrix.det (fun i k => v (e i) k) ≠ 0 := by
    by_contra h
    push Not at h
    let D := (Matrix.detRowAlternating : (I → ℤ) [⋀^I]→ₗ[ℤ] ℤ).toMultilinearMap
    have hz : D (fun i => ∑ j, b i j • v j) = 0 := by
      rw [D.map_sum]
      apply Finset.sum_eq_zero
      intro e _
      rw [D.map_smul_univ]
      change (∏ i, b i (e i)) • Matrix.det (fun i k => v (e i) k) = 0
      rw [h]
      exact smul_zero _
    have he : (fun i => ∑ j, b i j • v j) = (1 : Matrix I I ℤ) := by
      ext i k
      rw [show (∑ j, b i j • v j) = Pi.single i 1 from hb i]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [he] at hz
    change Matrix.det (1 : Matrix I I ℤ) = 0 at hz
    simp at hz
  obtain ⟨e, he⟩ := hex
  refine ⟨e, ?_, he⟩
  intro i j hij
  by_contra hne
  exact he (Matrix.det_zero_of_row_eq hne (by simp [hij]))

/-- The same finite-minor statement for an arbitrary direct sum. All supports
are retained, but only the finite union needed by the chosen rows is used. -/
theorem finitely_supported_split_family_minor {I S : Type*} [Fintype I] [DecidableEq I]
    (v : I → S →₀ ℤ) (B : (S →₀ ℤ) →ₗ[ℤ] (I → ℤ))
    (hB : ∀ i, B (v i) = Pi.single i 1) :
    ∃ e : I → S, Function.Injective e ∧ Matrix.det (fun i j => v i (e j)) ≠ 0 := by
  classical
  let P : Finset S := Finset.univ.biUnion (fun i => (v i).support)
  have hP (i : I) : (v i).support ⊆ P := by
    intro s hs
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
  have hexpand (i : I) : v i = ∑ p : P, (v i) p.1 • (Finsupp.single p.1 (1 : ℤ)) := by
    rw [Finset.sum_coe_sort P (fun p => (v i) p • (Finsupp.single p (1 : ℤ)))]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [← Finsupp.sum_of_support_subset (v i) (hP i)
      (fun p t => Finsupp.single p t) (by intro p _; simp)]
    exact (Finsupp.sum_single (v i)).symm
  let w : P → I → ℤ := fun p j => v j p.1
  let b : I → P → ℤ := fun i p => B (Finsupp.single p.1 1) i
  have hb (i : I) : ∑ p, b i p • w p = Pi.single i 1 := by
    ext j
    have hi := congrFun (hB j) i
    rw [hexpand j, map_sum] at hi
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    simpa only [b, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
      Pi.single_apply, eq_comm] using hi
  obtain ⟨e, he, hd⟩ := nonsingular_minor_of_left_inverse w b hb
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i j hij
    exact he (Subtype.ext hij)
  · have ht := Matrix.det_transpose (fun i j => v i (e j).1)
    exact fun h => hd (ht.trans h)

/-- Every finite subfamily of an arbitrary integral basis has a nonsingular
finite coordinate minor, including when the ambient basis is uncountable. -/
theorem basis_subfamily_minor {I R S : Type*} [Fintype I] [DecidableEq I]
    (A : (R →₀ ℤ) ≃ₗ[ℤ] (S →₀ ℤ)) (j : I ↪ R) :
    ∃ e : I → S, Function.Injective e ∧
      Matrix.det (fun i k => A (Finsupp.single (j i) 1) (e k)) ≠ 0 := by
  classical
  let B : (S →₀ ℤ) →ₗ[ℤ] (I → ℤ) :=
    LinearMap.pi fun i => (Finsupp.lapply (j i)).comp A.symm.toLinearMap
  apply finitely_supported_split_family_minor (fun i => A (Finsupp.single (j i) 1)) B
  intro i
  ext k
  simp [B, Pi.single_apply, Finsupp.single_apply, j.injective.eq_iff, eq_comm]

end EilenbergGanea

namespace EilenbergGanea
section ChainProjection
variable {Γ D S T R : Type*} [Group Γ] [Group D]

theorem pathChain_translate (v : S → Γ) (w : FreeGroup S) (g h : Γ) :
    translateChains g (pathChain v w h) = pathChain v w (g*h) := by
  induction w using FreeGroup.induction_on generalizing h with
  | one => simp
  | of s => simp
  | inv_of s ih => simp only [pathChain_inv, map_neg, ih, mul_assoc]
  | mul w z hw hz => simp only [pathChain_mul, map_add, hw, hz, mul_assoc]

theorem pathChain_quotient (v : S → Γ) (q : Γ →* D) (w : FreeGroup S) (g : Γ) :
    quotientChains q (pathChain v w g) = pathChain (fun s => q (v s)) w (q g) := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of s => simp
  | inv_of s ih => simp only [pathChain_inv, map_neg, ih, map_mul, map_inv, wordValue_quotient]
  | mul w z hw hz => simp only [pathChain_mul, map_add, hw, hz, map_mul, wordValue_quotient]

def projectExtraChains : BasedChains Γ (S ⊕ T) →ₗ[ℤ] BasedChains Γ T :=
  Finsupp.linearCombination ℤ fun p => match p.2 with
    | .inl _ => 0
    | .inr t => Finsupp.single (p.1,t) 1

omit [Group Γ] in
@[simp] theorem projectExtraChains_single_left (g : Γ) (s : S) (n : ℤ) :
    projectExtraChains (Finsupp.single (g,Sum.inl s) n : BasedChains Γ (S ⊕ T)) = 0 := by
  simp [projectExtraChains]

omit [Group Γ] in
@[simp] theorem projectExtraChains_single_right (g : Γ) (t : T) (n : ℤ) :
    projectExtraChains (Finsupp.single (g,Sum.inr t) n : BasedChains Γ (S ⊕ T)) =
      Finsupp.single (g,t) n := by simp [projectExtraChains]

theorem projectExtraChains_translate (g : Γ) (c : BasedChains Γ (S ⊕ T)) :
    projectExtraChains (translateChains g c) = translateChains g (projectExtraChains c) := by
  have he : (projectExtraChains (Γ := Γ) (S := S) (T := T)).comp (translateChains g) =
      (translateChains g).comp projectExtraChains := by
    apply Finsupp.lhom_ext
    rintro ⟨h, s | t⟩ n <;> simp
  exact LinearMap.congr_fun he c

theorem projectExtraChains_quotient (q : Γ →* D) (c : BasedChains Γ (S ⊕ T)) :
    projectExtraChains (quotientChains q c) = quotientChains q (projectExtraChains c) := by
  have he : (projectExtraChains (Γ := D) (S := S) (T := T)).comp (quotientChains q) =
      (quotientChains q).comp projectExtraChains := by
    apply Finsupp.lhom_ext
    rintro ⟨h, s | t⟩ n <;> simp
  exact LinearMap.congr_fun he c

def extraRelatorMap (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T)) :
    BasedChains Γ R →ₗ[ℤ] BasedChains Γ T :=
  projectExtraChains.comp (relatorChainMap v r)

@[simp] theorem extraRelatorMap_single (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (g : Γ) (i : R) (n : ℤ) :
    extraRelatorMap v r (Finsupp.single (g,i) n) =
      n • projectExtraChains (pathChain v (r i) g) := by
  simp [extraRelatorMap, relatorChainMap]

theorem extraRelatorMap_equivariant (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T)) :
    ChainsEquivariant (extraRelatorMap v r) := by
  intro g c
  have he : (extraRelatorMap v r).comp (translateChains g) =
      (translateChains g).comp (extraRelatorMap v r) := by
    apply Finsupp.lhom_ext
    rintro ⟨h,i⟩ n
    simp only [LinearMap.comp_apply, translateChains_single, extraRelatorMap_single, map_smul]
    rw [← projectExtraChains_translate, pathChain_translate]
  exact LinearMap.congr_fun he c

theorem extraRelatorMap_quotientMatrix (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (q : Γ →* D) :
    quotientMatrix q (extraRelatorMap v r) = extraRelatorMap (fun s => q (v s)) r := by
  apply Finsupp.lhom_ext
  rintro ⟨g,i⟩ n
  simp only [quotientMatrix_single, extraRelatorMap_single, one_smul]
  rw [← projectExtraChains_quotient, pathChain_quotient,
    ← projectExtraChains_translate, pathChain_translate, map_one, mul_one]

/-- The exponent minor used on a finite quotient is a consequence of the
ordinary projected boundary isomorphism itself; no independent rank hypothesis
and no unproved flatness claim is inserted. -/
theorem finite_extra_boundary_minor {I : Type*} [Fintype I] [DecidableEq I]
    (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
    (hA : A.toLinearMap = extraRelatorMap v r) (q : Γ →* D) (j : I ↪ D × R) :
    ∃ e : I → D × T, Function.Injective e ∧
      Matrix.det (fun i k => projectExtraChains
        (pathChain (fun s => q (v s)) (r (j i).2) (j i).1) (e k)) ≠ 0 := by
  let B := quotientChainEquiv q A (by rw [hA]; exact extraRelatorMap_equivariant v r)
  obtain ⟨e,he,hd⟩ := basis_subfamily_minor B j
  refine ⟨e,he,?_⟩
  have hB : B.toLinearMap = extraRelatorMap (fun s => q (v s)) r := by
    change quotientMatrix q A.toLinearMap = _
    rw [hA, extraRelatorMap_quotientMatrix]
  have hb (i : I) : B (Finsupp.single (j i) 1) = projectExtraChains
        (pathChain (fun s => q (v s)) (r (j i).2) (j i).1) := by
    change B.toLinearMap _ = _
    rw [hB]
    rcases j i with ⟨g,k⟩
    simp
  simpa only [hb] using hd

end ChainProjection
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section FiniteQuotientEquations
variable {Γ F S T R Z : Type*} [Group Γ] [Group F]

/-- The exponent of a literal edge is exactly its cellular path coefficient. -/
theorem pathSpelling_exponent [DecidableEq F] [DecidableEq S]
    (v : S → F) (w : FreeGroup S) (g : F) (e : F × S) :
    wordExponents (pathSpelling v w g) e = pathChain v w g e := by
  have he : (FreeGroup.lift (fun i : F × S =>
      Multiplicative.ofAdd (if e = i then (1 : ℤ) else 0))) =
      (Finsupp.applyAddHom e).toMultiplicative.comp
        (FreeGroup.lift (fun i : F × S => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)))) := by
    apply FreeGroup.ext_hom
    intro i
    simp [Finsupp.single_apply, eq_comm]
  simp only [wordExponents, he, MonoidHom.comp_apply, pathSpelling_abelianization]
  rfl

omit [Group F] in
/-- Projection to the extra alphabet really deletes only the prescribed edges. -/
theorem projectExtraChains_apply (c : BasedChains F (S ⊕ T)) (e : F × T) :
    projectExtraChains c e = c (e.1, Sum.inr e.2) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single p n =>
      rcases p with ⟨g,s | t⟩
      · simp
      · simp [Finsupp.single_apply, Prod.ext_iff]

/-- Sup norm agrees with the zero-normalized supremum, including an empty index. -/
theorem norm_eq_familySize {I : Type*} [Fintype I] (f : I → ℍ) :
    ‖f‖ = familySize (fun i => ‖f i‖) := by
  have hb : BddAbove (Set.range (fun i => ‖f i‖)) := Set.finite_range _ |>.bddAbove
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (familySize_nonneg _ hb)).mpr
      (fun i => le_familySize _ hb i)
  · exact familySize_le _ (norm_nonneg _) (fun i => norm_le_pi_norm f i)

/-- Reindexing does not change the actual supremum norm of a finite word family. -/
theorem norm_comp_equiv {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) (f : J → ℍ) :
    ‖fun i => f (e i)‖ = ‖f‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm f (e i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => by
      simpa using norm_le_pi_norm (fun i => f (e i)) (e.symm j)

end FiniteQuotientEquations
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section FiniteQuotientSolvability
variable {F S T R Z : Type*} [Group F] [Fintype F] [Fintype Z]

/-- The full finite quotient step. All coefficients on the prescribed alphabet
are retained exactly, not merely up to a small perturbation. -/
theorem finite_quotient_comparison_solvable
    (v : S ⊕ T → F) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
    (A : Finset R) (B : Finset R) (hAB : A ⊆ B)
    (Q : BasedChains F R ≃ₗ[ℤ] BasedChains F T)
    (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i)))
    (C δ η : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1)
    (hc₁ : C*(δ+η) < 1/2) (hc₂ : C*η < δ/2)
    (hcomp : ∀ (b : F → S ⊕ T → SU2) (h : ℝ), 0 ≤ h →
      (∀ g s, ‖(b g (.inl s) : ℍ)-1‖ ≤ η) →
      (∀ i ∈ A, ∀ g, pathProduct (H := SU2) v b (r (.inr i)) g = 1) →
      (∀ i g, ‖(pathProduct (H := SU2) v b (r (.inl i)) g : ℍ)-1‖ ≤ h) →
      ∀ i g,
        ‖(pathProduct (H := SU2) v b (FreeGroup.map Sum.inl (z i)) g : ℍ) -
          (pathProduct (H := SU2) v b (r (.inl i)) g : ℍ)‖ ≤ C*(η+h)*h ∧
        ‖(pathProduct (H := SU2) v b (FreeGroup.map Sum.inl (z i)) g : ℍ)-1‖ ≤ C*η)
    (a : F → S → SU2) (ha : ∀ g s, ‖(a g s : ℍ)-1‖ < η) :
    ∃ b : F → T → SU2,
      (∀ i ∈ B, ∀ g, pathProduct (H := SU2) v (mergeLabels a b) (r (.inr i)) g = 1) ∧
      (∀ i g, ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)-1‖ < δ) := by
  classical
  let I := F × ↥B
  let J := F × Z
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let j : Fin (Fintype.card I) ↪ F × R :=
    ⟨fun k => ((eI k).1, (eI k).2.val), fun k l h => by
      apply eI.injective
      exact Prod.ext (congrArg (fun p : F × R => p.1) h) (Subtype.ext (congrArg (fun p : F × R => p.2) h))⟩
  obtain ⟨e,he,hd⟩ := finite_extra_boundary_minor v (fun i => r (.inr i)) Q hQ
    (MonoidHom.id F) j
  let σ : Fin (Fintype.card I) ↪ F × (S ⊕ T) :=
    ⟨fun k => ((e k).1, .inr (e k).2), fun k l h =>
      he (Prod.ext (congrArg (fun p : F × (S ⊕ T) => p.1) h)
        (Sum.inr_injective (congrArg (fun p : F × (S ⊕ T) => p.2) h)))⟩
  let w : Fin (Fintype.card I) → FreeGroup (F × (S ⊕ T)) :=
    fun k => pathSpelling v (r (.inr (eI k).2.val)) (eI k).1
  let ρ : Fin (Fintype.card J) → FreeGroup (F × (S ⊕ T)) :=
    fun k => pathSpelling v (r (.inl (eJ k).2)) (eJ k).1
  have hdet : Matrix.det (fun i k => wordExponents (w i) (σ k)) ≠ 0 := by
    simp only [projectExtraChains_apply, MonoidHom.id_apply] at hd
    simp only [w, pathSpelling_exponent]
    exact hd
  let base : F × (S ⊕ T) → SU2 := fun p => Sum.elim (a p.1) (fun _ => 1) p.2
  have hbase (p) : ‖(base p : ℍ)-1‖ < 1 := by
    rcases p with ⟨g,s | t⟩
    · exact (ha g s).trans hη1
    · simp [base]
  let arc : ℝ → F × (S ⊕ T) → SU2 := fun t p => smallQuaternionArc (base p) t
  let L (t : ℝ) (x : Fin (Fintype.card I) → SU2) : F → S ⊕ T → SU2 :=
    fun g s => selectedLabel σ (arc t) x (g,s)
  have hleft (g : F) (s : S) (k : Fin (Fintype.card I)) : σ k ≠ (g,.inl s) := by
    change ((e k).1, Sum.inr (e k).2) ≠ (g,Sum.inl s)
    simp
  have hsmall (t : ℝ) (x : Fin (Fintype.card I) → SU2) (g : F) (s : S) :
      ‖(L t x g (.inl s) : ℍ)-1‖ ≤ η := by
    dsimp only [L]
    rw [selectedLabel_other σ _ x _ (hleft g s)]
    exact (smallQuaternionArc_distance (base (g,.inl s)) (hbase _) t).trans (ha g s).le
  have hword (b : F × (S ⊕ T) → SU2) (r : FreeGroup (S ⊕ T)) (g : F) :
      FreeGroup.lift b (pathSpelling v r g) = pathProduct (H := SU2) v (fun g s => b (g,s)) r g :=
    pathSpelling_eval v (fun g s => b (g,s)) r g
  obtain ⟨b,hfixed,hw,hρ⟩ := selected_word_sublevel_solvable σ w ρ arc
    (fun p => smallQuaternionArc_smooth _ (hbase p)) (by intro p; simp [arc])
    hdet δ hδ (fun t _ x hx => by
      let f : J → ℍ := fun p => (pathProduct (H := SU2) v (L t x) (r (.inl p.2)) p.1 : ℍ)-1
      have hordinary (i : R) (hi : i ∈ B) (g : F) :
          pathProduct (H := SU2) v (L t x) (r (.inr i)) g = 1 := by
        have h := hx (eI.symm (g,⟨i,hi⟩))
        simpa only [w, Equiv.apply_symm_apply, hword] using h
      have hb (i : Z) (g : F) : ‖(pathProduct (H := SU2) v (L t x) (r (.inl i)) g : ℍ)-1‖ ≤
          C*η + C*(‖f‖+η)*‖f‖ := by
        obtain ⟨h₁,h₂⟩ := hcomp (L t x) ‖f‖ (norm_nonneg _) (hsmall t x)
          (fun i hi => hordinary i (hAB hi))
          (fun i g => norm_le_pi_norm f (g,i)) i g
        have htri := norm_sub_le_norm_sub_add_norm_sub (pathProduct (H := SU2) v (L t x) (r (.inl i)) g : ℍ)
          (pathProduct (H := SU2) v (L t x) (FreeGroup.map Sum.inl (z i)) g : ℍ) 1
        calc
          _ ≤ C*(η+‖f‖)*‖f‖ + C*η := htri.trans (add_le_add ((norm_sub_rev _ _).trans_le h₁) h₂)
          _ = _ := by ring
      have hne : ‖f‖ ≠ δ := by
        rw [norm_eq_familySize]
        exact familySize_ne_threshold (fun p : J => ‖f p‖) (Set.finite_range _ |>.bddAbove)
          C δ η η hδ hC hη.le hη.le le_rfl hc₁ hc₂ (fun p => by
            simpa only [← norm_eq_familySize] using hb p.2 p.1)
      have heq : ‖(fun k => (FreeGroup.lift (selectedLabel σ (arc t) x) (ρ k) : ℍ))-1‖ = ‖f‖ := by
        change ‖fun k => (FreeGroup.lift (selectedLabel σ (arc t) x) (ρ k) : ℍ)-1‖ = _
        simpa only [ρ, hword, f, L] using norm_comp_equiv eJ f
      intro h
      exact hne (heq.symm.trans h))
  let b' : F → T → SU2 := fun g t => b (g,.inr t)
  have heval : (fun g s => b (g,s)) = mergeLabels a b' := by
    funext g s
    rcases s with s | t
    · rw [hfixed _ (hleft g s)]
      simp [arc, base, mergeLabels]
    · rfl
  refine ⟨b',?_,?_⟩
  · intro i hi g
    have h := hw (eI.symm (g,⟨i,hi⟩))
    simpa only [w, Equiv.apply_symm_apply, hword, heval] using h
  · intro i g
    have h := (norm_le_pi_norm
      ((fun k => (FreeGroup.lift b (ρ k) : ℍ))-1) (eJ.symm (g,i))).trans_lt hρ
    simpa only [ρ, Pi.sub_apply, Pi.one_apply, Equiv.apply_symm_apply, hword, heval] using h

end FiniteQuotientSolvability
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section AlignedComparison
variable {Γ : Type u} {S T Z R : Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]

omit [Group.ResiduallyFinite Γ] in
theorem wordValue_map_alphabet {E : Type*} (v : S → Γ) (f : E → S) (w : FreeGroup E) :
    wordValue v (FreeGroup.map f w) = wordValue (fun e => v (f e)) w := by
  have he : (wordValue v).comp (FreeGroup.map f) = wordValue (fun e => v (f e)) := by
    apply FreeGroup.ext_hom
    intro e
    simp [wordValue]
  exact congrArg (fun h : FreeGroup E →* Γ => h w) he

/-- The algebraic core of the manuscript's presentation comparison, for an
actual aligned presentation. The passage from arbitrary ordinary CW classifying
spaces to this presentation is a separate topological obligation. -/
theorem aligned_presentation_small_transport
    (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
    (hvT : ∀ t, v (.inr t) = 1)
    (hr : ∀ i, wordValue v (r i) = 1)
    (hz : ∀ i, wordValue (fun s => v (.inl s)) (z i) = 1)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r))
    (hinj : Function.Injective (relatorChainMap v r))
    (hchain : ∀ i, pathChain v (FreeGroup.map Sum.inl (z i)) 1 = pathChain v (r (.inl i)) 1)
    (Q : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
    (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i))) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
      (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
      (∀ i g, pathProduct (fun s => v (.inl s)) a (z i) g = 1) →
      ∀ w : FreeGroup S, wordValue (fun s => v (.inl s)) w = 1 → ∀ g,
        pathProduct (fun s => v (.inl s)) a w g = 1 := by
  classical
  have hzn (i) : FreeGroup.map Sum.inl (z i) ∈ Subgroup.normalClosure (Set.range r) := by
    rw [← hp]
    change wordValue v (FreeGroup.map Sum.inl (z i)) = 1
    rw [wordValue_map_alphabet, hz]
  have htn (t) : FreeGroup.of (.inr t) ∈ Subgroup.normalClosure (Set.range r) := by
    rw [← hp]
    change wordValue v (FreeGroup.of (.inr t)) = 1
    simpa [wordValue] using hvT t
  choose lz hlz using fun i => exists_normalExpression r (hzn i)
  choose lt hlt using fun t => exists_normalExpression r (htn t)
  have hc (i) : ((lz i).map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,Sum.inl i) 1 :=
    exact_translated_relator_counts v r hr hinj _ (.inl i) (hchain i) (lz i) (hlz i)
  obtain ⟨A,C,hC,hcomp⟩ := finite_normal_comparison v r hr z lz lt hlz hlt hc
  obtain ⟨δ,η,hδ,hδ1,hη,hη1,hc₁,hc₂⟩ := small_thresholds_exist C hC
  refine ⟨η,hη,?_⟩
  intro a ha haz
  let W : Γ × (Z ⊕ R) → FreeGroup (S ⊕ T) := fun p => r p.2
  let K : Γ × (Z ⊕ R) → Set SU2 := fun p => match p.2 with
    | .inl _ => {b | ‖(b : ℍ)-1‖ ≤ δ}
    | .inr _ => {1}
  have hK (p) : IsClosed (K p) := by
    rcases p with ⟨g,i | i⟩
    · exact isClosed_le ((continuous_subtype_val.sub continuous_const).norm) continuous_const
    · exact isClosed_singleton
  obtain ⟨b,hb⟩ := compact_labeling_from_finite_quotients v a W Prod.fst K hK
    (fun b : SU2 => ‖(b : ℍ)-1‖ < η) (by simpa using hη) ha (by
      intro N J aF haF
      let : Fintype (Γ ⧸ N.toSubgroup) := Fintype.ofFinite _
      let q := QuotientGroup.mk' N.toSubgroup
      let B := A ∪ (J.image Prod.snd).toRight
      let QF := quotientChainEquiv q Q (by rw [hQ]; exact extraRelatorMap_equivariant _ _)
      have hQF : QF.toLinearMap = extraRelatorMap (fun s => q (v s)) (fun i => r (.inr i)) := by
        change quotientMatrix q Q.toLinearMap = _
        rw [hQ, extraRelatorMap_quotientMatrix]
      obtain ⟨bF,hord,hdis⟩ := finite_quotient_comparison_solvable (fun s => q (v s)) r z A B
        (Finset.subset_union_left) QF hQF C δ η (by linarith) hδ hη hη1 hc₁ hc₂
        (fun b h hh hsmall hord hdist => hcomp q b η h hη.le hh hsmall hord hdist) aF haF
      refine ⟨bF,?_⟩
      rintro ⟨g,i | i⟩ hi d
      · exact (hdis i d).le
      · exact hord i (Finset.mem_union_right _ (Finset.mem_toRight.mpr
          (Finset.mem_image.mpr ⟨(g,.inr i),hi,rfl⟩))) d)
  have hord (i : R) (g : Γ) : pathProduct v (mergeLabels a b) (r (.inr i)) g = 1 :=
    hb (g,.inr i)
  have hdis (i : Z) (g : Γ) : ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)-1‖ ≤ δ :=
    hb (g,.inl i)
  let f : Z × Γ → ℝ := fun p => ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl p.1)) p.2 : ℍ)-1‖
  have hbounded : BddAbove (Set.range f) := ⟨δ, by rintro _ ⟨⟨i,g⟩,rfl⟩; exact hdis i g⟩
  have hzero : ∀ p, f p = 0 := familySize_contraction f (fun _ => norm_nonneg _)
    δ C η hδ.le (by linarith) hη.le (fun p => hdis p.1 p.2) (by linarith) (by
      rintro ⟨i,g⟩
      have h := (hcomp (MonoidHom.id Γ) (mergeLabels a b) η (familySize f) hη.le
        (familySize_nonneg f hbounded) (fun g s => (ha g s).le) (fun i _ => hord i)
        (fun i g => le_familySize f hbounded (i,g)) i g).1
      have hz' : pathProduct v (mergeLabels a b) (FreeGroup.map Sum.inl (z i)) g = 1 := by
        rw [pathProduct_map_alphabet]
        exact haz i g
      change ‖(pathProduct (H := SU2) v (mergeLabels a b) (FreeGroup.map Sum.inl (z i)) g : ℍ)-
        (pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)‖ ≤ _ at h
      rw [hz'] at h
      change ‖(1 : ℍ) - (pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)‖ ≤
        C * (η + familySize f) * familySize f at h
      change ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ) - 1‖ ≤
        C * (familySize f + η) * familySize f
      rw [norm_sub_rev]
      rwa [add_comm η (familySize f)] at h)
  have hdist (i : Z) (g : Γ) : pathProduct v (mergeLabels a b) (r (.inl i)) g = 1 := by
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp (hzero (i,g)))
  intro w hw g
  have hw' : wordValue v (FreeGroup.map Sum.inl w) = 1 := by
    rw [wordValue_map_alphabet, hw]
  have h := pathProduct_trivial_of_relators v (mergeLabels a b) (Set.range r)
    (by rintro _ ⟨i,rfl⟩; exact hr i) hp
    (by rintro _ ⟨i | i,rfl⟩ g; exact hdist i g; exact hord i g)
    (FreeGroup.map Sum.inl w) hw' g
  simpa only [pathProduct_map_alphabet, mergeLabels, Sum.elim_inl, Function.comp_def] using h

end AlignedComparison
end EilenbergGanea

end

end OAI

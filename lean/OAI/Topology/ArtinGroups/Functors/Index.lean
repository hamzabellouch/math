import Mathlib
import OAI.Topology.ArtinGroups.Quivers.VertexLinear
import OAI.Topology.ArtinGroups.Functors.PathImage

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
local notation "P" => pathImage Q step hstep N hN orient μ A

lemma linearMap_apply (x : Zigzag U K) (i j : I) :
    F x i j = ∑ p, Zigzag.pathCoordinates U x p • P p i j := by
  conv_lhs => rw [← Zigzag.sum_pathBasis U x]
  simp only [map_sum,map_smul,linearMap_pathBasis,Matrix.sum_apply,Matrix.smul_apply]

lemma linearMap_left (x : Zigzag U K) (i j : I) :
    Zigzag.vertexId U i.new * F x i j = F x i j := by
  rw [linearMap_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Algebra.mul_smul_comm,pathImage_left]

lemma linearMap_right (x : Zigzag U K) (i j : I) :
    F x i j * Zigzag.vertexId U j.new = F x i j := by
  rw [linearMap_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_assoc,pathImage_right]

lemma pathImage_homogeneous (p : Path (V × J) (StringArrow step N)) (i j : I) :
    Zigzag.Homogeneous U (Path.length p) (P p i j) := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage,Path.length]
    split_ifs
    · exact Zigzag.homogeneous_vertexId U _
    · exact Zigzag.homogeneous_zero U _
  · simp only [pathImage,arrowImage,Path.length]
    split_ifs
    all_goals first | exact Zigzag.homogeneous_zero U _ |
      exact Zigzag.homogeneous_smul U (by
        rw [← Zigzag.pathBasis_arrow]
        exact Zigzag.pathBasis_homogeneous (K := K) U (.inr (.inl _))) _
  · simp only [pathImage,tokenImage,Path.length]
    split_ifs
    · exact Zigzag.homogeneous_smul U (by
        rw [← Zigzag.pathBasis_token]
        exact Zigzag.pathBasis_homogeneous (K := K) U (.inr (.inr i.new))) _
    · exact Zigzag.homogeneous_zero U _

lemma linearMap_homogeneous {x : Zigzag U K} {a : ℤ}
    (hx : Zigzag.Homogeneous U a x) (i j : I) :
    Zigzag.Homogeneous U a (F x i j) := by
  rw [linearMap_apply]
  apply Zigzag.homogeneous_sum
  intro p hp
  by_cases ha : Path.length p=a
  · rw [← ha]
    exact Zigzag.homogeneous_smul U
      (pathImage_homogeneous Q step hstep N hN orient μ A p i j) _
  · rw [(Zigzag.coordinates_homogeneous U a x).1 hx p ha,zero_smul]
    exact Zigzag.homogeneous_zero U _

lemma linearMap_support {x : Zigzag U K} {a b : V × J}
    (hx : Zigzag.vertexId U a * x = x) (hy : x * Zigzag.vertexId U b = x)
    (i j : I) (h : i.old ≠ a ∨ j.old ≠ b) : F x i j = 0 := by
  rw [linearMap_apply]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hc : Zigzag.pathCoordinates U x p=0
  · rw [hc,zero_smul]
  · have hs := Zigzag.coordinates_corner U hx hy hc
    rw [pathImage_support Q step hstep N hN orient μ A p i j (by simpa [hs.1,hs.2] using h),smul_zero]

lemma linearMap_positive {x : Zigzag U K} (hx : x.vertex = 0) (i j : I) :
    (F x i j).vertex = 0 := by
  rw [linearMap_apply,Zigzag.vertex_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Zigzag.vertex_smul]
  by_cases hn : Path.length p ≠ 0
  · rw [pathImage_positive Q step hstep N hN orient μ A p hn i j,smul_zero]
  · have hc : Zigzag.pathCoordinates U x p = 0 := by
      rcases p with a|p|a
      · exact congrFun hx a
      · exact (hn (by norm_num [Path.length])).elim
      · exact (hn (by norm_num [Path.length])).elim
    rw [hc,zero_smul]

abbrev Index {T : Type*} (p : T → GeneratorPlacement (V × J)) :=
  (i : T) × {c : J // N (p i).color.2 c}

def indexEmbed {T : Type*} (p : T → GeneratorPlacement (V × J))
    (i : Index N p) : I := ⟨((p i.1).color,i.2),i.2.property⟩

def placement {T : Type*} (p : T → GeneratorPlacement (V × J)) :
    Index N p → GeneratorPlacement (V × J) :=
  fun i => ⟨((p i.1).color.1,i.2),(p i.1).cochain,(p i.1).internal⟩

noncomputable def matrix {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) :
    Matrix (Index N p) (Index N q) (Zigzag U K) :=
  fun i j => F (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)

lemma matrix_zero {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) :
    matrix Q step hstep N hN orient μ A p q 0 = 0 := by
  apply Matrix.ext
  intro i j
  exact congrFun (congrFun ((F).map_zero) (indexEmbed N p i)) (indexEmbed N q j)

lemma matrix_add {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M L : Matrix T R (Zigzag U K)) :
    matrix Q step hstep N hN orient μ A p q (M+L) =
      matrix Q step hstep N hN orient μ A p q M + matrix Q step hstep N hN orient μ A p q L := by
  apply Matrix.ext
  intro i j
  exact congrFun (congrFun ((F).map_add (M i.1 j.1) (L i.1 j.1)) (indexEmbed N p i)) (indexEmbed N q j)

lemma matrix_smul {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) (c : K) :
    matrix Q step hstep N hN orient μ A p q (c • M) =
      c • matrix Q step hstep N hN orient μ A p q M := by
  apply Matrix.ext
  intro i j
  exact congrFun (congrFun ((F).map_smul c (M i.1 j.1)) (indexEmbed N p i)) (indexEmbed N q j)

lemma matrix_entries {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) :
    Zigzag.ProjectiveEntries U (placement N p) (placement N q)
      (matrix Q step hstep N hN orient μ A p q M) := by
  constructor
  · intro i j
    exact linearMap_left Q step hstep N hN orient μ A (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)
  · intro i j
    exact linearMap_right Q step hstep N hN orient μ A (M i.1 j.1) (indexEmbed N p i) (indexEmbed N q j)

lemma matrix_degree {T R : Type*} (p : T → GeneratorPlacement (V × J))
    (q : R → GeneratorPlacement (V × J)) (M : Matrix T R (Zigzag U K)) {n v : ℤ}
    (hM : Zigzag.MapDegree U p q n v M) :
    Zigzag.MapDegree U (placement N p) (placement N q) n v
      (matrix Q step hstep N hN orient μ A p q M) := by
  intro i j
  constructor
  · intro h
    have hz := (hM i.1 j.1).1 h
    change F (M i.1 j.1) _ _ = 0
    rw [hz,map_zero]; rfl
  · exact linearMap_homogeneous Q step hstep N hN orient μ A (hM i.1 j.1).2 _ _

lemma matrix_mul {T R L : Type*} [Fintype R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : T → GeneratorPlacement (V × J)) (q : R → GeneratorPlacement (V × J))
    (r : L → GeneratorPlacement (V × J))
    (M : Matrix T R (Zigzag U K)) (D : Matrix R L (Zigzag U K))
    (hM : Zigzag.ProjectiveEntries U p q M) :
    matrix Q step hstep N hN orient μ A p r (M*D) =
      matrix Q step hstep N hN orient μ A p q M * matrix Q step hstep N hN orient μ A q r D := by
  apply Matrix.ext
  intro i k
  simp only [matrix,Matrix.mul_apply,map_sum,Matrix.sum_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [linearMap_mul Q step hstep N hN orient ho μ hμ δ A hA hroot hPF,Matrix.mul_apply]
  have hh : ∀ l : I,
      F (M i.1 j) (indexEmbed N p i) l * F (D j k.1) l (indexEmbed N r k) =
      if l.old=(q j).color then
        F (M i.1 j) (indexEmbed N p i) l * F (D j k.1) l (indexEmbed N r k) else 0 := by
    intro l
    by_cases hl : l.old=(q j).color
    · exact (ite_eq_left hl).symm
    · rw [ite_eq_right hl,linearMap_support Q step hstep N hN orient μ A (hM.1 _ _) (hM.2 _ _)
        _ l (Or.inr hl),zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => hh l)]
  rw [sum_over N ((q j).color)]
  rfl

lemma matrix_identity {T : Type*} [DecidableEq T]
    (p : T → GeneratorPlacement (V × J)) :
    matrix Q step hstep N hN orient μ A p p (Zigzag.projectiveIdentity U p) =
      Zigzag.projectiveIdentity U (placement N p) := by
  apply Matrix.ext
  rintro ⟨i,c⟩ ⟨j,d⟩
  by_cases hij : i=j
  · subst j
    by_cases hcd : c=d
    · subst d
      simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_true,
        ← Zigzag.pathBasis_vertex,linearMap_pathBasis,pathImage,unitImage]
      rw [ite_eq_left (by simp [indexEmbed,StringIndex.old])]
      simp only [Zigzag.pathBasis_vertex]
      rfl
    · have hind : (⟨i,c⟩ : Index N p) ≠ ⟨i,d⟩ := by simpa using hcd
      have hem : indexEmbed N p ⟨i,c⟩ ≠ indexEmbed N p ⟨i,d⟩ := by
        intro he
        apply hcd
        exact Subtype.ext (congrArg StringIndex.label he)
      simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_true,ite_eq_right hind,
        ← Zigzag.pathBasis_vertex,linearMap_pathBasis,pathImage,unitImage]
      rw [ite_eq_right (fun h => hem h.1)]
  · have hind : (⟨i,c⟩ : Index N p) ≠ ⟨j,d⟩ := fun h => hij (congrArg Sigma.fst h)
    simp only [matrix,Zigzag.projectiveIdentity,Matrix.diagonal_apply,ite_eq_right hij,ite_eq_right hind,map_zero]
    rfl

noncomputable def complex {T : Type*} [Fintype T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (E : Zigzag.BasedComplex U (K := K) T) :
    Zigzag.BasedComplex U (K := K) (Index N E.placement) where
  placement := placement N E.placement
  differential := matrix Q step hstep N hN orient μ A _ _ E.differential
  entries := matrix_entries Q step hstep N hN orient μ A _ _ _
  degree := matrix_degree Q step hstep N hN orient μ A _ _ _ E.degree
  square_zero := by
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      E.placement E.placement E.placement E.differential E.differential E.entries]
    rw [E.square_zero,matrix_zero]

lemma complex_minimal {T : Type*} [Fintype T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) :
    (complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E).IsMinimal U := by
  intro i j
  exact linearMap_positive Q step hstep N hN orient μ A (hE i.1 j.1)
    (indexEmbed N E.placement i) (indexEmbed N E.placement j)

section Functorial
variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    {T R L : Type*} [Fintype T] [Fintype R] [Fintype L]

local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => matrix Q step hstep N hN orient μ A

noncomputable def map {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Zigzag.BasedComplex.Map U (C E) (C D) where
  matrix := M E.placement D.placement f.matrix
  entries := matrix_entries Q step hstep N hN orient μ A _ _ _
  degree := matrix_degree Q step hstep N hN orient μ A _ _ _ f.degree
  commute := by
    change M _ _ E.differential * M _ _ f.matrix = M _ _ f.matrix * M _ _ D.differential
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries,
      ← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ f.entries,
      f.commute]

lemma map_comp {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} {G : Zigzag.BasedComplex U (K := K) L}
    (f : Zigzag.BasedComplex.Map U E D) (g : Zigzag.BasedComplex.Map U D G) :
    (map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (Zigzag.BasedComplex.Map.comp U f g)).matrix =
    (Zigzag.BasedComplex.Map.comp U
      (map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF f)
      (map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF g)).matrix := by
  exact matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ f.entries

lemma map_identity [DecidableEq T] (E : Zigzag.BasedComplex U (K := K) T) :
    (map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (Zigzag.BasedComplex.Map.identity U E)).matrix =
      (Zigzag.BasedComplex.Map.identity U (C E)).matrix := by
  exact matrix_identity Q step hstep N hN orient μ A _

noncomputable def homotopyEquivalence [DecidableEq T] [DecidableEq R]
    {E : Zigzag.BasedComplex U (K := K) T} {D : Zigzag.BasedComplex U (K := K) R}
    (h : Zigzag.BasedComplex.HomotopyEquivalence U E D) :
    Zigzag.BasedComplex.HomotopyEquivalence U (C E) (C D) where
  forward := map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF h.forward
  backward := map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF h.backward
  sourceHomotopy := M E.placement E.placement h.sourceHomotopy
  targetHomotopy := M D.placement D.placement h.targetHomotopy
  sourceEntries := matrix_entries Q step hstep N hN orient μ A _ _ _
  targetEntries := matrix_entries Q step hstep N hN orient μ A _ _ _
  sourceDegree := matrix_degree Q step hstep N hN orient μ A _ _ _ h.sourceDegree
  targetDegree := matrix_degree Q step hstep N hN orient μ A _ _ _ h.targetDegree
  sourceEquation := by
    change M _ _ h.forward.matrix * M _ _ h.backward.matrix = _
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.forward.entries,
      h.sourceEquation,matrix_add,matrix_add,matrix_identity,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.sourceEntries]
    rfl
  targetEquation := by
    change M _ _ h.backward.matrix * M _ _ h.forward.matrix = _
    rw [← matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.backward.entries,
      h.targetEquation,matrix_add,matrix_add,matrix_identity,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ D.entries,
      matrix_mul Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ h.targetEntries]
    rfl
end Functorial

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI

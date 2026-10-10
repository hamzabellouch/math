import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Crossing
import OAI.Topology.ArtinGroups.Quivers.VertexIdMulPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V B J K : Type*} (Q : ReversibleQuiver V B)

abbrev StringArrow (step : B → Bool) (N : J → J → Prop) :=
  {p : B × J × J // if step p.1 then N p.2.1 p.2.2 else p.2.1 = p.2.2}

namespace StringArrow
variable {N : J → J → Prop} {step : B → Bool}

def base (p : StringArrow step N) : B := p.1.1
def left (p : StringArrow step N) : J := p.1.2.1
def right (p : StringArrow step N) : J := p.1.2.2

@[ext] lemma ext {p q : StringArrow step N}
    (hb : p.base=q.base) (hl : p.left=q.left) (hr : p.right=q.right) : p=q := by
  apply Subtype.ext
  exact Prod.ext hb (Prod.ext hl hr)

end StringArrow

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)

def stringQuiver : ReversibleQuiver (V × J) (StringArrow step N) where
  source p := (Q.source p.base,p.left)
  target p := (Q.target p.base,p.right)
  reverse :=
    { toFun p := ⟨(Q.reverse p.base,p.right,p.left),by
        have hp := p.property
        change (if step p.base then N p.left p.right else p.left=p.right) at hp
        change (if step (Q.reverse p.base) then N p.right p.left else p.right=p.left)
        rw [hstep]
        cases hs : step p.base <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at *
        · exact hp.symm
        · exact hN hp⟩
      invFun p := ⟨(Q.reverse p.base,p.right,p.left),by
        have hp := p.property
        change (if step p.base then N p.left p.right else p.left=p.right) at hp
        change (if step (Q.reverse p.base) then N p.right p.left else p.right=p.left)
        rw [hstep]
        cases hs : step p.base <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at *
        · exact hp.symm
        · exact hN hp⟩
      left_inv p := by apply StringArrow.ext <;> simp [StringArrow.base,StringArrow.left,StringArrow.right]
      right_inv p := by apply StringArrow.ext <;> simp [StringArrow.base,StringArrow.left,StringArrow.right] }
  reverse_reverse p := by
    apply StringArrow.ext
    · exact Q.reverse_reverse p.base
    · rfl
    · rfl
  source_reverse p := Prod.ext (Q.source_reverse p.base) rfl
  target_reverse p := Prod.ext (Q.target_reverse p.base) rfl

abbrev StringIndex := {p : (V × J) × J // N p.1.2 p.2}

namespace StringIndex
variable {N}
def old (i : StringIndex (V := V) N) : V × J := i.1.1
def label (i : StringIndex (V := V) N) : J := i.1.2
def new (i : StringIndex (V := V) N) : V × J := (i.old.1,i.label)
@[ext] lemma ext {i j : StringIndex (V := V) N}
    (ho : i.old=j.old) (hl : i.label=j.label) : i=j := Subtype.ext (Prod.ext ho hl)
end StringIndex

namespace StringFunctor

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N

def coefficient (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (c d : J) : K :=
  if step p.base then GraphConnection.crossing μ A p.left p.right c d
  else if c=d then (if orient p.base then μ c / μ p.left else 1) else 0

noncomputable def unitImage (a : V × J) : Matrix I I (Zigzag U K) :=
  fun i j => if i=j ∧ i.old=a then Zigzag.vertexId U i.new else 0

noncomputable def tokenImage (μ : J → K) (a : V × J) : Matrix I I (Zigzag U K) :=
  fun i j => if i=j ∧ i.old=a then (μ i.label / μ a.2) • Zigzag.tokenBasis U i.new else 0

noncomputable def arrowImage (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) : Matrix I I (Zigzag U K) :=
  fun i j => if i.old=(U).source p ∧ j.old=(U).target p then
    if h : (if step p.base then N i.label j.label else i.label=j.label) then
      coefficient step N orient μ A p i.label j.label •
        Zigzag.arrowBasis U (⟨(p.base,i.label,j.label),h⟩ : StringArrow step N)
    else 0
  else 0

omit [DecidableEq B] in
lemma unitImage_mul (a : V × J) (M : Matrix I I (Zigzag U K))
    (hM : ∀ i j, Zigzag.vertexId U i.new * M i j = M i j) (i j : I) :
    (unitImage (K := K) Q step hstep N hN a * M) i j = if i.old=a then M i j else 0 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single i]
  · simp only [unitImage,true_and]
    by_cases hi : i.old=a <;> simp [hi,hM]
  · intro k hk hki
    simp [unitImage,Ne.symm hki]
  · simp

omit [DecidableEq B] in
lemma mul_unitImage (a : V × J) (M : Matrix I I (Zigzag U K))
    (hM : ∀ i j, M i j * Zigzag.vertexId U j.new = M i j) (i j : I) :
    (M * unitImage (K := K) Q step hstep N hN a) i j = if j.old=a then M i j else 0 := by
  rw [Matrix.mul_apply,Finset.sum_eq_single j]
  · simp only [unitImage,true_and]
    by_cases hi : j.old=a <;> simp [hi,hM]
  · intro k hk hkj
    simp [unitImage,hkj]
  · simp

lemma arrowImage_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) :
    Zigzag.vertexId U i.new * arrowImage Q step hstep N hN orient μ A p i j =
      arrowImage Q step hstep N hN orient μ A p i j := by
  unfold arrowImage
  by_cases h : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right h,mul_zero]
  rw [ite_eq_left h]
  by_cases h' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right h',mul_zero]
  rw [dite_eq_left h']
  rw [Algebra.mul_smul_comm]
  congr 1
  let r : StringArrow step N := ⟨(p.base,i.label,j.label),h'⟩
  have hr : (U).source r=i.new := by
    apply Prod.ext
    · exact (congrArg Prod.fst h.1).symm
    · rfl
  change Zigzag.vertexId U i.new * Zigzag.arrowBasis U r = _
  rw [← hr, ← Zigzag.pathBasis_arrow]
  exact Zigzag.pathBasis_left U (.inr (.inl r))

lemma arrowImage_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) :
    arrowImage Q step hstep N hN orient μ A p i j * Zigzag.vertexId U j.new =
      arrowImage Q step hstep N hN orient μ A p i j := by
  unfold arrowImage
  by_cases h : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right h,zero_mul]
  rw [ite_eq_left h]
  by_cases h' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right h',zero_mul]
  rw [dite_eq_left h']
  rw [smul_mul_assoc]
  congr 1
  let r : StringArrow step N := ⟨(p.base,i.label,j.label),h'⟩
  have hr : (U).target r=j.new := by
    apply Prod.ext
    · exact (congrArg Prod.fst h.2).symm
    · rfl
  change Zigzag.arrowBasis U r * Zigzag.vertexId U j.new = _
  rw [← hr, ← Zigzag.pathBasis_arrow]
  exact Zigzag.pathBasis_right U (.inr (.inl r))

lemma unitImage_arrowImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : StringArrow step N) :
    unitImage Q step hstep N hN a * arrowImage Q step hstep N hN orient μ A p =
      if (U).source p=a then arrowImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [unitImage_mul Q step hstep N hN _ _ (arrowImage_left Q step hstep N hN _ _ _ _) i j]
  by_cases ha : (U).source p=a
  · rw [ite_eq_left ha]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      simp only [arrowImage]
      rw [ite_eq_right (fun h => hi (h.1.trans ha))]
  · rw [ite_eq_right ha]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi]
      simp only [arrowImage]
      rw [ite_eq_right (fun h => ha (h.1.symm.trans hi))]
      rfl
    · simp only [ite_eq_right hi,Matrix.zero_apply]

lemma arrowImage_unitImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : StringArrow step N) :
    arrowImage Q step hstep N hN orient μ A p * unitImage Q step hstep N hN a =
      if (U).target p=a then arrowImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [mul_unitImage Q step hstep N hN _ _ (arrowImage_right Q step hstep N hN _ _ _ _) i j]
  by_cases ha : (U).target p=a
  · rw [ite_eq_left ha]
    by_cases hj : j.old=a
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      simp only [arrowImage]
      rw [ite_eq_right (fun h => hj (h.2.trans ha))]
  · rw [ite_eq_right ha]
    by_cases hj : j.old=a
    · rw [ite_eq_left hj]
      simp only [arrowImage]
      rw [ite_eq_right (fun h => ha (h.2.symm.trans hj))]
      rfl
    · simp only [ite_eq_right hj,Matrix.zero_apply]

def liftIndex (a : V × J) (c : {c : J // N a.2 c}) : I := ⟨(a,c),c.property⟩

lemma sum_over {R : Type*} [AddCommMonoid R] (a : V × J) (f : I → R) :
    (∑ i : I, if i.old=a then f i else 0) = ∑ c : {c : J // N a.2 c}, f (liftIndex N a c) := by
  symm
  apply Fintype.sum_of_injective (liftIndex N a)
  · intro c d h
    apply Subtype.ext
    exact congrArg StringIndex.label h
  · intro i hi
    have hv : i.old ≠ a := by
      intro h
      apply hi
      refine ⟨⟨i.label,?_⟩,?_⟩
      · rw [← h]
        exact i.property
      · apply StringIndex.ext
        · exact h.symm
        · rfl
    exact ite_eq_right hv
  · intro c
    simp [liftIndex,StringIndex.old]

omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_base (p : StringArrow step N) :
    StringArrow.base ((U).reverse p) = Q.reverse p.base := rfl
omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_left (p : StringArrow step N) :
    StringArrow.left ((U).reverse p) = p.right := rfl
omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
@[simp] lemma reverse_right (p : StringArrow step N) :
    StringArrow.right ((U).reverse p) = p.left := rfl

omit [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] in
lemma reverse_eq_iff (p q : StringArrow step N) :
    (U).reverse p=q ↔ Q.reverse p.base=q.base ∧ p.right=q.left ∧ p.left=q.right := by
  constructor
  · intro h
    exact ⟨congrArg StringArrow.base h,congrArg StringArrow.left h,congrArg StringArrow.right h⟩
  · rintro ⟨h₁,h₂,h₃⟩
    exact StringArrow.ext h₁ h₂ h₃

omit [Fintype V] in
lemma arrowImage_eq_zero_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) (h : i.old ≠ (U).source p) :
    arrowImage Q step hstep N hN orient μ A p i j = 0 := by
  exact ite_eq_right (fun h' => h h'.1)

omit [Fintype V] in
lemma arrowImage_eq_zero_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (i j : I) (h : j.old ≠ (U).target p) :
    arrowImage Q step hstep N hN orient μ A p i j = 0 := by
  exact ite_eq_right (fun h' => h h'.2)

omit [Fintype V] in
lemma arrowImage_entry_mul_of_not_reverse (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (i j k : I)
    (h : Q.reverse p.base ≠ q.base ∨ i.label ≠ k.label) :
    arrowImage Q step hstep N hN orient μ A p i j *
      arrowImage Q step hstep N hN orient μ A q j k = 0 := by
  unfold arrowImage
  by_cases hp : i.old=(U).source p ∧ j.old=(U).target p
  swap
  · rw [ite_eq_right hp,zero_mul]
  rw [ite_eq_left hp]
  by_cases hq : j.old=(U).source q ∧ k.old=(U).target q
  swap
  · rw [ite_eq_right hq,mul_zero]
  rw [ite_eq_left hq]
  by_cases hp' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · rw [dite_eq_right hp',zero_mul]
  rw [dite_eq_left hp']
  by_cases hq' : (if step q.base then N j.label k.label else j.label=k.label)
  swap
  · rw [dite_eq_right hq',mul_zero]
  rw [dite_eq_left hq',smul_mul_assoc,Algebra.mul_smul_comm,Zigzag.arrowBasis_mul_arrowBasis]
  have hr : (U).reverse (⟨(p.base,i.label,j.label),hp'⟩ : StringArrow step N) ≠
      ⟨(q.base,j.label,k.label),hq'⟩ := by
    intro hh
    rcases (reverse_eq_iff Q step hstep N hN _ _).1 hh with ⟨hb,_,hl⟩
    rcases h with h | h
    · exact h hb
    · exact h hl
  rw [ite_eq_right hr,smul_zero,smul_zero]

lemma arrowImage_mul_of_not_reverse_base (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (h : Q.reverse p.base ≠ q.base) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q = 0 := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero (fun j _ => arrowImage_entry_mul_of_not_reverse
    Q step hstep N hN orient μ A p q i j k (Or.inl h))

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI

import OAI.RingTheory.DirectFiniteness.ParameterBounds

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype A]

/-- Full finite affine cosets; no subset or segment convention is used. -/
def cosetPoints (U : Submodule Q A) (x : A) : Finset A :=
  Finset.univ.filter (fun y => y - x ∈ U)

@[simp] lemma mem_cosetPoints (U : Submodule Q A) (x y : A) :
    y ∈ cosetPoints U x ↔ y - x ∈ U := by simp [cosetPoints]

lemma self_mem_cosetPoints (U : Submodule Q A) (x : A) : x ∈ cosetPoints U x := by simp

lemma cosetPoints_eq {U : Submodule Q A} {x y : A} (h : y - x ∈ U) :
    cosetPoints U y = cosetPoints U x := by
  ext z
  simp only [mem_cosetPoints]
  constructor
  · intro hz
    convert U.add_mem hz h using 1; abel
  · intro hz
    convert U.sub_mem hz h using 1; abel

lemma cosetPoints_image (U : Submodule Q A) (x : A) :
    cosetPoints U x = Finset.univ.image (fun u : U => x + (u : A)) := by
  ext y
  simp only [mem_cosetPoints, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hy
    exact ⟨⟨y - x, hy⟩, by simp⟩
  · rintro ⟨u, rfl⟩
    simp [u.property]

lemma card_cosetPoints (U : Submodule Q A) (x : A) :
    (cosetPoints U x).card = Fintype.card U := by
  rw [cosetPoints_image, Finset.card_image_of_injective, Finset.card_univ]
  intro i j hij
  exact Subtype.ext (add_left_cancel hij)

lemma intersection_cosets_card_le (U W : Submodule Q A) (x o : A) :
    ((cosetPoints U x) ∩ (cosetPoints W o)).card ≤ Fintype.card ↥(U ⊓ W) := by
  by_cases hn : ((cosetPoints U x) ∩ (cosetPoints W o)).Nonempty
  · obtain ⟨z, hz⟩ := hn
    have huz : z - x ∈ U := by simpa using (Finset.mem_inter.mp hz).1
    have hwz : z - o ∈ W := by simpa using (Finset.mem_inter.mp hz).2
    rw [← cosetPoints_eq huz, ← cosetPoints_eq hwz]
    have he : cosetPoints U z ∩ cosetPoints W z = cosetPoints (U ⊓ W) z := by
      ext y
      simp
    rw [he, card_cosetPoints]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]

/-- Two independent directions yield disjoint affine cosets or a single point. -/
lemma intersection_cosets_card_le_one (U W : Submodule Q A) (h : Disjoint U W) (x o : A) :
    ((cosetPoints U x) ∩ (cosetPoints W o)).card ≤ 1 := by
  have hc := intersection_cosets_card_le U W x o
  simpa [h.eq_bot] using hc

/-- A coset variable is its full point set, so no arbitrary representatives
enter the random choices. -/
def AffineCoset (U : Submodule Q A) := {C : Finset A // ∃ x, C = cosetPoints U x}

namespace AffineCoset
variable (U : Submodule Q A)

def of (x : A) : AffineCoset U := ⟨cosetPoints U x,x,rfl⟩

instance : Fintype (AffineCoset U) := by
  unfold AffineCoset
  infer_instance

lemma of_surjective : Function.Surjective (of U) := by
  rintro ⟨C,x,rfl⟩
  exact ⟨x,rfl⟩

lemma card_le : Fintype.card (AffineCoset U) ≤ Fintype.card A :=
  Fintype.card_le_of_surjective _ (of_surjective U)

lemma card (C : AffineCoset U) : C.val.card = Fintype.card U := by
  obtain ⟨x,hx⟩ := C.property
  rw [hx,card_cosetPoints]

lemma nonempty (C : AffineCoset U) : C.val.Nonempty := by
  obtain ⟨x,hx⟩ := C.property
  exact ⟨x,hx ▸ self_mem_cosetPoints U x⟩

lemma eq_of_mem {C : AffineCoset U} {x : A} (hx : x ∈ C.val) : of U x = C := by
  obtain ⟨y,hy⟩ := C.property
  apply Subtype.ext
  change cosetPoints U x = C.val
  rw [hy] at hx ⊢
  exact cosetPoints_eq ((mem_cosetPoints U y x).mp hx)

lemma mem_iff (C : AffineCoset U) (x : A) : x ∈ C.val ↔ of U x = C := by
  refine ⟨eq_of_mem U, ?_⟩
  intro hx
  rw [← hx]
  exact self_mem_cosetPoints U x

lemma of_eq_iff (x y : A) : of U x = of U y ↔ x - y ∈ U := by
  rw [← mem_iff]
  exact mem_cosetPoints U y x

lemma add_mem_iff (C : AffineCoset U) (x v : A) (hv : v ∈ U) :
    x + v ∈ C.val ↔ x ∈ C.val := by
  obtain ⟨y,hy⟩ := C.property
  rw [hy]
  simp only [mem_cosetPoints]
  have he : x + v - y = (x - y) + v := by abel
  rw [he]
  exact (Submodule.add_mem_iff_left U hv)

end AffineCoset

variable [Fintype Q]

/-- A direction vector parametrizes every point of its full line. -/
def linePoints (x v : A) : Finset A := Finset.univ.image (fun t : Q => x + t • v)

omit [Fintype Q] [Fintype A] in
lemma lineParam_injective {x v : A} (hv : v ≠ 0) :
    Function.Injective (fun t : Q => x + t • v) := by
  intro t s ht
  exact (smul_left_injective Q hv) (add_left_cancel ht)

omit [Fintype A] in
lemma card_linePoints (x : A) {v : A} (hv : v ≠ 0) :
    (linePoints (Q := Q) x v).card = Fintype.card Q := by
  rw [linePoints, Finset.card_image_of_injective _ (lineParam_injective hv), Finset.card_univ]

omit [Fintype A] in
lemma base_mem_linePoints (x v : A) : x ∈ linePoints (Q := Q) x v := by
  simp only [linePoints, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨0, by simp⟩

lemma linePoints_eq_coset (x v : A) :
    linePoints (Q := Q) x v = cosetPoints (Submodule.span Q {v}) x := by
  ext y
  simp only [linePoints, Finset.mem_image, Finset.mem_univ, true_and, mem_cosetPoints,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [ht]; abel⟩

/-- Affine lines are identified by their actual point sets. -/
def FullLine (s : Finset A) : Prop := ∃ x v : A, v ≠ 0 ∧ s = linePoints (Q := Q) x v

omit [Fintype A] in
lemma FullLine.card {s : Finset A} (hs : FullLine (Q := Q) s) : s.card = Fintype.card Q := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  exact card_linePoints x hv

omit [Fintype A] in
lemma FullLine.nonempty {s : Finset A} (hs : FullLine (Q := Q) s) : s.Nonempty := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  exact ⟨x, base_mem_linePoints x v⟩

end KaplanskyCounterexample.FiniteGeometry
end

end OAI

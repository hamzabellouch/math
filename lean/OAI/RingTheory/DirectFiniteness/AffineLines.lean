import OAI.RingTheory.DirectFiniteness.SlabLoad

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype Q] [Fintype A]

omit [Fintype A] in
@[simp] lemma mem_linePoints (x v y : A) :
    y ∈ linePoints (Q := Q) x v ↔ ∃ t : Q, x + t • v = y := by
  simp [linePoints]

lemma linePoints_rebase {x v y : A} (hy : y ∈ linePoints (Q := Q) x v) :
    linePoints (Q := Q) y v = linePoints (Q := Q) x v := by
  rw [linePoints_eq_coset] at hy ⊢
  rw [linePoints_eq_coset]
  exact cosetPoints_eq ((mem_cosetPoints _ _ _).mp hy)

lemma linePoints_scale (x v : A) {t : Q} (ht : t ≠ 0) :
    linePoints (Q := Q) x (t • v) = linePoints (Q := Q) x v := by
  ext y
  simp only [mem_linePoints]
  constructor
  · rintro ⟨s,rfl⟩; exact ⟨s*t,by simp [smul_smul]⟩
  · rintro ⟨s,rfl⟩; exact ⟨s/t,by simp [smul_smul,ht]⟩

lemma FullLine.eq_linePoints_sub {l : Finset A} (hl : FullLine (Q := Q) l)
    {x y : A} (hx : x ∈ l) (hy : y ∈ l) (hne : y ≠ x) :
    l = linePoints (Q := Q) x (y-x) := by
  obtain ⟨a,v,hv,he⟩ := hl
  have he' : l = linePoints (Q := Q) x v := by
    rw [he]
    exact (linePoints_rebase (he ▸ hx)).symm
  rw [he'] at hy
  obtain ⟨t,ht⟩ := mem_linePoints _ _ _ |>.mp hy
  have ht0 : t ≠ 0 := by intro h; exact hne (by simpa [h] using ht.symm)
  have hdiff : y-x=t • v := by rw [← ht]; abel
  rw [he',hdiff,linePoints_scale _ _ ht0]

lemma FullLine.eq_of_two_mem {l m : Finset A} (hl : FullLine (Q := Q) l)
    (hm : FullLine (Q := Q) m) {x y : A} (hx : x ∈ l) (hy : y ∈ l)
    (hx' : x ∈ m) (hy' : y ∈ m) (hne : y ≠ x) : l=m := by
  rw [hl.eq_linePoints_sub hx hy hne,hm.eq_linePoints_sub hx' hy' hne]

omit [Fintype A] in
lemma direction_sub_mem {U : Submodule Q A} {a v x y : A} (hv : v ∈ U)
    (hx : x ∈ linePoints (Q := Q) a v) (hy : y ∈ linePoints (Q := Q) a v) :
    y-x ∈ U := by
  obtain ⟨s,rfl⟩ := (mem_linePoints _ _ _).mp hx
  obtain ⟨t,rfl⟩ := (mem_linePoints _ _ _).mp hy
  convert U.smul_mem (t-s) hv using 1
  simp only [sub_smul]
  abel

/-- A partition by full lines, represented without arbitrary labels or duplicates. -/
structure LinePartition where
  through : A → Finset A
  self : ∀ x, x ∈ through x
  full : ∀ x, FullLine (Q := Q) (through x)
  stable : ∀ x y, y ∈ through x → through y = through x

namespace LinePartition
variable (L : LinePartition (Q := Q) (A := A))
omit [Fintype A] in
lemma mem_iff (x y : A) : y ∈ L.through x ↔ L.through y = L.through x := by
  exact ⟨L.stable x y, fun h => h ▸ L.self y⟩
omit [Fintype A] in
lemma disjoint_or_eq (x y : A) : Disjoint (L.through x) (L.through y) ∨ L.through x=L.through y := by
  by_cases h : Disjoint (L.through x) (L.through y)
  · exact Or.inl h
  · obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr ((L.stable x z hz).symm.trans (L.stable y z hz'))
end LinePartition
end KaplanskyCounterexample.FiniteGeometry
end

end OAI

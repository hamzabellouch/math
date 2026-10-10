import OAI.RingTheory.DirectFiniteness.SlabPartition

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P] [Fintype Q] [Fintype P]

def slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Finset (P × Q) :=
  Finset.univ.filter (fun p => p ∈ slabLine J γ)

@[simp] lemma mem_slabLinePoints (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (p : P × Q) :
    p ∈ slabLinePoints J γ ↔ p ∈ slabLine J γ := by simp [slabLinePoints]

lemma slabLinePoints_full [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (hγ : γ ≠ 0) : FullLine (Q := Q) (slabLinePoints J γ) := by
  obtain ⟨u,v,hv,he⟩ := slabLine_is_line hd J γ hγ
  refine ⟨u,v,fun h => hv (congrArg Prod.fst h),?_⟩
  ext z
  rw [mem_slabLinePoints,he,Set.mem_range,mem_linePoints]

def modelAxis : Finset (P × Q) := linePoints (Q := Q) 0 (0,1)

omit [Fintype P] in
@[simp] lemma mem_modelAxis (p : P × Q) : p ∈ modelAxis (Q := Q) (P := P) ↔ p.1=0 := by
  change p ∈ linePoints (Q := Q) 0 (0,1) ↔ p.1=0
  constructor
  · intro membership
    obtain ⟨scalar,rfl⟩ := (mem_linePoints _ _ _).mp membership
    exact (zero_add (scalar • (0 : P))).trans (smul_zero scalar)
  · intro first_zero
    apply (mem_linePoints _ _ _).mpr
    refine ⟨p.2,Prod.ext ?_ ?_⟩
    · exact ((zero_add _).trans (smul_zero p.2)).trans first_zero.symm
    · exact (zero_add _).trans (mul_one p.2)

omit [Fintype P] in
lemma modelAxis_full : FullLine (Q := Q) (modelAxis (Q := Q) (P := P)) :=
  ⟨0,(0,1),fun h => one_ne_zero (congrArg Prod.snd h),rfl⟩

variable [FiniteDimensional Q P] (hd : finrank Q P = 2) (J : P →ₗ[Q] P) (hJ : NoEigenvector J)

def modelFunctional (x : P × Q) (hx : x.1 ≠ 0) : P →ₗ[Q] Q :=
  (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose

omit [Fintype Q] [Fintype P] in
lemma modelFunctional_spec (x : P × Q) (hx : x.1 ≠ 0) :
    x ∈ slabLine J (modelFunctional hd J hJ x hx) := by
  have h := (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose_spec.1
  exact ⟨h.1,h.2.symm⟩

omit [Fintype Q] [Fintype P] in
lemma modelFunctional_unique (x : P × Q) (hx : x.1 ≠ 0) (γ : P →ₗ[Q] Q)
    (hγ : x ∈ slabLine J γ) : γ=modelFunctional hd J hJ x hx :=
  (existsUnique_slab_functional hd J hJ x.1 hx x.2).choose_spec.2 γ ⟨hγ.1,hγ.2.symm⟩

def modelThrough (x : P × Q) : Finset (P × Q) :=
  if hx : x.1=0 then modelAxis else slabLinePoints J (modelFunctional hd J hJ x hx)

lemma modelThrough_self (x : P × Q) : x ∈ modelThrough hd J hJ x := by
  unfold modelThrough
  split_ifs with hx
  · exact (mem_modelAxis x).mpr hx
  · exact (mem_slabLinePoints _ _ _).mpr (modelFunctional_spec hd J hJ x hx)

lemma modelThrough_full (x : P × Q) : FullLine (Q := Q) (modelThrough hd J hJ x) := by
  unfold modelThrough
  split_ifs with hx
  · exact modelAxis_full
  · exact slabLinePoints_full hd J _ (slabLine_functional_ne_zero J _ (modelFunctional_spec hd J hJ x hx))

lemma modelThrough_stable (x y : P × Q) (hy : y ∈ modelThrough hd J hJ x) :
    modelThrough hd J hJ y=modelThrough hd J hJ x := by
  by_cases hx : x.1=0
  · rw [modelThrough,dite_eq_left hx] at hy
    conv_rhs => rw [modelThrough,dite_eq_left hx]
    rw [modelThrough,dite_eq_left ((mem_modelAxis y).mp hy)]
  · rw [modelThrough,dite_eq_right hx] at hy
    conv_rhs => rw [modelThrough,dite_eq_right hx]
    have hy' := (mem_slabLinePoints _ _ _).mp hy
    have hy0 := slabLine_off_axis J _ hy'
    rw [modelThrough,dite_eq_right hy0]
    rw [← modelFunctional_unique hd J hJ y hy0 _ hy']

def axisPartition : LinePartition (Q := Q) (A := P × Q) :=
  ⟨modelThrough hd J hJ,modelThrough_self hd J hJ,modelThrough_full hd J hJ,modelThrough_stable hd J hJ⟩

lemma axisPartition_through_zero : (axisPartition hd J hJ).through 0 = modelAxis := by
  simp [axisPartition,modelThrough]

lemma axisPartition_projection {x y z : P × Q} (hx : x.1 ≠ 0)
    (hy : y ∈ (axisPartition hd J hJ).through x) (hz : z ∈ (axisPartition hd J hJ).through x)
    (hne : z ≠ y) : z.1-y.1 ≠ 0 := by
  change y ∈ modelThrough hd J hJ x at hy
  change z ∈ modelThrough hd J hJ x at hz
  rw [modelThrough,dite_eq_right hx,mem_slabLinePoints] at hy hz
  intro h
  have he : z.1=y.1 := sub_eq_zero.mp h
  apply hne
  exact Prod.ext he (by rw [hz.2,hy.2,he])

lemma axisPartition_zero_mem_iff (x : P × Q) :
    (0 : P × Q) ∈ (axisPartition hd J hJ).through x ↔ x.1=0 := by
  change 0 ∈ modelThrough hd J hJ x ↔ _
  by_cases hx : x.1=0
  · simp [modelThrough,hx]
  · rw [modelThrough,dite_eq_right hx,mem_slabLinePoints]
    constructor
    · intro h
      exact False.elim (slabLine_off_axis J _ h rfl)
    · exact False.elim ∘ hx

omit [FiniteDimensional Q P] in
def parallelPlanePartition (v : P) (hv : v ≠ 0) : LinePartition (Q := Q) (A := P × Q) where
  through x := linePoints (Q := Q) x (v,0)
  self x := base_mem_linePoints x _
  full x := ⟨x,(v,0),fun h => hv (congrArg Prod.fst h),rfl⟩
  stable _ _ h := linePoints_rebase h

omit [FiniteDimensional Q P] in
lemma parallelPlanePartition_projection (v : P) (hv : v ≠ 0) {x y z : P × Q}
    (hy : y ∈ (parallelPlanePartition v hv).through x)
    (hz : z ∈ (parallelPlanePartition v hv).through x) (hne : z ≠ y) : z.1-y.1 ≠ 0 := by
  obtain ⟨t,rfl⟩ := (mem_linePoints _ _ _).mp hy
  obtain ⟨s,rfl⟩ := (mem_linePoints _ _ _).mp hz
  intro he
  have he' : s • v=t • v := add_left_cancel (sub_eq_zero.mp he)
  have hst := (smul_left_injective Q hv) he'
  exact hne (by rw [hst])

end KaplanskyCounterexample.FiniteGeometry
end

end OAI

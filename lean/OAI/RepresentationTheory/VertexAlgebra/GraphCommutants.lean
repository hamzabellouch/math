import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.HilbertCore

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData

theorem entry_commutes_of_graph_invariant
    (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (Q : H →L[ℂ] H)
    (hQ : ∀ x y : H, (x,y) ∈ T.graph → (Q x,Q y) ∈ T.graph)
    (hQa : ∀ x y : H, (x,y) ∈ T.graph → (Q.adjoint x,Q.adjoint y) ∈ T.graph)
    (i j : Bool) : Q * entry T hT i j = entry T hT i j * Q := by
  have hinv : ∀ z ∈ graph T, diagonalAction Q z ∈ graph T := by
    intro z hz
    exact hQ _ _ hz
  have hinva : ∀ z ∈ graph T, (diagonalAction Q).adjoint z ∈ graph T := by
    rw [diagonalAction_adj]
    intro z hz
    exact hQa _ _ hz
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  have hP : (diagonalAction Q).comp (projection T hT) =
      (projection T hT).comp (diagonalAction Q) :=
    commutes_projection_of_reduces (graph T) (diagonalAction Q) hinv hinva
  change Q.comp (entry T hT i j) = (entry T hT i j).comp Q
  have hc : Q.comp (coordinate i) = (coordinate i).comp (diagonalAction Q) :=
    (coordinate_diagonalAction Q i).symm
  calc
    Q.comp (entry T hT i j) =
        ((coordinate i).comp (diagonalAction Q)).comp ((projection T hT).comp (inclusion j)) := by
      rw [← hc]; rfl
    _ = (coordinate i).comp (((projection T hT).comp (diagonalAction Q)).comp (inclusion j)) := by
      simpa only [ContinuousLinearMap.comp_assoc] using
        congrArg (fun R => (coordinate i).comp (R.comp (inclusion j))) hP
    _ = (entry T hT i j).comp Q := by
      simp only [ContinuousLinearMap.comp_assoc, diagonalAction_inclusion, entry]

end ClosedGraphData

namespace LocalOperatorAlgebra
open scoped Pointwise
 

def generated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
        (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]

theorem subset_generated (s : Set (H →L[ℂ] H)) : s ⊆ generated s := by
  intro x hx
  exact StarAlgebra.adjoin_le_centralizer_centralizer ℂ s
    (StarAlgebra.subset_adjoin ℂ s hx)

theorem generated_mono {s t : Set (H →L[ℂ] H)} (hst : s ⊆ t) :
    generated s ≤ generated t :=
  StarSubalgebra.centralizer_le _ _ _ (StarSubalgebra.centralizer_le _ _ _ hst)

theorem generated_le {s : Set (H →L[ℂ] H)} {M : VonNeumannAlgebra H}
    (h : s ⊆ M) : generated s ≤ M := by
  have hle := StarSubalgebra.centralizer_le ℂ _ _ (StarSubalgebra.centralizer_le ℂ _ _ h)
  change (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ _
  change (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆
    (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (M : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) at hle
  simpa only [StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq, Set.union_self, M.centralizer_centralizer] using hle

@[simp]
theorem coe_generated_commutant (s : Set (H →L[ℂ] H)) :
    ((generated s).commutant : Set (H →L[ℂ] H)) = (s ∪ star s).centralizer := by
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = _
  rw [StarSubalgebra.coe_centralizer_centralizer,
    Set.centralizer_centralizer_centralizer]

 

theorem generated_le_commutant_iff (s t : Set (H →L[ℂ] H)) :
    generated s ≤ (generated t).commutant ↔
      ∀ x ∈ s, ∀ y ∈ t, y*x = x*y ∧ star y*x = x*star y := by
  constructor
  · intro h x hx y hy
    have hmem := h (subset_generated s hx)
    rw [← SetLike.mem_coe, coe_generated_commutant] at hmem
    exact ⟨hmem y (Set.mem_union_left _ hy),
      hmem (star y) (Set.mem_union_right _ (by simpa using hy))⟩
  · intro h
    apply generated_le
    intro x hx
    rw [coe_generated_commutant]
    rintro y (hy | hy)
    · exact (h x hx y hy).1
    · have hy' : star y ∈ t := hy
      simpa using (h x hx (star y) hy').2

end LocalOperatorAlgebra

end GraphData

namespace SmoothCircleFunction

 
def onCircle (f : SmoothCircleFunction) : AddCircle (2*Real.pi) → ℂ :=
  f.periodic.lift

@[simp]
theorem onCircle_coe (f : SmoothCircleFunction) (t : ℝ) :
    f.onCircle (t : AddCircle (2*Real.pi)) = f.toFun t := rfl

end SmoothCircleFunction

 

structure ProperCircleArc where
  left : ℝ
  right : ℝ
  nonempty' : left < right
  nondense' : right < left + 2*Real.pi

namespace ProperCircleArc

def carrier (I : ProperCircleArc) : Set (AddCircle (2*Real.pi)) :=
  (fun t : ℝ => (t : AddCircle (2*Real.pi))) '' Set.Ioo I.left I.right

 
def complement (I : ProperCircleArc) : ProperCircleArc where
  left := I.right
  right := I.left + 2*Real.pi
  nonempty' := I.nondense'
  nondense' := by linarith [I.nonempty']

end ProperCircleArc

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def localGraphData (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ (a : V) (d : ℕ) (ha : a ∈ A.grade d) (f : SmoothCircleFunction),
      tsupport f.onCircle ⊆ O ∧ ∃ i j : Bool,
        x = ClosedGraphData.entry (U.closedSmoothField hc a d f)
          (U.closedSmoothField_isClosed hc ha f) i j}

 

def localAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  LocalOperatorAlgebra.generated (U.localGraphData hc O)

def intervalAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (I : ProperCircleArc) : VonNeumannAlgebra (Completion V) :=
  U.localAlgebra hc I.carrier

 

def CKLWStrongLocal (hc : A.toVertexAlgebra.C2Cofinite) : Prop :=
  (∀ a : V, A.PolynomialEnergyBound a) ∧
    ∀ I : ProperCircleArc, U.intervalAlgebra hc I ≤
      (U.intervalAlgebra hc I.complement).commutant

theorem localAlgebra_isotone (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (hOP : O ⊆ P) :
    U.localAlgebra hc O ≤ U.localAlgebra hc P := by
  apply LocalOperatorAlgebra.generated_mono
  rintro x ⟨a,d,ha,f,hf,i,j,rfl⟩
  exact ⟨a,d,ha,f,hf.trans hOP,i,j,rfl⟩

 

theorem closedSmoothField_graphData_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hf : tsupport f.onCircle ⊆ O) (i j : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.localAlgebra hc O :=
  LocalOperatorAlgebra.subset_generated _ ⟨a,d,ha,f,hf,i,j,rfl⟩

 

theorem CKLWStrongLocal_iff_graphData (hc : A.toVertexAlgebra.C2Cofinite) :
    U.CKLWStrongLocal hc ↔
    ∀ I : ProperCircleArc, ∀ x ∈ U.localGraphData hc I.carrier,
      ∀ y ∈ U.localGraphData hc I.complement.carrier, y*x=x*y := by
  constructor
  · intro h I x hx y hy
    exact ((LocalOperatorAlgebra.generated_le_commutant_iff _ _).mp (h.2 I) x hx y hy).1
  · intro h
    refine ⟨U.polynomialEnergyBounds hc, fun I => ?_⟩
    apply (LocalOperatorAlgebra.generated_le_commutant_iff _ _).mpr
    intro x hx y hy
    refine ⟨h I x hx y hy, ?_⟩
    apply h I x hx (star y)
    obtain ⟨a,d,ha,f,hf,i,j,rfl⟩ := hy
    exact ⟨a,d,ha,f,hf,j,i,ClosedGraphData.star_entry _ _ i j⟩

end CFTTypeVOA.UnitaryStructure

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 
def gradeEmbedding (d : ℕ) : A.grade d →ₗᵢ[ℂ] Completion V :=
  (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).comp (A.grade d).subtypeₗᵢ

include U in
theorem completed_grades_orthogonal :
    OrthogonalFamily ℂ (fun d => A.grade d) (fun d => gradeEmbedding (A := A) d) := by
  intro d e hde a b
  change inner ℂ ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) a.val)
    ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) b.val) = 0
  rw [LinearIsometry.inner_map_map]
  exact U.grades_orthogonal hde a.property b.property

include U in
 

theorem completed_isHilbertSum :
    IsHilbertSum ℂ (fun d => A.grade d) (fun d => gradeEmbedding (A := A) d) := by
  classical
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  apply IsHilbertSum.mk U.completed_grades_orthogonal
  let S := ⨆ d, LinearMap.range (gradeEmbedding (A := A) d).toLinearMap
  have hcore : HilbertCore.space V ≤ S := by
    rintro _ ⟨a, rfl⟩
    rw [← A.sum_gradeComponents a, map_sum]
    apply Submodule.sum_mem
    intro d _
    apply Submodule.mem_iSup_of_mem d
    exact ⟨⟨A.gradeComponent d a, A.gradeComponent_mem d a⟩, rfl⟩
  have hd : Dense (S : Set (Completion V)) := HilbertCore.dense.mono hcore
  exact le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp hd).symm

 
def energyCoordinates : Completion V ≃ₗᵢ[ℂ] lp (fun d => A.grade d) 2 :=
  U.completed_isHilbertSum.linearIsometryEquiv

@[simp]
theorem energyCoordinates_grade {d : ℕ} (a : A.grade d) :
    U.energyCoordinates (a.val : Completion V) = lp.single 2 d a := by
  apply U.energyCoordinates.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (U.completed_isHilbertSum.linearIsometryEquiv_symm_apply_single a).symm

 

theorem energyCoordinates_coe (a : V) (d : ℕ) :
    (U.energyCoordinates (a : Completion V) d).val = A.gradeComponent d a := by
  apply A.homogeneous_induction (P := fun a =>
    (U.energyCoordinates (a : Completion V) d).val = A.gradeComponent d a)
  · change (U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) 0) d).val = _
    rw [map_zero, map_zero]
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, Submodule.coe_zero]
  · intro e b hb
    rw [energyCoordinates_grade U ⟨b,hb⟩]
    by_cases hed : e = d
    · subst e
      simp [A.gradeComponent_of_mem hb]
    · simp [lp.single_apply, Ne.symm hed, A.gradeComponent_of_mem_ne hed hb]
  · intro b c hb hc
    change (U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (b+c)) d).val = _
    simp only [map_add, lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    change (U.energyCoordinates (b : Completion V) d).val +
      (U.energyCoordinates (c : Completion V) d).val = _
    rw [hb,hc]

end CFTTypeVOA.UnitaryStructure

open scoped ENNReal
namespace HilbertScale
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

abbrev Space (G : ι → Type u) [∀ i, NormedAddCommGroup (G i)] := lp G 2

 
def domain (w : ι → ℂ) : Submodule ℂ (Space G) where
  carrier := {x | Memℓp (fun i => w i • x i) 2}
  zero_mem' := by
    change Memℓp (fun i => w i • (0 : G i)) 2
    simpa only [smul_zero] using (zero_mem_ℓp' (E := G) (p := 2))
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun i => w i • (x i + y i)) 2
    convert hx.add hy using 1
    ext i
    exact smul_add _ _ _
  smul_mem' := by
    intro c x hx
    change Memℓp (fun i => w i • (c • x i)) 2
    convert hx.const_smul c using 1
    ext i
    exact smul_comm _ _ _

 
def diagonal (w : ι → ℂ) : Space G →ₗ.[ℂ] Space G where
  domain := domain w
  toFun :=
    { toFun := fun x => ⟨fun i => w i • x.val i, x.property⟩
      map_add' := by
        intro x y; ext i
        change w i • (x.val i + y.val i) = w i • x.val i + w i • y.val i
        exact smul_add _ _ _
      map_smul' := by intro c x; ext i; simp [smul_smul, mul_comm] }

@[simp]
theorem diagonal_apply (w : ι → ℂ) (x : (diagonal (G := G) w).domain) (i : ι) :
    diagonal w x i = w i • x.val i := rfl

theorem mem_graph_iff (w : ι → ℂ) (x y : Space G) :
    (x,y) ∈ (diagonal w).graph ↔ ∀ i, y i = w i • x i := by
  constructor
  · intro hz i
    obtain ⟨z,hz,hzw⟩ := (diagonal w).mem_graph_iff.mp hz
    have h1 : (z : Space G) = x := hz
    have h2 : diagonal w z = y := hzw
    have hi := congrArg (fun v : Space G => v i) h2
    change w i • (z : Space G) i = y i at hi
    rw [h1] at hi
    exact hi.symm
  · intro h
    have hd : x ∈ domain w := by
      change Memℓp (fun i => w i • x i) 2
      convert lp.memℓp y using 1
      ext i; exact (h i).symm
    exact (diagonal w).mem_graph_iff.mpr ⟨⟨x,hd⟩,rfl,by ext i; exact (h i).symm⟩

theorem diagonal_closed (w : ι → ℂ) : (diagonal (G := G) w).IsClosed := by
  have heq : ((diagonal (G := G) w).graph : Set (Space G × Space G)) =
      ⋂ i, {z : Space G × Space G | z.2 i = w i • z.1 i} := by
    ext z; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_graph_iff w z.1 z.2
  rw [LinearPMap.IsClosed, heq]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((lp.evalCLM ℂ G 2 i).continuous.comp continuous_snd)
    (((lp.evalCLM ℂ G 2 i).continuous.comp continuous_fst).const_smul (w i))

variable [DecidableEq ι]

theorem single_mem_domain (w : ι → ℂ) (i : ι) (v : G i) :
    lp.single 2 i v ∈ domain w := by
  change Memℓp _ 2
  have heq : (fun j => w j • lp.single 2 i v j) = (lp.single 2 i (w i • v) : ∀ j, G j) := by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [lp.single_apply, h]
  rw [heq]
  exact lp.memℓp _

theorem diagonal_single (w : ι → ℂ) (i : ι) (v : G i) :
    diagonal w ⟨lp.single 2 i v, single_mem_domain w i v⟩ = lp.single 2 i (w i • v) := by
  ext j; by_cases h : j = i
  · subst h; simp
  · simp [lp.single_apply, h]

theorem domain_dense (w : ι → ℂ) : Dense (domain (G := G) w : Set (Space G)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  apply Filter.Eventually.of_forall
  intro s
  exact Submodule.sum_mem _ (fun i _ => single_mem_domain w i (x i))

variable [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι] [∀ i, CompleteSpace (G i)] in
 

theorem diagonal_formalAdjoint (w : ι → ℂ) :
    (diagonal (G := G) w).IsFormalAdjoint (diagonal (fun i => star (w i))) := by
  intro x y
  rw [← (lp.hasSum_inner (diagonal w x) (y : Space G)).tsum_eq,
    ← (lp.hasSum_inner (x : Space G) (diagonal (fun i => star (w i)) y)).tsum_eq]
  apply tsum_congr
  intro i
  simp only [diagonal_apply, inner_smul_left, inner_smul_right, starRingEnd_apply]

theorem adjoint_coordinate (w : ι → ℂ) (y : (diagonal (G := G) w).adjoint.domain)
    (i : ι) : (diagonal (G := G) w).adjoint y i = star (w i) • (y : Space G) i := by
  apply ext_inner_right ℂ
  intro v
  have h : inner ℂ ((diagonal (G := G) w).adjoint y) (lp.single 2 i v) =
      inner ℂ (y : Space G) (lp.single 2 i (w i • v)) := by
    have hh := (LinearPMap.adjoint_isFormalAdjoint (domain_dense (G := G) w)) y
      ⟨lp.single 2 i v, single_mem_domain (G := G) w i v⟩
    rw [diagonal_single] at hh
    exact hh
  rw [lp.inner_single_right, lp.inner_single_right] at h
  simpa only [inner_smul_right, inner_smul_left, star_star, starRingEnd_apply] using h

 

theorem adjoint_le_diagonal (w : ι → ℂ) :
    (diagonal (G := G) w).adjoint ≤ diagonal (G := G) (fun i => star (w i)) := by
  apply LinearPMap.le_graph_iff.mp
  intro z hz
  obtain ⟨y,hy,hTy⟩ := ((diagonal (G := G) w).adjoint).mem_graph_iff.mp hz
  apply (mem_graph_iff (G := G) _ _ _).mpr
  intro i
  have h1 : (y : Space G) = z.1 := hy
  have h2 : (diagonal (G := G) w).adjoint y = z.2 := hTy
  have hi := adjoint_coordinate w y i
  rw [h1, h2] at hi
  exact hi

theorem adjoint_diagonal (w : ι → ℂ) :
    (diagonal (G := G) w).adjoint = diagonal (fun i => star (w i)) := by
  apply le_antisymm (adjoint_le_diagonal w)
  have hf : (diagonal (G := G) w).IsFormalAdjoint (diagonal (fun i => star (w i))) :=
    diagonal_formalAdjoint w
  exact hf.le_adjoint (domain_dense w)

 
def finiteCore : Submodule ℂ (Space G) :=
  Submodule.span ℂ {x | ∃ i v, x = lp.single 2 i v}

omit [∀ i, CompleteSpace (G i)] in
theorem single_mem_finiteCore (i : ι) (v : G i) :
    lp.single 2 i v ∈ finiteCore (G := G) :=
  Submodule.subset_span ⟨i,v,rfl⟩

omit [∀ i, CompleteSpace (G i)] in
theorem finiteCore_le_domain (w : ι → ℂ) : finiteCore (G := G) ≤ domain w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,v,rfl⟩
  exact single_mem_domain w i v

omit [∀ i, CompleteSpace (G i)] in
 

theorem diagonal_hasCore (w : ι → ℂ) :
    (diagonal (G := G) w).HasCore finiteCore := by
  let T := (diagonal (G := G) w).domRestrict finiteCore
  have hT : T.IsClosable := (diagonal_closed w).isClosable.leIsClosable
    LinearPMap.domRestrict_le
  refine ⟨finiteCore_le_domain w, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hT.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) (diagonal_closed w)
  · intro z hz
    have hzy := (mem_graph_iff w z.1 z.2).mp hz
    have hs := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z.1).prodMk
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z.2)
    apply mem_closure_of_tendsto hs
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    apply T.mem_graph_iff.mpr
    have hdom : lp.single 2 i (z.1 i) ∈ T.domain :=
      ⟨single_mem_finiteCore _ _, single_mem_domain _ _ _⟩
    refine ⟨⟨_,hdom⟩,rfl,?_⟩
    change diagonal w ⟨lp.single 2 i (z.1 i),single_mem_domain _ _ _⟩ = _
    rw [diagonal_single, ← hzy i]

 

theorem real_diagonal_selfAdjoint (w : ι → ℝ) :
    (diagonal (G := G) (fun i => (w i : ℂ))).adjoint = diagonal (fun i => (w i : ℂ)) := by
  rw [adjoint_diagonal]
  simp only [Complex.star_def, Complex.conj_ofReal]

end HilbertScale

namespace OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

 

def transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) : H →ₗ.[ℂ] H where
  domain := T.domain.comap E.toLinearEquiv.toLinearMap
  toFun :=
    { toFun := fun x => E.symm (T ⟨E x.val, x.property⟩)
      map_add' := by
        intro x y
        simp only [Submodule.coe_add,map_add]
        change E.symm (T (⟨E x.val,x.property⟩ + ⟨E y.val,y.property⟩)) = _
        rw [T.map_add,map_add]
      map_smul' := by
        intro c x
        simp only [Submodule.coe_smul,map_smul]
        change E.symm (T (c • (⟨E x.val,x.property⟩ : T.domain))) = _
        rw [T.map_smul,map_smul]
        rfl }

theorem mem_graph_iff (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (x y : H) :
    (x,y) ∈ (transport E T).graph ↔ (E x, E y) ∈ T.graph := by
  rw [(transport E T).mem_graph_iff, T.mem_graph_iff]
  constructor
  · rintro ⟨z,hz,hzy⟩
    dsimp only [Prod.fst,Prod.snd] at hz hzy ⊢
    have hmem : E z.val ∈ T.domain := z.property
    refine ⟨⟨E z.val,hmem⟩,congrArg E hz,?_⟩
    rw [← hzy]
    exact (E.apply_symm_apply _).symm
  · rintro ⟨z,hz,hzy⟩
    dsimp only [Prod.fst,Prod.snd] at hz hzy ⊢
    have hx : x ∈ (transport E T).domain := by
      change E x ∈ T.domain
      rw [← hz]; exact z.property
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    change E.symm (T ⟨E x,hx⟩) = y
    have hz' : (⟨E x,hx⟩ : T.domain) = z := Subtype.ext hz.symm
    rw [hz',hzy,E.symm_apply_apply]
end OperatorTransport
end StronglyRationalVOA

end

end OAI

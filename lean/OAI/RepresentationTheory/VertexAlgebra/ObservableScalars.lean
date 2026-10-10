import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.LocalNormalMap

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma LocalState.smul (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hL : U.LocalState hc a d) (c : ℂ) :
    U.LocalState hc (c • a) d := by
  apply LocalState.span U hc d (S := {a})
  · intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact ⟨ha,hL⟩
  · exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton a))
lemma LocalState.add (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade d)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b d) :
    U.LocalState hc (a+b) d := by
  apply LocalState.span U hc d (S := {a,b})
  · intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact ⟨ha,hLa⟩
    · rcases Set.mem_singleton_iff.mp hc with rfl
      exact ⟨hb,hLb⟩
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
lemma localState_zero (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) : U.LocalState hc (0:V) d := by
  apply LocalState.span U hc d (S := ∅) (by simp)
  exact Submodule.zero_mem _
def localStateSpace (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) : Submodule ℂ V where
  carrier := {a | a ∈ A.grade d ∧ U.LocalState hc a d}
  zero_mem' := ⟨(A.grade d).zero_mem,U.localState_zero hc d⟩
  add_mem' := fun ha hb => ⟨(A.grade d).add_mem ha.1 hb.1,LocalState.add U hc ha.1 hb.1 ha.2 hb.2⟩
  smul_mem' := fun c _ ha => ⟨(A.grade d).smul_mem c ha.1,LocalState.smul U hc ha.1 ha.2 c⟩
lemma translation_mem_grade {a : V} {d : ℕ} (ha : a ∈ A.grade d) :
    A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
  rw [← A.virasoro_neg_one_eq_translation]
  exact A.virasoro_mem_grade ha (-1) (by omega)
lemma LocalState.negative_mode (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b e) :
    U.LocalState hc (mode A.fields a (-1-(n:ℤ)) b) (d+e+n) := by
  induction n generalizing a d with
  | zero => simpa only [Nat.cast_zero,sub_zero,add_zero] using LocalState.normal_product U hc ha hb hLa hLb
  | succ n ih =>
    have ht := LocalState.translation U hc hLa
    have htg := translation_mem_grade ha
    have H := ih htg ht
    have hm : mode A.fields (A.toVertexAlgebra.translation a) (-1-(n:ℤ)) b =
        ((n+1:ℕ):ℂ) • mode A.fields a (-1-((n+1:ℕ):ℤ)) b := by
      rw [A.translation_covariance,LinearMap.smul_apply]
      congr 1
      · push_cast
        ring
      · congr 2
        omega
    have hg : mode A.fields (A.toVertexAlgebra.translation a) (-1-(n:ℤ)) b ∈ A.grade (d+1+e+n) :=
      A.mode_mem_grade htg hb _ (by omega)
    have HH := LocalState.smul U hc hg H (((n+1:ℕ):ℂ)⁻¹)
    rw [hm,smul_smul,inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero n)),one_smul] at HH
    convert HH using 1
    omega
lemma LocalState.virasoro_negative (hc : A.toVertexAlgebra.C2Cofinite)
    {b : V} {e : ℕ} (hb : b ∈ A.grade e) (hLb : U.LocalState hc b e)
    (n : ℕ) (hn : 0 < n) : U.LocalState hc (A.virasoroMode (-(n:ℤ)) b) (e+n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  cases n with
  | zero =>
    simpa only [Nat.cast_one,A.virasoro_neg_one_eq_translation] using LocalState.translation U hc hLb
  | succ n =>
    have H := LocalState.negative_mode U hc n A.conformal_mem hb (U.stress_localState hc) hLb
    convert! H using 1
    · congr 2
      dsimp [CFTTypeVOA.virasoroMode]
      congr 1
      omega
    · omega
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.ProperCircleArc
lemma isOpen_carrier (I : ProperCircleArc) : IsOpen I.carrier :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma grade_le_localStateSpace (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) :
    A.grade d ≤ U.localStateSpace hc d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d=0
    · subst d
      rw [A.grade_zero]
      exact Submodule.span_le.mpr (by
        intro a ha
        rcases Set.mem_singleton_iff.mp ha with rfl
        exact ⟨by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _,U.vacuum_localState hc⟩)
    · intro a ha
      obtain ⟨q,hq,hpq,y,hy,rfl⟩ := U.primary_decomposition ha
      apply (U.localStateSpace hc d).add_mem (show q ∈ U.localStateSpace hc d from
        ⟨hq,U.primary_localState hc hq hpq (by omega)⟩)
      have hK : A.lowerVirasoroSpace d ≤ U.localStateSpace hc d := by
        apply iSup_le
        intro n z hz
        obtain ⟨b,hb,rfl⟩ := Submodule.mem_map.mp hz
        have hbLocal := (ih (d-(n.val+1)) (by have := n.isLt; omega) hb).2
        have H := LocalState.virasoro_negative U hc hb hbLocal (n.val+1) (by omega)
        have he : d-(n.val+1)+(n.val+1)=d := by have := n.isLt; omega
        rw [he] at H
        refine ⟨A.virasoro_mem_grade hb _ (by have := n.isLt; omega),?_⟩
        simpa only [Nat.cast_add,Nat.cast_one] using H
      exact hK hy
lemma all_state_localState (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) : U.LocalState hc a d :=
  (U.grade_le_localStateSpace hc d ha).2
lemma all_state_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.all_state_localState hc ha O hO f hs Q hQ x y hxy
  · intro x y hxy
    exact U.all_state_localState hc ha O hO f hs Q.adjoint (star_mem hQ) x y hxy
lemma localAlgebra_eq_primaryAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) :
    U.localAlgebra hc O=U.primaryAlgebra hc O := by
  apply le_antisymm _ (U.primaryAlgebra_le_localAlgebra hc O)
  apply LocalOperatorAlgebra.generated_le
  rintro x ⟨a,d,ha,f,hf,i,j,rfl⟩
  exact U.all_state_entry_mem hc ha f hO hf i j
lemma localAlgebra_locality (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hP : IsOpen P) (h : Disjoint O P) :
    U.localAlgebra hc O ≤ (U.localAlgebra hc P).commutant := by
  rw [U.localAlgebra_eq_primaryAlgebra hc hO,U.localAlgebra_eq_primaryAlgebra hc hP]
  exact U.primaryAlgebra_locality hc h
 

theorem cklwStrongLocal (hc : A.toVertexAlgebra.C2Cofinite) : U.CKLWStrongLocal hc := by
  refine ⟨U.polynomialEnergyBounds hc,?_⟩
  intro I
  exact U.localAlgebra_locality hc I.isOpen_carrier I.complement.isOpen_carrier I.disjoint_complement
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hamiltonian_kernel {x : Completion V} (hx : (x,0) ∈ U.conformalHamiltonian.graph) :
    ∃ c : ℂ, x=c • (A.vacuum : Completion V) := by
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ x 0).mp hx
  rw [map_zero,HilbertScale.mem_graph_iff] at h
  let a : A.grade 0 := U.energyCoordinates x 0
  have he : U.energyCoordinates x=lp.single 2 0 a := by
    ext d
    by_cases hd : d=0
    · subst d
      simp [a]
    · have H := h d
      simp only [lp.coeFn_zero,Pi.zero_apply] at H
      have hz : U.energyCoordinates x d=0 := by
        exact (smul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast hd)
      simp [lp.single_apply,hd,hz]
  have ha : (a : V) ∈ Submodule.span ℂ {A.vacuum} := by
    rw [← A.grade_zero]
    exact a.property
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp ha
  refine ⟨c,?_⟩
  apply U.energyCoordinates.injective
  rw [he,← U.energyCoordinates_grade a]
  congr 1
  rw [← hc,Completion.coe_smul]
lemma stress_graph_le_hamiltonian (hc : A.toVertexAlgebra.C2Cofinite) :
    (U.closedSmoothField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).graph ≤
      U.conformalHamiltonian.graph := by
  intro p hp
  have hcore (v : V) : ((v : Completion V),(A.virasoroMode 0 v : Completion V)) ∈
      U.conformalHamiltonian.graph := by
    apply A.homogeneous_induction (P := fun v => ((v : Completion V),(A.virasoroMode 0 v : Completion V)) ∈ U.conformalHamiltonian.graph)
    · simpa only [map_zero,Completion.coe_zero,Prod.zero_eq_mk] using U.conformalHamiltonian.graph.zero_mem
    · intro d a ha
      have H : ((a : Completion V),(d : ℂ) • (a : Completion V)) ∈ (U.energyOperator (fun d => d)).graph := (U.energyOperator (fun d => d)).mem_graph_iff.mpr
        ⟨⟨(a : Completion V),U.coe_mem_energyOperator (fun d => d) a⟩,rfl,
          by simpa only [Complex.ofReal_natCast] using U.energyOperator_grade (fun d => d) ⟨a,ha⟩⟩
      simpa only [conformalHamiltonian,virasoroMode,zero_add,A.conformal_energy d a ha,Completion.coe_smul,Complex.ofReal_natCast] using H
    · intro a b ha hb
      simpa only [map_add,Completion.coe_add,Prod.mk_add_mk] using U.conformalHamiltonian.graph.add_mem ha hb
  change p ∈ ((U.closedSmoothField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).graph : Set (Completion V × Completion V)) at hp
  rw [U.closedSmoothField_graph hc A.conformal_mem] at hp
  apply closure_minimal (fun p hp => ?_) (U.energyOperator_closed (fun d => d)) hp
  obtain ⟨z,hz,hp⟩ := (U.smoothSmearedField hc A.conformalVector 2 (SmoothCircleFunction.constant 1)).mem_graph_iff.mp hp
  obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective z
  change HilbertCore.operator _ (HilbertCore.equiv V v)=p.2 at hp
  rw [HilbertCore.operator_apply,U.constant_stress_core hc] at hp
  have he : p=((v : Completion V),(A.virasoroMode 0 v : Completion V)) := Prod.ext hz.symm hp.symm
  rw [he]
  exact hcore v
lemma local_commutant_preserves_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} {Q : Completion V →L[ℂ] Completion V}
    (hQ : Q ∈ (U.localAlgebra hc O).commutant) {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f : SmoothCircleFunction) (hf : tsupport f.onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes _ (U.closedSmoothField_isClosed hc ha f) Q _ hxy
  intro i j
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hQ _ (U.closedSmoothField_graphData_mem hc ha f hf i j)).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma closedSmoothField_core_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) (v : V) :
    ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v) ∈
      (U.closedSmoothField hc a d f).graph := by
  apply LinearPMap.le_graph_of_le (U.smoothSmearedField hc a d f).le_closure
  exact (U.smoothSmearedField hc a d f).mem_graph_iff.mpr
    ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply _ v⟩
lemma smearedMap_character (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (n : ℤ) (v : V) :
    A.smearedMap a d (U.polynomialEnergyBounds hc a)
      ((SmoothCircleFunction.constant 1).modulate n).coefficient
      ((SmoothCircleFunction.constant 1).modulate n).rapid_coefficients v=
        (A.physicalMode a d n v : Completion V) := by
  rw [A.smearedMap_apply,tsum_eq_single n]
  · simp only [SmoothCircleFunction.modulate_coefficient,sub_self,
      SmoothCircleFunction.coefficient_constant_zero,one_smul]
  · intro j hj
    rw [SmoothCircleFunction.modulate_coefficient,SmoothCircleFunction.coefficient_constant,
      ite_eq_right (sub_ne_zero.mpr hj),zero_smul]
lemma global_commutant_vacuum (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.localAlgebra hc Set.univ).commutant) :
    ∃ c : ℂ, Q (A.vacuum : Completion V)=c • (A.vacuum : Completion V) := by
  apply U.hamiltonian_kernel
  have h := U.closedSmoothField_core_graph hc A.conformalVector 2 (SmoothCircleFunction.constant 1) A.vacuum
  rw [U.constant_stress_core hc,A.virasoro_vacuum 0 (by omega),Completion.coe_zero] at h
  have H := U.local_commutant_preserves_graph hc hQ A.conformal_mem _ (Set.subset_univ _) h
  rw [map_zero] at H
  exact U.stress_graph_le_hamiltonian hc H
 

lemma global_commutant_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.localAlgebra hc Set.univ).commutant) :
    ∃ c : ℂ, Q=c • (1 : Completion V →L[ℂ] Completion V) := by
  obtain ⟨c,hcQ⟩ := U.global_commutant_vacuum hc hQ
  refine ⟨c,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x (isClosed_eq Q.continuous (c • (1 : Completion V →L[ℂ] Completion V)).continuous) ?_
  intro v
  change Q (v : Completion V)=c • (v : Completion V)
  apply A.homogeneous_induction (P := fun v => Q (v : Completion V)=c • (v : Completion V))
  · simp only [Completion.coe_zero,map_zero,smul_zero]
  · intro d a ha
    let f := (SmoothCircleFunction.constant 1).modulate (-(d : ℤ))
    have h : ((A.vacuum : Completion V),(a : Completion V)) ∈ (U.closedSmoothField hc a d f).graph := by
      have H := U.closedSmoothField_core_graph hc a d f A.vacuum
      change ((A.vacuum:Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a) ((SmoothCircleFunction.constant 1).modulate (-(d:ℤ))).coefficient ((SmoothCircleFunction.constant 1).modulate (-(d:ℤ))).rapid_coefficients A.vacuum) ∈ _ at H
      rw [U.smearedMap_character hc] at H
      have he : A.physicalMode a d (-(d:ℤ)) A.vacuum=a := by
        simpa only [physicalMode,neg_add_cancel,zero_sub] using A.creation a
      rwa [he] at H
    have H := U.local_commutant_preserves_graph hc hQ ha f (Set.subset_univ _) h
    apply (U.closedSmoothField hc a d f).mem_graph_snd_inj H ((U.closedSmoothField hc a d f).graph.smul_mem c h)
    exact hcQ
  · intro a b ha hb
    simp only [Completion.coe_add,map_add,ha,hb,smul_add]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.ProperCircleArc
lemma exists_mem (x : AddCircle (2*Real.pi)) : ∃ I : ProperCircleArc, x ∈ I.carrier := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    let I : ProperCircleArc := ⟨t-Real.pi/2,t+Real.pi/2,by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    exact ⟨I,t,⟨by dsimp [I]; linarith [Real.pi_pos],by dsimp [I]; linarith [Real.pi_pos]⟩,rfl⟩
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.SmoothCircleFunction
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
 
lemma finite_arc_cutoffs : ∃ (s : Finset (AddCircle (2*Real.pi)))
    (χ : AddCircle (2*Real.pi) → SmoothCircleFunction) (I : AddCircle (2*Real.pi) → ProperCircleArc),
    (∀ x, (χ x).IsReal ∧ tsupport (χ x).onCircle ⊆ (I x).carrier) ∧
      ∀ t : AddCircle (2*Real.pi), ∃ x ∈ s, (χ x).onCircle t ≠ 0 := by
  classical
  have hex (x : AddCircle (2*Real.pi)) : ∃ I : ProperCircleArc, ∃ χ : SmoothCircleFunction,
      χ.IsReal ∧ χ.onCircle x=1 ∧ tsupport χ.onCircle ⊆ I.carrier := by
    obtain ⟨I,hI⟩ := ProperCircleArc.exists_mem x
    obtain ⟨χ,hχ,hχ1,hχS⟩ := exists_real_cutoff (isCompact_singleton (x := x)) I.isOpen_carrier
      (Set.singleton_subset_iff.mpr hI)
    exact ⟨I,χ,hχ,hχ1 (Set.mem_singleton _),hχS⟩
  choose I χ hχ hχ1 hχS using hex
  have hop (x : AddCircle (2*Real.pi)) : IsOpen {t | (χ x).onCircle t ≠ 0} := by
    exact isOpen_ne_fun (χ x).toContinuousMap.continuous continuous_const
  have hcov : (Set.univ : Set (AddCircle (2*Real.pi))) ⊆ ⋃ x, {t | (χ x).onCircle t ≠ 0} := by
    intro t _
    exact Set.mem_iUnion.mpr ⟨t,by change (χ t).onCircle t ≠ 0; rw [hχ1]; exact one_ne_zero⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover _ hop hcov
  refine ⟨s,χ,I,fun x => ⟨hχ x,hχS x⟩,?_⟩
  intro t
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ t))
  obtain ⟨hxS,hxt⟩ := Set.mem_iUnion.mp hx
  exact ⟨x,hxS,hxt⟩
def sumTests {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) : SmoothCircleFunction where
  toFun := fun t => ∑ i ∈ s, f i t
  periodic := fun t => Finset.sum_congr rfl (fun i _ => (f i).periodic t)
  smooth := ContDiff.sum (fun i _ => (f i).smooth)
@[simp] lemma sumTests_apply {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) (t : ℝ) :
    sumTests s f t=∑ i ∈ s, f i t := rfl
def reciprocal (f : SmoothCircleFunction) (hf : ∀ t, f t ≠ 0) : SmoothCircleFunction where
  toFun := fun t => (f t)⁻¹
  periodic := fun t => by dsimp only; rw [f.periodic]
  smooth := f.smooth.inv hf
@[simp] lemma reciprocal_apply (f : SmoothCircleFunction) (hf : ∀ t, f t ≠ 0) (t : ℝ) :
    reciprocal f hf t=(f t)⁻¹ := rfl
lemma finite_arc_partition (f : SmoothCircleFunction) : ∃ (s : Finset (AddCircle (2*Real.pi)))
    (g : AddCircle (2*Real.pi) → SmoothCircleFunction) (I : AddCircle (2*Real.pi) → ProperCircleArc),
    (∀ x, tsupport (g x).onCircle ⊆ (I x).carrier) ∧
      (f : ℝ → ℂ)=fun t => ∑ x ∈ s, g x t := by
  classical
  obtain ⟨s,χ,I,hχ,hcov⟩ := finite_arc_cutoffs
  let S := sumTests s (fun x => (χ x).power 2)
  have hSn (t : ℝ) : S t ≠ 0 := by
    have hr (x) : χ x t=((χ x t).re : ℂ) := by
      have H := congrArg Complex.im ((hχ x).1 t)
      apply Complex.ext
      · rfl
      · change -(χ x t).im=(χ x t).im at H
        change (χ x t).im=0
        linarith
    have he : (S t).re=∑ x ∈ s, (χ x t).re^2 := by
      simp only [S,sumTests_apply,power_apply,Complex.re_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hr,← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_re]
    have hp : 0 < ∑ x ∈ s, (χ x t).re^2 := by
      apply Finset.sum_pos' (fun x _ => sq_nonneg _)
      obtain ⟨x,hx,hxt⟩ := hcov (t : AddCircle (2*Real.pi))
      refine ⟨x,hx,sq_pos_of_ne_zero ?_⟩
      intro hz
      apply hxt
      change χ x t=0
      rw [hr,hz,Complex.ofReal_zero]
    intro hz
    rw [hz,Complex.zero_re] at he
    linarith
  let R := S.reciprocal hSn
  let g := fun x => ((χ x).power 2).mul (R.mul f)
  refine ⟨s,g,I,?_,?_⟩
  · intro x
    apply Subset.trans _ (hχ x).2
    apply closure_mono
    intro t ht
    have hn : (χ x).onCircle t ≠ 0 := by
      intro hz
      apply ht
      induction t using QuotientAddGroup.induction_on with
      | H t =>
        change (χ x t)^2*(R t*f t)=0
        change χ x t=0 at hz
        rw [hz,zero_pow (by decide),zero_mul]
    exact hn
  · funext t
    change f t=∑ x ∈ s, (χ x t)^2*((S t)⁻¹*f t)
    rw [← Finset.sum_mul]
    change f t=S t*((S t)⁻¹*f t)
    rw [← mul_assoc,mul_inv_cancel₀ (hSn t),one_mul]
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.ProperCircleArc
def translate (I : ProperCircleArc) (t : ℝ) : ProperCircleArc :=
  ⟨I.left+t,I.right+t,by linarith [I.nonempty'],by linarith [I.nondense']⟩
lemma translate_contains (I : ProperCircleArc) (t : ℝ) {x : AddCircle (2*Real.pi)}
    (hx : x-(t : AddCircle (2*Real.pi)) ∈ I.carrier) : x ∈ (I.translate t).carrier := by
  obtain ⟨s,hs,he⟩ := hx
  refine ⟨s+t,⟨by dsimp [translate]; linarith [hs.1],by dsimp [translate]; linarith [hs.2]⟩,?_⟩
  change ((s+t : ℝ) : AddCircle (2*Real.pi))=x
  change (s : AddCircle (2*Real.pi))=x-(t : AddCircle (2*Real.pi)) at he
  rw [AddCircle.coe_add,he,sub_add_cancel]
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_sumTests (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction) :
    U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients=
      ∑ i ∈ s, U.smoothSmear hc ha (f i).rapid_coefficients := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : SmoothCircleFunction.sumTests ∅ f=SmoothCircleFunction.constant 0 := by ext; simp
    rw [he,U.smoothSmear_constant]
    simp
  | @insert i s hi ih =>
    have he : SmoothCircleFunction.sumTests (insert i s) f=(f i).add (SmoothCircleFunction.sumTests s f) := by
      ext t
      simp only [SmoothCircleFunction.sumTests_apply,Finset.sum_insert hi,SmoothCircleFunction.add_apply]
    rw [he,U.smoothSmear_add_functions,ih,Finset.sum_insert hi]
lemma finite_test_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {ι : Type*} (s : Finset ι) (f : ι → SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V) (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hF : ∀ i ∈ s, ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (f i)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (f i)).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f)).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f)).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hcomm : U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients*R=
      R*U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients := by
    rw [U.smoothSmear_sumTests,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc ha (f i).rapid_coefficients) Q hQ (U.closedSmoothField hc a d (f i))
      (U.smoothSmear_graph hc ha (f i).rapid_coefficients) (hF i hi)
  have he := U.smoothSmear_core hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace
    (U.smoothSmear hc ha (SmoothCircleFunction.sumTests s f).rapid_coefficients)).closure=
      U.closedSmoothField hc a d (SmoothCircleFunction.sumTests s f) at he
  rw [← he] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant U.smoothEnergySpace _
    (U.smoothSmear_core_closable hc ha _) Q hQ hcomm hxy
lemma smoothConjugate_interval_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (I : ProperCircleArc)
    (hf : tsupport f.onCircle ⊆ I.carrier) (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ J : ProperCircleArc, Q ∈ (U.intervalAlgebra hc J).commutant)
    (ε : ℝ) (hε : 0 < ε) {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t _ x y hxy
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  apply U.local_commutant_preserves_graph hc (hQ (I.translate (-t))) ha (f.translate (-t)) _ huv
  intro z hz
  exact I.translate_contains (-t) (hf (f.translate_tsupport_subset (-t) hz))
lemma interval_commutant_all_graphs (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ I : ProperCircleArc, Q ∈ (U.intervalAlgebra hc I).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨s,g,I,hg,hfg⟩ := f.finite_arc_partition
  have he : f=SmoothCircleFunction.sumTests s g := SmoothCircleFunction.ext (congrFun hfg)
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    rw [he] at hxy ⊢
    apply U.finite_test_graph_invariant hc ha s g (R n) (fun z => U.smoothConjugate_smooth Q _ _ z.property) _ hxy
    intro i _ u v huv
    exact U.smoothConjugate_interval_graph hc ha (g i) (I i) (hg i) Q hQ _ _ huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
 

theorem interval_commutant_scalar (hc : A.toVertexAlgebra.C2Cofinite)
    {Q : Completion V →L[ℂ] Completion V}
    (hQ : ∀ I : ProperCircleArc, Q ∈ (U.intervalAlgebra hc I).commutant) :
    ∃ c : ℂ, Q=c • (1 : Completion V →L[ℂ] Completion V) := by
  apply U.global_commutant_scalar hc
  rw [← SetLike.mem_coe,localAlgebra,LocalOperatorAlgebra.coe_generated_commutant]
  intro B hB
  have hdata : ∀ B ∈ U.localGraphData hc Set.univ, Q*B=B*Q := by
    rintro B ⟨a,d,ha,f,_,i,j,rfl⟩
    apply ClosedGraphData.entry_commutes_of_graph_invariant
    · intro x y hxy
      exact U.interval_commutant_all_graphs hc ha f Q hQ hxy
    · intro x y hxy
      exact U.interval_commutant_all_graphs hc ha f Q.adjoint (fun I => star_mem (hQ I)) hxy
  rcases hB with hB | hB
  · exact (hdata B hB).symm
  · apply (hdata B ?_).symm
    obtain ⟨a,d,ha,f,hf,i,j,he⟩ := hB
    refine ⟨a,d,ha,f,hf,j,i,?_⟩
    have H := congrArg star he
    rw [star_star,ClosedGraphData.star_entry] at H
    exact H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_vacuum (t : ℝ) : U.rotation t (A.vacuum : Completion V)=(A.vacuum : Completion V) := by
  have h := U.rotation_grade t (⟨A.vacuum,by rw [A.grade_zero]; exact Submodule.subset_span (Set.mem_singleton _)⟩ : A.grade 0)
  simpa only [Nat.cast_zero,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] using h
lemma rotation_conjugate_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (I : ProperCircleArc)
    (hf : tsupport f.onCircle ⊆ I.carrier) (t : ℝ)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.intervalAlgebra hc (I.translate t)).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    ((U.rotation (-t)*Q*U.rotation t) x,(U.rotation (-t)*Q*U.rotation t) y) ∈
      (U.closedSmoothField hc a d f).graph := by
  have h := U.rotation_closedSmoothField_graph hc ha f t hxy
  have H := U.local_commutant_preserves_graph hc hQ ha (f.translate t)
    (fun z hz => I.translate_contains t (hf (f.translate_tsupport_subset t hz))) h
  have H' := U.rotation_closedSmoothField_graph hc ha (f.translate t) (-t) H
  simpa only [SmoothCircleFunction.translate_add,add_neg_cancel,SmoothCircleFunction.translate_zero,
    mul_apply_eq_comp] using H'
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI

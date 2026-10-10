import OAI.RingTheory.BassTrace.Subdivisions

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma Subdivision.carrier_marked {K : Geometry.SimplicialComplex ℝ V}
    (S : Subdivision K) {P : Set V} (hP : IsMarked K P) {E : Finset V}
    (hE : E ∈ S.complex.faces) (hEP : convexHull ℝ (E : Set V) ⊆ P) :
    ∃ F ∈ K.faces, convexHull ℝ (F : Set V) ⊆ P ∧
      convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) := by
  classical
  let c : ℝ := (E.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr
    (S.complex.nonempty_of_mem_faces hE).card_pos)
  have hsum : ∑ x ∈ E, c = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt (inv_pos.mp hc))
  have hb := Sparse.sum_weights_mem_convexHull E (fun _ _ => hc.le) hsum
  obtain ⟨F,hF,hbF,hFP⟩ := hP _ (hEP hb)
  let A := E.filter (· ∈ convexHull ℝ (F : Set V))
  have hbA : (∑ x ∈ E, c • x) ∈ convexHull ℝ (A : Set V) := by
    simpa only [A,coe_filter_mem] using (S.respects F hF E hE ▸
      (show (∑ x ∈ E, c • x) ∈ convexHull ℝ (E : Set V) ∩
        convexHull ℝ (F : Set V) from ⟨hb,hbF⟩))
  have hEA := Sparse.positiveCombination_carrier (S.complex.indep hE)
    (Finset.filter_subset _ _) (fun _ => c) (fun _ _ => hc) hsum hbA
  refine ⟨F,hF,hFP,convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro x hx
  exact (Finset.mem_filter.mp (hEA hx)).2

structure PointFiltration (K : Geometry.SimplicialComplex ℝ V) (n : ℕ) where
  T : ℕ → Geometry.SimplicialComplex ℝ V
  Z : ℕ → Set V
  top : T n = K
  top_space : Z n = K.space
  marked : ∀ i, i ≤ n → IsMarked (T i) (Z i)
  finer : ∀ i, i < n → Refines (T i) (T (i+1))
  nested : ∀ i, i < n → Z i ⊆ Z (i+1)
  drop : ∀ i, i < n → DimensionDrop (T (i+1)) (T i) (Z (i+1)) (Z i)

namespace PointFiltration

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ} (Q : PointFiltration K n)

lemma refines {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Refines (Q.T j) (Q.T i) := by
  induction i, hji using Nat.le_induction with
  | base => exact refines_self _
  | succ i hji ih => exact ih (by omega) |>.trans (Q.finer i (by omega))

lemma subset {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Q.Z j ⊆ Q.Z i := by
  induction i, hji using Nat.le_induction with
  | base => exact subset_rfl
  | succ i hji ih => exact (ih (by omega)).trans (Q.nested i (by omega))

lemma iterated_drop {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (_hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    {E : Finset V} (hE : E ∈ (Q.T j).faces)
    (hEF : convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Q.Z j) :
    E.card + (i-j) ≤ F.card := by
  classical
  generalize hd : i-j = d
  induction d using Nat.strong_induction_on generalizing j E with
  | h d ih =>
    by_cases hji' : j = i
    · subst j
      have hcard := (Q.T i).indep hE |>.card_le_card_of_subset_affineSpan
        ((subset_convexHull ℝ _).trans ((hEF.trans Set.inter_subset_left).trans
          (convexHull_subset_affineSpan _)))
      have : d = 0 := by simpa using hd.symm
      simpa [this] using hcard
    · have hj : j < i := by omega
      obtain ⟨S,hS⟩ := Q.finer j (by omega)
      obtain ⟨W,hW⟩ := Q.refines (show j+1 ≤ i by omega) hin
      have hm : IsMarked (Q.T (j+1)) (convexHull ℝ (F : Set V) ∩ Q.Z (j+1)) :=
        (hW ▸ W.marked hF).inter (Q.marked (j+1) (by omega))
      have hEP : convexHull ℝ (E : Set V) ⊆
          convexHull ℝ (F : Set V) ∩ Q.Z (j+1) :=
        Set.subset_inter (hEF.trans Set.inter_subset_left)
          ((hEF.trans Set.inter_subset_right).trans (Q.nested j (by omega)))
      obtain ⟨U,hU,hUP,hEU⟩ := S.carrier_marked hm (hS.symm ▸ hE) hEP
      have hcard := Q.drop j (by omega) U hU (hUP.trans Set.inter_subset_right)
        E hE (Set.subset_inter hEU (hEF.trans Set.inter_subset_right))
      have hrec := ih (i-(j+1)) (by omega) (show j+1 ≤ i by omega) hU hUP rfl
      omega

lemma dimension_bound (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {E : Finset V} (hE : E ∈ (Q.T i).faces) (hEZ : convexHull ℝ (E : Set V) ⊆ Q.Z i) :
    E.card ≤ i+1 := by
  obtain ⟨S,hS⟩ := Q.refines hi le_rfl
  obtain ⟨F,hF,hEF⟩ := S.carrier E (hS.symm ▸ hE)
  have hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z n := by
    rw [Q.top_space]
    exact K.convexHull_subset_space (Q.top ▸ hF)
  have hb := Q.iterated_drop hi le_rfl hF hFZ hE (Set.subset_inter hEF hEZ)
  have hc := hK F (Q.top ▸ hF)
  omega

lemma card_lower_of_mem_zero {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    (hzF : z ∈ convexHull ℝ (F : Set V)) : i+1 ≤ F.card := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le i) hi
  have hm : IsMarked (Q.T 0) (convexHull ℝ (F : Set V) ∩ Q.Z 0) :=
    (hS ▸ S.marked hF).inter (Q.marked 0 (Nat.zero_le n))
  obtain ⟨E,hE,_,hEF⟩ := hm z ⟨hzF,hz⟩
  have hb := Q.iterated_drop (Nat.zero_le i) hi hF hFZ hE hEF
  have hc := (Q.T 0).nonempty_of_mem_faces hE |>.card_pos
  omega

lemma zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {z : V} (hz : z ∈ Q.Z 0) :
    ∃ F ∈ (Q.T i).faces, convexHull ℝ (F : Set V) ⊆ Q.Z i ∧
      z ∈ convexHull ℝ (F : Set V) ∧ F.card = i+1 ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) → F ⊆ E) ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) →
        E.card = i+1 → E = F) := by
  have hzi := Q.subset (Nat.zero_le i) hi hz
  obtain ⟨F,hF,hzF,hmin⟩ := exists_smallest_carrier (Q.T i)
    ((Q.marked i hi).subset_space hzi)
  obtain ⟨E,hE,hzE,hEZ⟩ := Q.marked i hi z hzi
  have hFZ := (convexHull_mono (hmin E hE hzE)).trans hEZ
  have hb := Q.dimension_bound hK hi hF hFZ
  have hl := Q.card_lower_of_mem_zero hi hz hF hFZ hzF
  have hc : F.card = i+1 := by omega
  refine ⟨F,hF,hFZ,hzF,hc,hmin,?_⟩
  intro E hE hzE hcard
  exact (Finset.eq_of_subset_of_card_le (hmin E hE hzE) (by omega)).symm

end PointFiltration

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K S T : Geometry.SimplicialComplex ℝ V}

lemma IsMarked.contains_of_positive_barycenter {P : Set V} (hP : IsMarked K P)
    {F : Finset V} (hF : F ∈ K.faces) (w : V → ℝ)
    (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hp : (∑ x ∈ F, w x • x) ∈ P) : convexHull ℝ (F : Set V) ⊆ P := by
  obtain ⟨E,hE,hpE,hEP⟩ := hP _ hp
  exact (convexHull_mono (Sparse.simplex_contains_positivePoint K hF hE w hw hws hpE)).trans hEP

lemma IsMarked.face_in_union {I : Type*} {P : I → Set V}
    (hP : ∀ i, IsMarked K (P i)) {F : Finset V} (hF : F ∈ K.faces)
    (hFU : convexHull ℝ (F : Set V) ⊆ ⋃ i, P i) :
    ∃ i, convexHull ℝ (F : Set V) ⊆ P i := by
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos)
  have hs : ∑ x ∈ F, c = 1 := by simp [c,ne_of_gt (Nat.cast_pos.mpr
    (K.nonempty_of_mem_faces hF).card_pos : (0 : ℝ) < F.card)]
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFU (Sparse.sum_weights_mem_convexHull F
    (fun _ _ => hc.le) hs))
  exact ⟨i,(hP i).contains_of_positive_barycenter hF _ (fun _ _ => hc) hs hi⟩

lemma dimensionDrop_union_levels {I : Type*} (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    {P : Set V} {Z : I → Set V} (hZ : ∀ i, IsMarked S (Z i))
    (hlevel : ∀ i, Z i ⊆ {x | a i x = b i})
    (hgeneric : ∀ F ∈ T.faces, ∀ i, ∃ v ∈ F, a i v ≠ b i) :
    DimensionDrop T S P (⋃ i, Z i) := by
  intro F hF _ E hE hEF
  obtain ⟨i,hi⟩ := IsMarked.face_in_union hZ hE (fun x hx => (hEF hx).2)
  exact card_lt_of_generic_hyperplane (S.indep hE)
    ((subset_convexHull ℝ _).trans (fun x hx => (hEF hx).1)) (a i) (b i)
    (fun x hx => hlevel i (hi (subset_convexHull ℝ _ hx))) (hgeneric F hF i)

lemma DimensionDrop.refine {P Z : Set V} (h : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) {L : Geometry.SimplicialComplex ℝ V}
    (hL : Refines L S) (hST : Refines S T) : DimensionDrop T L P Z := by
  obtain ⟨A,rfl⟩ := hL
  obtain ⟨B,rfl⟩ := hST
  intro F hF hFP E hE hEF
  have hm : IsMarked B.complex (convexHull ℝ (F : Set V) ∩ Z) :=
    (B.marked hF).inter hZ
  obtain ⟨C,hC,hCP,hEC⟩ := A.carrier_marked hm hE hEF
  have hcard : E.card ≤ C.card := (A.complex.indep hE).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hEC.trans (convexHull_subset_affineSpan _)))
  exact lt_of_le_of_lt hcard (h F hF hFP C hC hCP)

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma IsMarked.inter_iInter {I : Type*} {P : Set V} {Q : I → Set V}
    (hP : IsMarked K P) (hQ : ∀ i, IsMarked K (K.space ∩ Q i)) :
    IsMarked K (P ∩ ⋂ i, Q i) := by
  intro x hx
  obtain ⟨F,hF,hxF,hmin⟩ := exists_smallest_carrier K (hP.subset_space hx.1)
  obtain ⟨E,hE,hxE,hEP⟩ := hP _ hx.1
  refine ⟨F,hF,hxF,fun y hy => ⟨hEP (convexHull_mono (hmin E hE hxE) hy),?_⟩⟩
  apply Set.mem_iInter.mpr
  intro i
  obtain ⟨E,hE,hxE,hEQ⟩ := hQ i _ ⟨hP.subset_space hx.1,Set.mem_iInter.mp hx.2 i⟩
  exact (hEQ (convexHull_mono (hmin E hE hxE) hy)).2

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def closedPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∀ j ∈ A, d.form j x ≤ d.level j}

def outerPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∃ j ∈ A, d.level j ≤ d.form j x}

def spherePatch (P : Set V) (A : Finset J) : Set V :=
  d.closedPatch P A ∩ {x | ∃ j ∈ A, d.form j x = d.level j}

lemma closedPatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.closedPatch P A) := by
  have hh := hP.inter_iInter (I := A) (Q := fun j => {x | d.form j x ≤ d.level j})
    (fun j => by simpa only [LocalCutData.globalComplex_space,UniversalCuts.onComplex]
      using (d.onComplex S).globalComplex_marked_le j)
  convert hh using 1
  ext x
  simp only [closedPatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,Subtype.forall]

lemma outerPatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.outerPatch P A) := by
  have hh := hP.inter (IsMarked.iUnion (fun j : A => (d.onComplex S).globalComplex_marked_ge j))
  convert hh using 1
  ext x
  simp only [outerPatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Subtype.exists]
  constructor
  · rintro ⟨hx,j,hj,hh⟩
    exact ⟨hx,j,hj,(LocalCutData.globalComplex_space (d.onComplex S)) ▸ hP.subset_space hx,hh⟩
  · rintro ⟨hx,j,hj,_,hh⟩
    exact ⟨hx,j,hj,hh⟩

lemma spherePatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.spherePatch P A) := by
  have hC := d.closedPatch_marked hP A
  have hh := hC.inter (IsMarked.iUnion (fun j : A => (d.onComplex S).globalComplex_marked_eq j))
  convert hh using 1
  ext x
  simp only [spherePatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Subtype.exists]
  constructor
  · rintro ⟨hx,j,hj,hh⟩
    exact ⟨hx,j,hj,(LocalCutData.globalComplex_space (d.onComplex S)) ▸ hC.subset_space hx,hh⟩
  · rintro ⟨hx,j,hj,_,hh⟩
    exact ⟨hx,j,hj,hh⟩

lemma spherePatches_dimensionDrop {I : Type*} {S : Geometry.SimplicialComplex ℝ V}
    {P : I → Set V} (hP : ∀ i, IsMarked (d.onComplex S).globalComplex (P i))
    (A : I → Finset J) (t : ℝ) (ht : ∀ j, d.level j = t)
    (hg : ∀ F ∈ S.faces, ∀ j, ∃ v ∈ F, d.form j v ≠ t) (Z : Set V) :
    DimensionDrop S (d.onComplex S).globalComplex Z (⋃ i, d.spherePatch (P i) (A i)) := by
  intro F hF _ E hE hEF
  obtain ⟨i,hi⟩ := IsMarked.face_in_union (fun i => d.spherePatch_marked (hP i) (A i))
    hE (fun x hx => (hEF hx).2)
  apply card_lt_of_generic_max_level (fun j : A i => d.form j) t
    ((d.onComplex S).globalComplex.nonempty_of_mem_faces hE)
    ((d.onComplex S).globalComplex.indep hE)
    ((subset_convexHull ℝ _).trans (fun x hx => (hEF hx).1))
    (fun j => hg F hF j)
  · intro x hx j
    simpa only [← ht j] using (hi hx).1.2 j j.property
  · intro x hx
    obtain ⟨j,hj,hjx⟩ := (hi hx).2
    exact ⟨⟨j,hj⟩,hjx.trans (ht j)⟩

end UniversalCuts

end

open Set Finset

open scoped Classical Topology

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

namespace MarkedFamily

lemma set_localConstancy {T : SubdivisionFamily X K} (P : MarkedFamily T)
    (s : Finset V) (hs : s ∈ K.faces) :
    IsLocallyConstant (fun x => P.val x ∩ convexHull ℝ (s : Set V)) := by
  let U : Set (Finset V) → Set V := fun A => ⋃ t ∈ A, convexHull ℝ (t : Set V)
  have he (x : X) : P.val x ∩ convexHull ℝ (s : Set V) = U
      ((restrictComplex (geometricRestriction (T.val x).complex (P.val x))
        (convexHull ℝ (s : Set V))).faces) := by
    have hh := restrictComplex_space_of_respects
      (geometricRestriction (T.val x).complex (P.val x)) (convexHull ℝ (s : Set V))
      (fun t ht => (T.val x).respects s hs t ht.1)
    rw [(P.marked x).restriction_space] at hh
    exact hh.symm
  simp_rw [he]
  exact (P.localConstancy s hs).comp U

def ofSets (T : SubdivisionFamily X K) (P : X → Set V)
    (hP : ∀ x, IsMarked (T.val x).complex (P x))
    (hLC : ∀ s ∈ K.faces, IsLocallyConstant (fun x => P x ∩ convexHull ℝ (s : Set V))) :
    MarkedFamily T where
  val := P
  marked := hP
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set V → Set (Finset V) :=
      fun A Q => {t | t ∈ A ∧ convexHull ℝ (t : Set V) ⊆ Q}
    have he (x : X) :
        (restrictComplex (geometricRestriction (T.val x).complex (P x))
          (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces)
        (P x ∩ convexHull ℝ (s : Set V)) := by
      ext t
      change ((t ∈ (T.val x).complex.faces ∧ convexHull ℝ (t : Set V) ⊆ P x) ∧
        (t : Set V) ⊆ convexHull ℝ (s : Set V)) ↔
        ((t ∈ (T.val x).complex.faces ∧ (t : Set V) ⊆ convexHull ℝ (s : Set V)) ∧
          convexHull ℝ (t : Set V) ⊆ P x ∩ convexHull ℝ (s : Set V))
      constructor
      · rintro ⟨⟨ht,hP⟩,hst⟩
        exact ⟨⟨ht,hst⟩,Set.subset_inter hP (convexHull_min hst (convex_convexHull _ _))⟩
      · rintro ⟨⟨ht,hst⟩,hP⟩
        exact ⟨⟨ht,fun _ hy => (hP hy).1⟩,hst⟩
    simp_rw [he]
    exact (T.localConstancy s hs).comp₂ (hLC s hs) F

def refine {T S : SubdivisionFamily X K} (P : MarkedFamily T)
    (hS : ∀ x, Refines (S.val x).complex (T.val x).complex) : MarkedFamily S :=
  ofSets S P.val (fun x => by
    obtain ⟨W,hW⟩ := hS x
    rw [← hW]
    exact W.preserves_marked (P.marked x)) P.set_localConstancy

def inter {T : SubdivisionFamily X K} (P Q : MarkedFamily T) : MarkedFamily T :=
  ofSets T (fun x => P.val x ∩ Q.val x)
    (fun x => (P.marked x).inter (Q.marked x)) (by
      intro s hs
      have hh := (P.set_localConstancy s hs).comp₂ (Q.set_localConstancy s hs) Set.inter
      convert hh using 1
      ext x y
      change ((y ∈ P.val x ∧ y ∈ Q.val x) ∧ y ∈ convexHull ℝ (s : Set V)) ↔
        ((y ∈ P.val x ∧ y ∈ convexHull ℝ (s : Set V)) ∧
          (y ∈ Q.val x ∧ y ∈ convexHull ℝ (s : Set V)))
      tauto)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

lemma locallyConstant_active_union {I : Type*} (A : I → Set V) (B : I → Set X)
    (hB : ∀ i, IsClopen (B i)) (Q : Set V)
    (hfinite : {i | (A i ∩ Q).Nonempty}.Finite) :
    IsLocallyConstant (fun x => (⋃ i, if x ∈ B i then A i else ∅) ∩ Q) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hp (i : I) : ∀ᶠ y in 𝓝 x, (y ∈ B i ↔ x ∈ B i) := by
    by_cases hx : x ∈ B i
    · exact Filter.Eventually.mono ((hB i).2.mem_nhds hx) (by intro y hy; exact ⟨fun _ => hx, fun _ => hy⟩)
    · exact Filter.Eventually.mono ((hB i).1.isOpen_compl.mem_nhds hx)
        (by intro y hy; exact ⟨fun h => False.elim (hy h), fun h => False.elim (hx h)⟩)
  filter_upwards [hfinite.eventually_all.mpr (fun i _ => hp i)] with y hy
  ext p
  simp only [Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hyB : y ∈ B i
    · simp only [hyB,ite_true] at hi
      have hxB := (hy i ⟨p,hi,hpQ⟩).mp hyB
      exact ⟨⟨i,by simpa only [hxB,ite_true] using hi⟩,hpQ⟩
    · simp only [hyB,ite_false,Set.mem_empty_iff_false] at hi
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hxB : x ∈ B i
    · simp only [hxB,ite_true] at hi
      have hyB := (hy i ⟨p,hi,hpQ⟩).mpr hxB
      exact ⟨⟨i,by simpa only [hyB,ite_true] using hi⟩,hpQ⟩
    · simp only [hxB,ite_false,Set.mem_empty_iff_false] at hi

end MarkedFamily

end BassTrace.Sparse.Cuts

end

end OAI

import OAI.Topology.EilenbergGanea.SmallHolonomy
import OAI.GroupTheory.RightAngledArtin.TraceWords

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace AffineTransport

/-- A finite family of proper quaternion subspaces cannot cover ℍ. -/
theorem exists_avoid_subspaces {I : Type*} [Finite I]
    (p : I → Submodule ℝ ℍ) (hp : ∀ i, p i ≠ ⊤) :
    ∃ q : ℍ, ∀ i, q ∉ p i := by
  have ho (i) : IsOpen ((p i : Set ℍ)ᶜ) :=
    (p i).closed_of_finiteDimensional.isOpen_compl
  have hd (i) : Dense ((p i : Set ℍ)ᶜ) := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.not_nonempty_iff_eq_empty.mp
    intro h
    exact hp i ((p i).eq_top_of_nonempty_interior' h)
  obtain ⟨q,hq⟩ := (dense_iInter_of_isOpen ho hd).nonempty
  exact ⟨q,Set.mem_iInter.mp hq⟩

/-- Simultaneous general position for finitely many local quaternion gauges.
Different vertices may use different invertible linear transformations in each
chart. No flatness or topology is assumed in this finite-dimensional lemma. -/
theorem exists_triangle_general_position {A V : Type*} [Finite A] [Fintype V]
    (T : A → V → ℍ ≃ₗ[ℝ] ℍ) :
    ∃ q : V → ℍ, ∀ a (s : Finset V), s.card ≤ 3 →
      LinearIndepOn ℝ (fun v => T a v (q v)) (s : Set V) := by
  classical
  suffices ∀ U : Finset V, ∃ q : V → ℍ, ∀ a (s : Finset V), s ⊆ U → s.card ≤ 3 →
      LinearIndepOn ℝ (fun v => T a v (q v)) (s : Set V) by
    obtain ⟨q,hq⟩ := this Finset.univ
    exact ⟨q,fun a s h => hq a s (Finset.subset_univ _) h⟩
  intro U
  induction U using Finset.induction with
  | empty =>
      refine ⟨0,?_⟩
      intro a s hs _
      have : s = ∅ := Finset.subset_empty.mp hs
      subst s
      simpa only [Finset.coe_empty,Pi.zero_apply] using
        linearIndepOn_empty ℝ (fun v => T a v (0 : ℍ))
  | @insert v U hv ih =>
      obtain ⟨q,hq⟩ := ih
      let I := A × {s : Finset V // s ⊆ U ∧ s.card ≤ 2}
      let p : I → Submodule ℝ ℍ := fun i =>
        (Submodule.span ℝ ((fun w => T i.1 w (q w)) '' (i.2.val : Set V))).comap
          (T i.1 v).toLinearMap
      have hp (i : I) : p i ≠ ⊤ := by
        have hf : Module.finrank ℝ (Submodule.span ℝ
            ((fun w => T i.1 w (q w)) '' (i.2.val : Set V))) ≤ 2 := by
          have hh := finrank_span_finset_le_card (R := ℝ) (i.2.val.image (fun w => T i.1 w (q w)))
          rw [Finset.coe_image] at hh
          exact hh.trans ((Finset.card_image_le).trans i.2.property.2)
        have hproper : Submodule.span ℝ ((fun w => T i.1 w (q w)) ''
            (i.2.val : Set V)) ≠ ⊤ := by
          apply ne_of_lt (Submodule.lt_top_of_finrank_lt_finrank _)
          rw [Quaternion.finrank_eq_four]
          omega
        intro hh
        apply hproper
        apply top_unique
        intro x _
        have hm : (T i.1 v).symm x ∈ p i := by rw [hh]; trivial
        simpa only [p,Submodule.mem_comap,LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using hm
      obtain ⟨z,hz⟩ := exists_avoid_subspaces p hp
      refine ⟨Function.update q v z,?_⟩
      intro a s hs hc
      by_cases hvs : v ∈ s
      · have hsub : s.erase v ⊆ U := by
          intro w hw
          have hh := hs (Finset.mem_of_mem_erase hw)
          exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase hw)
        have hcard : (s.erase v).card ≤ 2 := by
          have he := Finset.card_erase_add_one hvs
          omega
        have heq : ∀ w ∈ (s.erase v : Finset V), Function.update q v z w = q w := by
          intro w hw
          exact Function.update_of_ne (Finset.ne_of_mem_erase hw) _ _
        have hi : LinearIndepOn ℝ (fun w => T a w (Function.update q v z w))
            ((s.erase v : Finset V) : Set V) := by
          apply (hq a (s.erase v) hsub (by omega)).congr
          intro w hw
          dsimp only
          rw [heq w hw]
        have hn : T a v (Function.update q v z v) ∉ Submodule.span ℝ
            ((fun w => T a w (Function.update q v z w)) ''
              ((s.erase v : Finset V) : Set V)) := by
          rw [Function.update_self]
          have him : ((fun w => T a w (Function.update q v z w)) ''
              ((s.erase v : Finset V) : Set V)) =
              ((fun w => T a w (q w)) '' ((s.erase v : Finset V) : Set V)) := by
            apply Set.image_congr
            intro w hw
            rw [heq w hw]
          rw [him]
          exact hz ⟨a,⟨s.erase v,hsub,hcard⟩⟩
        have ht := (linearIndepOn_insert (by simp : v ∉ ((s.erase v : Finset V) : Set V))).mpr
          ⟨hi,hn⟩
        simpa only [← Finset.coe_insert,Finset.insert_erase hvs] using ht
      · have hsub : s ⊆ U := by
          intro w hw
          have hh := hs hw
          rcases Finset.mem_insert.mp hh with rfl | hh
          · exact False.elim (hvs hw)
          · exact hh
        apply (hq a s hsub hc).congr
        intro w hw
        dsimp only
        rw [Function.update_of_ne (by intro h; subst w; exact hvs hw)]


@[simp] theorem unit_norm (h : SU2) : ‖(h : ℍ)‖ = 1 :=
  (quaternion_mem_unitary_iff _).mp h.property

def leftLinearEquiv (h : SU2) : ℍ ≃ₗ[ℝ] ℍ where
  toFun q := (h : ℍ) * q
  invFun q := (h⁻¹ : SU2) * q
  left_inv q := by simp [← mul_assoc,← Submonoid.coe_mul]
  right_inv q := by simp [← mul_assoc,← Submonoid.coe_mul]
  map_add' _ _ := mul_add _ _ _
  map_smul' r q := mul_smul_comm r (h : ℍ) q

@[simp] theorem leftLinearEquiv_apply (h : SU2) (q : ℍ) :
    leftLinearEquiv h q = (h : ℍ) * q := rfl

theorem normalize_left (h : SU2) {q : ℍ} (hq : q ≠ 0) :
    normalizeQuaternion ((h : ℍ) * q) = h * normalizeQuaternion q := by
  have hh : (h : ℍ) * q ≠ 0 := by
    exact (leftLinearEquiv h).map_ne_zero_iff.mpr hq
  apply Subtype.ext
  rw [normalizeQuaternion_coe_of_ne_zero hh]
  change ‖(h : ℍ) * q‖⁻¹ • ((h : ℍ) * q) = (h : ℍ) * (normalizeQuaternion q : ℍ)
  rw [normalizeQuaternion_coe_of_ne_zero hq,norm_mul,unit_norm,one_mul,mul_smul_comm]

section FiniteSimplex
variable {V : Type*} [Fintype V]

def coordinateSimplex : Set (V → ℝ) :=
  {weights | (∀ vertex, 0 ≤ weights vertex) ∧ ∑ vertex, weights vertex = 1}

/-- Closed coordinate face of the standard simplex. -/
def face (s : Finset V) : Set (V → ℝ) :=
  {b | b ∈ coordinateSimplex ∧ ∀ v ∉ s, b v = 0}

/-- The whole two-skeleton of a finite standard simplex. -/
def triangleSet : Set (V → ℝ) :=
  ⋃ s : {s : Finset V // s.card ≤ 3}, face s.val

abbrev TrianglePoint (V : Type*) [Fintype V] := (triangleSet : Set (V → ℝ))

theorem mem_triangleSet {b : V → ℝ} : b ∈ triangleSet ↔
    ∃ s : Finset V, s.card ≤ 3 ∧ b ∈ coordinateSimplex ∧ ∀ v ∉ s, b v = 0 := by
  simp only [triangleSet,Set.mem_iUnion,face,Set.mem_ofPred_eq,Subtype.exists,exists_prop]

omit [Fintype V] in
private theorem isClosed_face_support (s : Finset V) :
    IsClosed {b : V → ℝ | ∀ v ∉ s, b v = 0} := by
  have he : {b : V → ℝ | ∀ v ∉ s, b v = 0} =
      ⋂ v, ⋂ (_ : v ∉ s), {b : V → ℝ | b v = 0} := by ext b; simp
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply v) continuous_const

theorem isCompact_face (s : Finset V) : IsCompact (face s) := by
  have compact_simplex : IsCompact (coordinateSimplex : Set (V → ℝ)) := by
    convert isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous using 1
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext weights
    simp [coordinateSimplex]
  exact compact_simplex.inter_right (isClosed_face_support s)

theorem isCompact_triangleSet : IsCompact (triangleSet : Set (V → ℝ)) :=
  isCompact_iUnion fun _ => isCompact_face _

instance : CompactSpace (TrianglePoint V) :=
  isCompact_iff_compactSpace.mp isCompact_triangleSet

theorem point_simplex (b : TrianglePoint V) : (b : V → ℝ) ∈ coordinateSimplex := by
  obtain ⟨_,_,h,_⟩ := mem_triangleSet.mp b.property
  exact h

theorem point_exists_nonzero (b : TrianglePoint V) : ∃ v, (b : V → ℝ) v ≠ 0 := by
  by_contra! h
  have he := (point_simplex b).2
  simp only [h,Finset.sum_const_zero] at he
  norm_num at he

variable (h : V → V → SU2) (q : V → ℍ)

def rawGauge (a : V) (b : V → ℝ) : ℍ := ∑ v, b v • ((h a v : ℍ) * q v)

def GeneralPosition : Prop := ∀ a (s : Finset V), s.card ≤ 3 →
  LinearIndepOn ℝ (fun v => (h a v : ℍ) * q v) (s : Set V)

theorem exists_generalPosition : ∃ q : V → ℍ, GeneralPosition h q := by
  obtain ⟨q,hq⟩ := exists_triangle_general_position (fun a v => leftLinearEquiv (h a v))
  exact ⟨q,hq⟩

theorem rawGauge_ne_zero (hq : GeneralPosition h q) (a : V) (b : TrianglePoint V) :
    rawGauge h q a b ≠ 0 := by
  classical
  obtain ⟨s,hs,hb,hout⟩ := mem_triangleSet.mp b.property
  intro he
  have he' : ∑ v ∈ s, (b : V → ℝ) v • ((h a v : ℍ) * q v) = 0 := by
    rw [← he]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [hout v hv,zero_smul]
  have hz := (linearIndepOn_iff'.mp (hq a s hs)) s b (Set.Subset.refl _) he'
  have hall : ∀ v, (b : V → ℝ) v = 0 := by
    intro v
    by_cases hv : v ∈ s
    · exact hz v hv
    · exact hout v hv
  have heq := hb.2
  simp only [hall,Finset.sum_const_zero] at heq
  norm_num at heq

def gauge (a : V) (b : TrianglePoint V) : SU2 := normalizeQuaternion (rawGauge h q a b)

theorem continuous_rawGauge (a : V) : Continuous (rawGauge h q a) :=
  continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const

theorem continuous_gauge (hq : GeneralPosition h q) (a : V) : Continuous (gauge h q a) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  exact ContinuousAt.comp (f := fun c : TrianglePoint V => rawGauge h q a c)
    (normalizeQuaternion_continuousAt (rawGauge_ne_zero h q hq a b))
    ((continuous_rawGauge h q a).comp continuous_subtype_val).continuousAt

/-- Uniform modulus over all charts, including across the edges of all simplices. -/
theorem gauges_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c : TrianglePoint V, dist b c < δ →
      ∀ a, dist (gauge h q a b) (gauge h q a c) < ε := by
  have hc : Continuous (fun b : TrianglePoint V => fun a => gauge h q a b) :=
    continuous_pi fun a => continuous_gauge h q hq a
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  obtain ⟨δ,hδ,H⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro b c hbc a
  exact lt_of_le_of_lt (dist_le_pi_dist (fun a => gauge h q a b) (fun a => gauge h q a c) a) (H hbc)

end FiniteSimplex

theorem unitary_dist_left (a b c : SU2) : dist (a * b) (a * c) = dist b c := by
  change dist ((a : ℍ) * (b : ℍ)) ((a : ℍ) * (c : ℍ)) = dist (b : ℍ) (c : ℍ)
  rw [dist_eq_norm,dist_eq_norm,← mul_sub,norm_mul,unit_norm,one_mul]

theorem unitary_dist_inv_mul_one (a b : SU2) : dist (a⁻¹ * b) 1 = dist a b := by
  rw [← unitary_dist_left a (a⁻¹ * b) 1]
  simp [dist_comm]

theorem unitary_dist_mul_one_le (a b : SU2) :
    dist (a * b) 1 ≤ dist a 1 + dist b 1 := by
  calc
    dist (a * b) 1 ≤ dist (a * b) a + dist a 1 := dist_triangle _ _ _
    _ = dist b 1 + dist a 1 := by
      exact congrArg (fun t => t + dist a 1) (by simpa only [mul_one] using unitary_dist_left a b 1)
    _ = dist a 1 + dist b 1 := add_comm _ _

section Connection
variable {V : Type*} [Fintype V]
variable (L : SimpleGraph V)

def Related (a b : V) : Prop := a = b ∨ L.Adj a b

omit [Fintype V] in
theorem Related.refl (a : V) : Related L a a := Or.inl rfl

omit [Fintype V] in
theorem Related.symm {a b : V} : Related L a b → Related L b a := by
  rintro (rfl | h)
  · exact Related.refl L _
  · exact Or.inr h.symm

def Star (a : V) (b : TrianglePoint V) : Prop :=
  ∀ v, (b : V → ℝ) v ≠ 0 → Related L a v

def CliquePoint (b : TrianglePoint V) : Prop :=
  ∀ a, (b : V → ℝ) a ≠ 0 → Star L a b

def Compatible (b c : TrianglePoint V) : Prop :=
  ∀ v w, ((b : V → ℝ) v ≠ 0 ∨ (c : V → ℝ) v ≠ 0) →
    ((b : V → ℝ) w ≠ 0 ∨ (c : V → ℝ) w ≠ 0) → Related L v w

def root (b : TrianglePoint V) : V := Classical.choose (point_exists_nonzero b)

theorem root_mem (b : TrianglePoint V) : (b : V → ℝ) (root b) ≠ 0 :=
  Classical.choose_spec (point_exists_nonzero b)

variable (h : V → V → SU2) (q : V → ℍ)

def FlatConnection : Prop := ∀ a b c, Related L a b → Related L b c →
  Related L a c → h a b * h b c = h a c

theorem rawGauge_transition (hf : FlatConnection L h) {a c : V}
    {b : TrianglePoint V} (hac : Related L a c) (ha : Star L a b) (hc : Star L c b) :
    rawGauge h q a b = (h a c : ℍ) * rawGauge h q c b := by
  classical
  simp only [rawGauge,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : (b : V → ℝ) v = 0
  · simp [hv]
  · rw [mul_smul_comm,← mul_assoc,← Submonoid.coe_mul,hf a c v hac (hc v hv) (ha v hv)]

theorem gauge_transition (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {a c : V} {b : TrianglePoint V} (hac : Related L a c)
    (ha : Star L a b) (hc : Star L c b) :
    gauge h q a b = h a c * gauge h q c b := by
  unfold gauge
  rw [rawGauge_transition L h q hf hac ha hc]
  exact normalize_left _ (rawGauge_ne_zero h q hq c b)

def chartTransport (a : V) (b c : TrianglePoint V) : SU2 :=
  (gauge h q a b)⁻¹ * gauge h q a c

def transport (b c : TrianglePoint V) : SU2 := chartTransport h q (root b) b c

theorem transport_chart (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c : TrianglePoint V} (hb : Compatible L b c) {a : V}
    (hab : Star L a b) (hac : Star L a c) :
    transport h q b c = chartTransport h q a b c := by
  have hrb : Star L (root b) b := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inl hv)
  have hrc : Star L (root b) c := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inr hv)
  have har : Related L a (root b) := hab _ (root_mem b)
  unfold transport chartTransport
  rw [gauge_transition L h q hf hq har hab hrb,
    gauge_transition L h q hf hq har hac hrc]
  group

theorem compatible_symm {b c : TrianglePoint V} (hb : Compatible L b c) :
    Compatible L c b := fun v w hv hw => hb v w hv.symm hw.symm

theorem transport_reverse (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c : TrianglePoint V} (hb : Compatible L b c) :
    transport h q c b = (transport h q b c)⁻¹ := by
  have hrc : Star L (root b) c := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inr hv)
  have hrb : Star L (root b) b := fun v hv => hb _ _ (Or.inl (root_mem b)) (Or.inl hv)
  rw [transport_chart L h q hf hq (compatible_symm L hb) hrc hrb]
  unfold transport chartTransport
  group

theorem chartTransport_trans (a : V) (b c d : TrianglePoint V) :
    chartTransport h q a b c * chartTransport h q a c d = chartTransport h q a b d := by
  unfold chartTransport
  group

theorem exists_large_coordinate (b : TrianglePoint V) :
    ∃ a, 1 / (Fintype.card V + 1 : ℝ) < (b : V → ℝ) a := by
  by_contra! H
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => H a)
  have hb := (point_simplex b).2
  rw [hb,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (Fintype.card V : ℝ) + 1 := by positivity
  have he := (le_div_iff₀ hd).mp (by simpa only [mul_one_div] using hs)
  linarith

theorem nearby_star {b c : TrianglePoint V} {a : V}
    (ha : 1 / (Fintype.card V + 1 : ℝ) < (b : V → ℝ) a)
    (hc : CliquePoint L c) (hbc : dist b c < 1 / (Fintype.card V + 1 : ℝ)) :
    Star L a c := by
  apply hc a
  intro he
  have hd := lt_of_le_of_lt (dist_le_pi_dist (b : V → ℝ) (c : V → ℝ) a) hbc
  rw [he, Real.dist_eq,sub_zero,abs_of_nonneg ((point_simplex b).1 a)] at hd
  exact (not_lt_of_ge ha.le) hd

theorem chartTransport_dist (a : V) (b c : TrianglePoint V) :
    dist (chartTransport h q a b c) 1 = dist (gauge h q a b) (gauge h q a c) :=
  unitary_dist_inv_mul_one _ _

theorem transport_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c : TrianglePoint V, dist b c < δ → dist (transport h q b c) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := gauges_uniform h q hq hε
  exact ⟨δ,hδ,fun b c hbc => (chartTransport_dist h q _ b c).symm ▸ H b c hbc (root b)⟩

/-- Two compatible pieces, rather than a chosen homotopy class of paths, suffice. -/
def edgeTransport (b c d : TrianglePoint V) : SU2 := transport h q b c * transport h q c d

theorem edgeTransport_chart (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c d : TrianglePoint V} (hbc : Compatible L b c) (hcd : Compatible L c d)
    {a : V} (hab : Star L a b) (hac : Star L a c) (had : Star L a d) :
    edgeTransport h q b c d = chartTransport h q a b d := by
  rw [edgeTransport,transport_chart L h q hf hq hbc hab hac,
    transport_chart L h q hf hq hcd hac had,chartTransport_trans]

theorem edgeTransport_reverse (hf : FlatConnection L h) (hq : GeneralPosition h q)
    {b c d : TrianglePoint V} (hbc : Compatible L b c) (hcd : Compatible L c d) :
    edgeTransport h q d c b = (edgeTransport h q b c d)⁻¹ := by
  rw [edgeTransport,edgeTransport,transport_reverse L h q hf hq hbc,
    transport_reverse L h q hf hq hcd,mul_inv_rev]

theorem edgeTransport_uniform (hq : GeneralPosition h q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b c d : TrianglePoint V, dist b c < δ → dist c d < δ →
      dist (edgeTransport h q b c d) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := transport_uniform h q hq (show 0 < ε/2 by positivity)
  refine ⟨δ,hδ,?_⟩
  intro b c d hbc hcd
  apply lt_of_le_of_lt (unitary_dist_mul_one_le _ _)
  have h₁ := H b c hbc
  have h₂ := H c d hcd
  linarith

/-- All three edge images in one chart have exactly trivial triangle holonomy. -/
theorem edgeTransport_triangle (hf : FlatConnection L h) (hq : GeneralPosition h q)
    (b c d u v w : TrianglePoint V) {a : V}
    (hbu : Compatible L b u) (huc : Compatible L u c)
    (hcv : Compatible L c v) (hvd : Compatible L v d)
    (hdw : Compatible L d w) (hwb : Compatible L w b)
    (hab : Star L a b) (hac : Star L a c) (had : Star L a d)
    (hau : Star L a u) (hav : Star L a v) (haw : Star L a w) :
    edgeTransport h q b u c * edgeTransport h q c v d * edgeTransport h q d w b = 1 := by
  rw [edgeTransport_chart L h q hf hq hbu huc hab hau hac,
    edgeTransport_chart L h q hf hq hcv hvd hac hav had,
    edgeTransport_chart L h q hf hq hdw hwb had haw hab]
  unfold chartTransport
  group

/-- A uniform local chart for any finite or infinite family of nearby clique points. -/
theorem nearby_family_chart {I : Type*} (b : TrianglePoint V) (c : I → TrianglePoint V)
    (hc : ∀ i, CliquePoint L (c i))
    (hbc : ∀ i, dist b (c i) < 1 / (Fintype.card V + 1 : ℝ)) :
    ∃ a, ∀ i, Star L a (c i) := by
  obtain ⟨a,ha⟩ := exists_large_coordinate b
  exact ⟨a,fun i => nearby_star L ha (hc i) (hbc i)⟩

end Connection

end AffineTransport




end EilenbergGanea

end

end OAI

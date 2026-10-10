import OAI.RingTheory.BassTrace.CentralizerGeometry

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

noncomputable section

namespace BassTrace.FreeParameter

open Set MeasureTheory

open scoped Pointwise

universe u v

variable {H : Type u} [Group H] (S : Subgroup H)

noncomputable def residue (t : H) : S :=
  ⟨(Quotient.out (QuotientGroup.mk t : H ⧸ S))⁻¹ * t,
    QuotientGroup.leftRel_apply.mp
      (@Quotient.exact' _ (QuotientGroup.leftRel S) _ _ (Quotient.out_eq' _))⟩

lemma residue_out (q : H ⧸ S) : residue S q.out = 1 := by
  apply Subtype.ext
  simp [residue]

lemma residue_mul (t : H) (s : S) : residue S (t * s) = residue S t * s := by
  apply Subtype.ext
  simp [residue, QuotientGroup.mk_mul_of_mem _ s.property, mul_assoc]

lemma out_mul_residue (t : H) :
    (Quotient.out (QuotientGroup.mk t : H ⧸ S)) * residue S t = t := by
  simp [residue]

variable {C : Type v} [Group C] (χ : S →* C)

abbrev Offsets := (H ⧸ S) → C

noncomputable def encode (ω : Offsets S (C := C)) (t : H) : C :=
  ω (QuotientGroup.mk t) * χ (residue S t)

lemma encode_out (ω : Offsets S (C := C)) (q : H ⧸ S) :
    encode S χ ω q.out = ω q := by
  simp [encode, residue_out]

lemma encode_mul (ω : Offsets S (C := C)) (t : H) (s : S) :
    encode S χ ω (t * s) = encode S χ ω t * χ s := by
  simp [encode, QuotientGroup.mk_mul_of_mem _ s.property, residue_mul, mul_assoc]

lemma encode_injective : Function.Injective (encode S χ) := by
  intro ω η h
  funext q
  simpa only [encode_out] using congrFun h q.out

noncomputable def shift (h : H) (ω : Offsets S (C := C)) : Offsets S (C := C) :=
  fun q => encode S χ ω (h⁻¹ * q.out)

lemma encode_shift (h : H) (ω : Offsets S (C := C)) (t : H) :
    encode S χ (shift S χ h ω) t = encode S χ ω (h⁻¹ * t) := by
  change encode S χ ω (h⁻¹ * (QuotientGroup.mk t : H ⧸ S).out) *
    χ (residue S t) = _
  rw [← encode_mul, mul_assoc, out_mul_residue]

lemma shift_one (ω : Offsets S (C := C)) : shift S χ 1 ω = ω := by
  apply encode_injective S χ
  funext t
  simp [encode_shift]

lemma shift_mul (h k : H) (ω : Offsets S (C := C)) :
    shift S χ (h * k) ω = shift S χ h (shift S χ k ω) := by
  apply encode_injective S χ
  funext t
  simp [encode_shift, mul_assoc]

lemma shift_not_fixed (a : S) (ha : χ a ≠ 1) (ω : Offsets S (C := C)) :
    shift S χ (a : H) ω ≠ ω := by
  intro h
  have he := congrArg (fun η => encode S χ η (a : H)) h
  rw [encode_shift, inv_mul_cancel] at he
  have hm := encode_mul S χ ω 1 a
  simp only [one_mul] at hm
  rw [hm] at he
  exact ha ((mul_left_cancel (a := encode S χ ω 1)) (by simpa using he.symm))

lemma continuous_shift [TopologicalSpace C] [ContinuousMul C] (h : H) :
    Continuous (shift S χ h) := by
  apply continuous_pi
  intro q
  exact (continuous_apply _).mul continuous_const

lemma measurable_shift [MeasurableSpace C] [MeasurableMul₂ C] (h : H) :
    Measurable (shift S χ h) := by
  apply Measurable.of_eval
  intro q
  exact (measurable_pi_apply _).mul measurable_const

section Probability

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

noncomputable def uniform : Measure C := (PMF.uniformOfFintype C).toMeasure

instance uniform_probability : IsProbabilityMeasure (uniform (C := C)) := by
  unfold uniform
  infer_instance

lemma uniform_map_equiv (e : C ≃ C) :
    (uniform (C := C)).map e = uniform := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton c)]
  have he : e ⁻¹' {c} = {e.symm c} := by
    ext x
    exact e.eq_symm_apply.symm
  rw [he]
  change (PMF.uniformOfFintype C).toMeasure {e.symm c} =
    (PMF.uniformOfFintype C).toMeasure {c}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

noncomputable def offsetMeasure : Measure (Offsets S (C := C)) :=
  Measure.infinitePi (fun _ : H ⧸ S => uniform (C := C))

instance offsetMeasure_probability : IsProbabilityMeasure (offsetMeasure S (C := C)) := by
  unfold offsetMeasure
  infer_instance

omit [MeasurableSingletonClass C] in
lemma reindex_measure (h : H) :
    (offsetMeasure S (C := C)).map (fun ω q => ω (h⁻¹ • q)) = offsetMeasure S := by
  have hr := Measure.infinitePi_map_piCongrLeft
    (fun _ : H ⧸ S => uniform (C := C)) (MulAction.toPerm (β := H ⧸ S) h)
  unfold offsetMeasure
  rw [← hr]
  congr 1
  funext ω q
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

lemma offsetMeasure_shift (h : H) :
    (offsetMeasure S (C := C)).map (shift S χ h) = offsetMeasure S := by
  let m : (H ⧸ S) → C := fun q => χ (residue S (h⁻¹ * q.out))
  have hm : ∀ q, Measurable (fun c : C => c * m q) :=
    fun _ => measurable_of_finite _
  have hp : (offsetMeasure S (C := C)).map (fun ω q => ω q * m q) =
      offsetMeasure S := by
    rw [offsetMeasure, Measure.infinitePi_map_pi _ hm]
    congr 1
    funext q
    exact uniform_map_equiv (Equiv.mulRight (m q))
  have hf : shift S χ h = (fun ω q => ω q * m q) ∘
      (fun ω q => ω (h⁻¹ • q)) := by
    funext ω q
    change ω (QuotientGroup.mk (h⁻¹ * q.out)) * _ = ω (h⁻¹ • q) * _
    rw [show (QuotientGroup.mk (h⁻¹ * q.out) : H ⧸ S) = h⁻¹ • q from
      MulAction.Quotient.mk_smul_out S h⁻¹ q]
  have hm' : Measurable (fun ω : Offsets S (C := C) => fun q => ω q * m q) :=
    Measurable.of_eval (fun q => (hm q).comp (measurable_pi_apply q))
  have hr' : Measurable (fun ω : Offsets S (C := C) => fun q => ω (h⁻¹ • q)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [hf, ← Measure.map_map hm' hr', reindex_measure, hp]

end Probability

structure Character (a : H) where
  Color : Type u
  [group : Group Color]
  [finite : Finite Color]
  value : Subgroup.zpowers a →* Color
  detects : value ⟨a, Subgroup.mem_zpowers a⟩ ≠ 1

attribute [instance] Character.group Character.finite

lemma zpowers_subtype_generator (a : H) :
    Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.property
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨j, ?_⟩
  apply Subtype.ext
  exact hj

noncomputable def character (a : H) (ha : a ≠ 1) : Character a := by
  classical
  by_cases hf : IsOfFinOrder a
  · letI : Finite (Subgroup.zpowers a) := hf.finite_zpowers
    exact { Color := Subgroup.zpowers a
            group := inferInstance
            finite := inferInstance
            value := MonoidHom.id _
            detects := fun h => ha (congrArg Subtype.val h) }
  · letI : Infinite (Subgroup.zpowers a) := infinite_zpowers.mpr hf
    let e := intEquivOfZPowersEqTop
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (zpowers_subtype_generator a)
    let f : Subgroup.zpowers a →* ULift.{u} (Multiplicative (ZMod 2)) :=
      MulEquiv.ulift.symm.toMonoidHom.comp
        ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp e.symm.toMonoidHom)
    refine { Color := ULift.{u} (Multiplicative (ZMod 2))
             group := inferInstance
             finite := inferInstance
             value := f
             detects := ?_ }
    intro he
    have he' := congrArg (fun z : ULift (Multiplicative (ZMod 2)) => z.down.toAdd) he
    have hx : e.symm ⟨a, Subgroup.mem_zpowers a⟩ = Multiplicative.ofAdd 1 :=
      intEquivOfZPowersEqTop_symm_self (zpowers_subtype_generator a)
    norm_num [f, hx] at he'
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) he'

namespace Character

variable {a : H} (F : Character a)

instance colorTopology : TopologicalSpace F.Color := ⊥

instance colorDiscrete : DiscreteTopology F.Color := ⟨rfl⟩

instance colorMeasurable : MeasurableSpace F.Color := ⊤

instance colorSingleton : MeasurableSingletonClass F.Color := ⟨fun _ => trivial⟩

instance colorBorel : BorelSpace F.Color := ⟨borel_eq_top_of_discrete.symm⟩

noncomputable instance colorFintype : Fintype F.Color := Fintype.ofFinite _

end Character

variable (H)

abbrev Space := (a : {a : H // a ≠ 1}) →
  Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)

instance spaceTopology : TopologicalSpace (Space H) :=
  inferInstanceAs (TopologicalSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceMeasurable : MeasurableSpace (Space H) :=
  inferInstanceAs (MeasurableSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceCompact : CompactSpace (Space H) :=
  inferInstanceAs (CompactSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceT2 : T2Space (Space H) :=
  inferInstanceAs (T2Space ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceTotallyDisconnected : TotallyDisconnectedSpace (Space H) :=
  inferInstanceAs (TotallyDisconnectedSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance quotientCountable [Countable H] (S : Subgroup H) : Countable (H ⧸ S) :=
  (QuotientGroup.mk_surjective (s := S)).countable

instance spaceMetrizable [Countable H] : TopologicalSpace.MetrizableSpace (Space H) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

instance spaceBorel [Countable H] : BorelSpace (Space H) :=
  inferInstanceAs (BorelSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))

noncomputable instance spaceAction : MulAction H (Space H) where
  smul h ω a := shift _ (character a.val a.property).value h (ω a)
  one_smul ω := funext fun a => shift_one _ _ (ω a)
  mul_smul h k ω := funext fun a => shift_mul _ _ h k (ω a)

instance spaceContinuous : ContinuousConstSMul H (Space H) where
  continuous_const_smul h := by
    apply continuous_pi
    intro a
    exact (continuous_shift _ _ h).comp (continuous_apply a)

instance spaceFree : IsCancelSMul H (Space H) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro h ω he
  by_contra hn
  let a : {a : H // a ≠ 1} := ⟨h, hn⟩
  exact shift_not_fixed _ (character h hn).value
    ⟨h, Subgroup.mem_zpowers h⟩ (character h hn).detects (ω a) (congrFun he a)

noncomputable def probability : Measure (Space H) :=
  Measure.infinitePi (fun a : {a : H // a ≠ 1} =>
    offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color))

instance probability_isProbability : IsProbabilityMeasure (probability H) := by
  have : ∀ a : {a : H // a ≠ 1}, IsProbabilityMeasure
      (offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)) :=
    fun a => offsetMeasure_probability _
  unfold probability
  infer_instance

lemma probability_preserving (h : H) :
    MeasurePreserving (fun ω : Space H => h • ω) (probability H) (probability H) := by
  have hm : ∀ a : {a : H // a ≠ 1},
      Measurable (shift (Subgroup.zpowers a.val) (character a.val a.property).value h) :=
    fun a => measurable_shift _ _ h
  refine ⟨Measurable.of_eval (fun a => (hm a).comp (measurable_pi_apply a)), ?_⟩
  change Measure.map (fun (ω : Space H) (a : {a : H // a ≠ 1}) =>
    shift _ (character a.val a.property).value h (ω a)) _ = _
  rw [probability, Measure.infinitePi_map_pi _ hm]
  congr 1
  funext a
  exact offsetMeasure_shift _ _ h

end BassTrace.FreeParameter

end

end OAI

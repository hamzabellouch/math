import Mathlib

namespace OAI

/-! Sequential ray telescopes, finite-stage representatives and path connectedness. -/

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology

namespace NearbyLagrangian.RayTelescope
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (φ : ∀ m n, m ≤ n → C(X m,X n))

abbrev Raw := Σ n, X n × {t : ℝ // (n:ℝ) ≤ t}

inductive Glue : Raw X → Raw X → Prop
  | step (n m : ℕ) (h : n ≤ m) (x : X n) (t : ℝ) (ht : (m:ℝ) ≤ t) :
      Glue ⟨n,(x,⟨t,(by exact le_trans (by exact_mod_cast h) ht)⟩)⟩
        ⟨m,(φ n m h x,⟨t,ht⟩)⟩

abbrev Space := Quot (Glue X φ)

def rawHeight : C(Raw X,ℝ) :=
  ⟨fun a => a.2.2,continuous_sigma (fun _ => continuous_subtype_val.comp continuous_snd)⟩

def height : C(Space X φ,ℝ) :=
  ⟨Quot.lift (rawHeight X) (by intro a b h; cases h; rfl),
   continuous_quot_lift _ (rawHeight X).continuous⟩

@[simp] theorem height_quot (a : Raw X) : height X φ (Quot.mk _ a) = a.2.2 := rfl

def bottomTime (n : ℕ) : {t : ℝ // (n:ℝ) ≤ t} := ⟨(n:ℝ),by exact le_rfl⟩

def stage (n : ℕ) : C(X n,Space X φ) :=
  ⟨fun x => Quot.mk _ ⟨n,(x,bottomTime n)⟩,by
    exact continuous_quot_mk.comp (continuous_sigmaMk.comp
      (continuous_id.prodMk (continuous_const :
        Continuous (fun _ : X n => bottomTime n))))⟩

@[simp] theorem height_stage (n : ℕ) (x : X n) : height X φ (stage X φ n x) = n := rfl

variable [∀ n, Nonempty (X n)]
variable [DirectedSystem X (fun {m n} h => (φ m n h : _ → _))]

def rawCollapse (N : ℕ) : C(Raw X,X N) where
  toFun a := if h : a.1 ≤ N then φ a.1 N h a.2.1 else Classical.choice inferInstance
  continuous_toFun := continuous_sigma (fun n => by
    by_cases h : n ≤ N
    · simpa only [dite_eq_left h,Function.comp_def] using (φ n N h).continuous.comp continuous_fst
    · simpa only [dite_eq_right h] using
        (continuous_const : Continuous (fun _ : X n × {t : ℝ // (n:ℝ) ≤ t} => (Classical.choice inferInstance : X N))))

omit [∀ n, Nonempty (X n)] in
lemma stage_le_of_height_lt {N : ℕ} (a : Raw X) (h : rawHeight X a < (N:ℝ)+1) : a.1 ≤ N := by
  have h' : (a.1:ℝ) < (N:ℝ)+1 := lt_of_le_of_lt a.2.2.2 h
  have : a.1 < N+1 := by exact_mod_cast h'
  omega

lemma collapse_compatible {N : ℕ} {a b : Raw X}
    (h : Quot.mk (Glue X φ) a = Quot.mk (Glue X φ) b)
    (ha : rawHeight X a < (N:ℝ)+1) : rawCollapse X φ N a = rawCollapse X φ N b := by
  have hrel := Quot.eqvGen_exact h
  have aux : ∀ a b, Relation.EqvGen (Glue X φ) a b →
      rawHeight X a = rawHeight X b ∧
      (rawHeight X a < (N:ℝ)+1 → rawCollapse X φ N a = rawCollapse X φ N b) := by
    intro a b h
    induction h with
    | rel a b hab =>
      cases hab with
      | step n m h x t ht =>
        refine ⟨rfl,fun hz => ?_⟩
        have hm : m ≤ N := stage_le_of_height_lt X ⟨m,(φ n m h x,⟨t,ht⟩)⟩ hz
        have hn := h.trans hm
        simp only [rawCollapse,ContinuousMap.coe_mk,dite_eq_left hn,dite_eq_left hm]
        exact (DirectedSystem.map_map (f:=fun {m n} h => (φ m n h : _ → _)) h hm x).symm
    | refl a => exact ⟨rfl,fun _ => rfl⟩
    | symm a b hab ih => exact ⟨ih.1.symm,fun hb => (ih.2 (ih.1.symm ▸ hb)).symm⟩
    | trans a b c hab hbc ihab ihbc =>
      exact ⟨ihab.1.trans ihbc.1,fun ha => (ihab.2 ha).trans (ihbc.2 (ihab.1 ▸ ha))⟩
  exact (aux a b hrel).2 ha

abbrev Trunc (N : ℕ) := {z : Space X φ // height X φ z < (N:ℝ)+1}

def representative (z : Space X φ) : Raw X := (Quot.mk_surjective z).choose

omit [∀ n, Nonempty (X n)] [DirectedSystem X (fun {m n} h => (φ m n h : _ → _))] in
@[simp] theorem representative_mk (z : Space X φ) :
    Quot.mk (Glue X φ) (representative X φ z) = z := (Quot.mk_surjective z).choose_spec

def retract (N : ℕ) : C(Trunc X φ N,X N) where
  toFun z := rawCollapse X φ N (representative X φ z.1)
  continuous_toFun := by
    let s := {z : Space X φ | height X φ z < (N:ℝ)+1}
    have hs : IsOpen s := isOpen_lt (height X φ).continuous continuous_const
    have hq := (isQuotientMap_quot_mk (r:=Glue X φ)).restrictPreimage_isOpen hs
    apply hq.continuous_iff.mpr
    change Continuous (fun a : {a : Raw X // Quot.mk (Glue X φ) a ∈ s} =>
      rawCollapse X φ N (representative X φ (Quot.mk _ a.1)))
    have hf : (fun a : {a : Raw X // Quot.mk (Glue X φ) a ∈ s} =>
      rawCollapse X φ N (representative X φ (Quot.mk _ a.1))) =
        fun a => rawCollapse X φ N a.1 := by
      funext a
      apply collapse_compatible X φ
      · exact representative_mk X φ _
      · change height X φ (Quot.mk _ (representative X φ (Quot.mk _ a.1))) < _
        rw [representative_mk]
        exact a.2
    rw [hf]
    exact (rawCollapse X φ N).continuous.comp continuous_subtype_val

@[simp] theorem retract_quot (N : ℕ) (a : Raw X)
    (ha : rawHeight X a < (N:ℝ)+1) :
    retract X φ N ⟨Quot.mk _ a,ha⟩ = rawCollapse X φ N a := by
  apply collapse_compatible X φ
  · exact representative_mk X φ _
  · change height X φ (Quot.mk _ (representative X φ (Quot.mk _ a))) < _
    rw [representative_mk]
    exact ha

@[simp] theorem retract_stage (N n : ℕ) (h : n ≤ N) (x : X n)
    (hx : height X φ (stage X φ n x) < (N:ℝ)+1) :
    retract X φ N ⟨stage X φ n x,hx⟩ = φ n N h x := by
  calc
    retract X φ N ⟨stage X φ n x,hx⟩ = rawCollapse X φ N ⟨n,(x,bottomTime n)⟩ :=
      retract_quot X φ N ⟨n,(x,bottomTime n)⟩ hx
    _ = φ n N h x := by simp only [rawCollapse,ContinuousMap.coe_mk,dite_eq_left h]

end NearbyLagrangian.RayTelescope

end

noncomputable section
universe u v w


namespace NearbyLagrangian.RayTelescope
open Set ContinuousMap
open scoped Topology
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (φ : ∀ m n, m ≤ n → C(X m,X n))

def raiseTime (N : ℕ) (s : unitInterval) (t : ℝ) : ℝ := t + s * (max t N-t)

lemma le_raiseTime (N : ℕ) (s : unitInterval) (t : ℝ) : t ≤ raiseTime N s t := by
  unfold raiseTime
  exact le_add_of_nonneg_right (mul_nonneg s.2.1 (sub_nonneg.mpr (le_max_left _ _)))

@[simp] theorem raiseTime_zero (N : ℕ) (t : ℝ) : raiseTime N 0 t = t := by simp [raiseTime]
@[simp] theorem raiseTime_one (N : ℕ) (t : ℝ) : raiseTime N 1 t = max t N := by simp [raiseTime]

def cylinderRaise (N n : ℕ) : C((X n × {t : ℝ // (n:ℝ) ≤ t}) × unitInterval,Space X φ) where
  toFun z := Quot.mk _ ⟨n,(z.1.1,⟨raiseTime N z.2 z.1.2,
    z.1.2.2.trans (le_raiseTime _ _ _)⟩)⟩
  continuous_toFun := by
    have ht : Continuous (fun z : (X n × {t : ℝ // (n:ℝ) ≤ t}) × unitInterval => raiseTime N z.2 z.1.2) := by
      unfold raiseTime
      fun_prop
    exact continuous_quot_mk.comp (continuous_sigmaMk.comp
      (continuous_fst.fst.prodMk (ht.subtype_mk _)))

def rawRaise (N : ℕ) : C(Raw X,C(unitInterval,Space X φ)) :=
  ⟨fun a => (cylinderRaise X φ N a.1).curry a.2,
   continuous_sigma (fun _ => (cylinderRaise X φ N _).curry.continuous)⟩

def raiseFamily (N : ℕ) : C(Space X φ,C(unitInterval,Space X φ)) :=
  ⟨Quot.lift (rawRaise X φ N) (by
    intro a b h
    ext s
    cases h with
    | step n m h x t ht =>
      exact Quot.sound (Glue.step n m h x (raiseTime N s t) (ht.trans (le_raiseTime _ _ _)))),
   continuous_quot_lift _ (rawRaise X φ N).continuous⟩

@[simp] theorem raiseFamily_apply (N : ℕ) (a : Raw X) (s : unitInterval) :
    raiseFamily X φ N (Quot.mk _ a) s = Quot.mk _
      ⟨a.1,(a.2.1,⟨raiseTime N s a.2.2,a.2.2.2.trans (le_raiseTime _ _ _)⟩)⟩ := rfl

def raised (N : ℕ) : C(Space X φ,Space X φ) :=
  ⟨fun z => raiseFamily X φ N z 1,(continuous_eval_const (1:unitInterval)).comp
    (raiseFamily X φ N).continuous⟩

def raiseHomotopy (N : ℕ) : (ContinuousMap.id (Space X φ)).Homotopy (raised X φ N) where
  toFun z := raiseFamily X φ N z.2 z.1
  continuous_toFun := (raiseFamily X φ N).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    induction z using Quot.inductionOn with
    | h a =>
      change Quot.mk _ ⟨a.1,(a.2.1,⟨raiseTime N 0 a.2.2,_⟩)⟩ = Quot.mk _ a
      exact congrArg (fun t : {t : ℝ // (a.1:ℝ) ≤ t} => Quot.mk (Glue X φ) ⟨a.1,(a.2.1,t)⟩)
        (Subtype.ext (raiseTime_zero N a.2.2))
  map_one_left _ := rfl

@[simp] theorem height_raised (N : ℕ) (z : Space X φ) :
    height X φ (raised X φ N z) = max (height X φ z) N := by
  induction z using Quot.inductionOn with
  | h a => change raiseTime N 1 a.2.2 = max (a.2.2:ℝ) N; exact raiseTime_one _ _

variable [∀ n, Nonempty (X n)]
variable [DirectedSystem X (fun {m n} h => (φ m n h : _ → _))]

theorem raised_eq_stage_retract (N : ℕ) (z : Space X φ) (hz : height X φ z ≤ N) :
    raised X φ N z = stage X φ N
      (retract X φ N ⟨z,lt_of_le_of_lt hz (by linarith)⟩) := by
  induction z using Quot.inductionOn with
  | h a =>
    have hn : a.1 ≤ N := stage_le_of_height_lt X a (lt_of_le_of_lt hz (by linarith))
    have hr : retract X φ N ⟨Quot.mk _ a,lt_of_le_of_lt hz (by linarith)⟩ =
        rawCollapse X φ N a := retract_quot X φ N a _
    rw [hr]
    change Quot.mk (Glue X φ) ⟨a.1,(a.2.1,⟨raiseTime N 1 a.2.2,_⟩)⟩ =
      Quot.mk (Glue X φ) ⟨N,(rawCollapse X φ N a,⟨(N:ℝ),le_rfl⟩)⟩
    have hz' : (a.2.2:ℝ) ≤ N := hz
    simp only [raiseTime_one,max_eq_right hz',rawCollapse,ContinuousMap.coe_mk,dite_eq_left hn]
    exact Quot.sound (Glue.step a.1 N hn a.2.1 (N:ℝ) le_rfl)

end NearbyLagrangian.RayTelescope

end

noncomputable section
universe u v w


namespace NearbyLagrangian.RayTelescope
open Set ContinuousMap
open scoped Topology
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (φ : ∀ m n, m ≤ n → C(X m,X n))
variable {A : Type v} [TopologicalSpace A]

theorem exists_height_bound [CompactSpace A] (f : C(A,Space X φ)) :
    ∃ N : ℕ, ∀ a, height X φ (f a) ≤ N := by
  obtain ⟨r,hr⟩ := (isCompact_range ((height X φ).continuous.comp f.continuous)).bddAbove
  obtain ⟨N,hN⟩ := exists_nat_gt r
  exact ⟨N,fun a => le_of_lt ((hr ⟨a,rfl⟩).trans_lt hN)⟩

variable [∀ n, Nonempty (X n)]
variable [DirectedSystem X (fun {m n} h => (φ m n h : _ → _))]

def finiteMap (N : ℕ) (f : C(A,Space X φ)) (hf : ∀ a, height X φ (f a) < (N:ℝ)+1) : C(A,X N) :=
  (retract X φ N).comp ⟨fun a => ⟨f a,hf a⟩,f.continuous.subtype_mk _⟩

def finiteHomotopy (N : ℕ) (f : C(A,Space X φ)) (hf : ∀ a, height X φ (f a) ≤ N) :
    f.Homotopy ((stage X φ N).comp
      (finiteMap X φ N f (fun a => lt_of_le_of_lt (hf a) (by linarith)))) :=
  ((raiseHomotopy X φ N).compContinuousMap f).cast (by ext; rfl) (by
    ext a
    exact raised_eq_stage_retract X φ N (f a) (hf a))

theorem exists_finite_representative [CompactSpace A] (f : C(A,Space X φ)) :
    ∃ N : ℕ, ∃ g : C(A,X N), f.Homotopic ((stage X φ N).comp g) := by
  obtain ⟨N,hN⟩ := exists_height_bound X φ f
  exact ⟨N,finiteMap X φ N f (fun a => lt_of_le_of_lt (hN a) (by linarith)),
    ⟨finiteHomotopy X φ N f hN⟩⟩

@[simp] theorem finiteMap_stage (N m : ℕ) (h : m ≤ N) (f : C(A,X m))
    (hf : ∀ a, height X φ ((stage X φ m).comp f a) < (N:ℝ)+1) :
    finiteMap X φ N ((stage X φ m).comp f) hf = (φ m N h).comp f := by
  ext a
  exact retract_stage X φ N m h (f a) (hf a)

theorem stage_stabilize_homotopic (m N : ℕ) (h : m ≤ N) :
    (stage X φ m).Homotopic ((stage X φ N).comp (φ m N h)) := by
  have hh : ∀ x : X m, height X φ (stage X φ m x) ≤ N := by
    intro x
    change (m:ℝ) ≤ N
    exact_mod_cast h
  have H := finiteHomotopy X φ N (stage X φ m) hh
  refine ⟨H.cast rfl ?_⟩
  apply congrArg ((stage X φ N).comp)
  ext x
  exact retract_stage X φ N m h x _

def finiteStageHomotopy {m n N : ℕ} (hm : m ≤ N) (hn : n ≤ N)
    (f : C(A,X m)) (g : C(A,X n))
    (H : ((stage X φ m).comp f).Homotopy ((stage X φ n).comp g))
    (hH : ∀ z, height X φ (H z) < (N:ℝ)+1) :
    ((φ m N hm).comp f).Homotopy ((φ n N hn).comp g) where
  toFun z := retract X φ N ⟨H z,hH z⟩
  continuous_toFun := (retract X φ N).continuous.comp (H.continuous.subtype_mk _)
  map_zero_left a := by
    have ha : height X φ (stage X φ m (f a)) < (N:ℝ)+1 := by
      have := hH (0,a)
      simpa only [ContinuousMap.Homotopy.apply_zero,ContinuousMap.comp_apply] using this
    calc
      retract X φ N ⟨H (0,a),hH (0,a)⟩ = retract X φ N ⟨stage X φ m (f a),ha⟩ :=
        congrArg (retract X φ N) (Subtype.ext (H.map_zero_left a))
      _ = _ := retract_stage X φ N m hm (f a) ha
  map_one_left a := by
    have ha : height X φ (stage X φ n (g a)) < (N:ℝ)+1 := by
      have := hH (1,a)
      simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.comp_apply] using this
    calc
      retract X φ N ⟨H (1,a),hH (1,a)⟩ = retract X φ N ⟨stage X φ n (g a),ha⟩ :=
        congrArg (retract X φ N) (Subtype.ext (H.map_one_left a))
      _ = _ := retract_stage X φ N n hn (g a) ha

theorem stage_homotopic_iff [CompactSpace A] {m n : ℕ} (f : C(A,X m)) (g : C(A,X n)) :
    ((stage X φ m).comp f).Homotopic ((stage X φ n).comp g) ↔
      ∃ (N : ℕ) (hm : m ≤ N) (hn : n ≤ N), ((φ m N hm).comp f).Homotopic ((φ n N hn).comp g) := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨K,hK⟩ := exists_height_bound X φ H.toContinuousMap
    let N := max K (max m n)
    have hm : m ≤ N := (le_max_left m n).trans (le_max_right _ _)
    have hn : n ≤ N := (le_max_right m n).trans (le_max_right _ _)
    have hKN : (K:ℝ) ≤ N := by exact_mod_cast (le_max_left K (max m n))
    refine ⟨N,hm,hn,⟨finiteStageHomotopy X φ hm hn f g H ?_⟩⟩
    intro z
    exact lt_of_le_of_lt ((hK z).trans hKN) (by linarith)
  · rintro ⟨N,hm,hn,h⟩
    exact (((stage_stabilize_homotopic X φ m N hm).comp (ContinuousMap.Homotopic.refl f)).trans
      ((ContinuousMap.Homotopic.refl (stage X φ N)).comp h)).trans
      (((stage_stabilize_homotopic X φ n N hn).comp (ContinuousMap.Homotopic.refl g)).symm)

theorem stage_nullhomotopic_iff [CompactSpace A] {m : ℕ} (f : C(A,X m)) :
    ((stage X φ m).comp f).Nullhomotopic ↔
      ∃ (N : ℕ) (hm : m ≤ N), ((φ m N hm).comp f).Nullhomotopic := by
  constructor
  · rintro ⟨c,⟨H⟩⟩
    obtain ⟨K,hK⟩ := exists_height_bound X φ H.toContinuousMap
    obtain ⟨J,hJ⟩ := exists_nat_gt (height X φ c)
    let N := max K (max m J)
    have hm : m ≤ N := (le_max_left m J).trans (le_max_right _ _)
    have hKN : (K:ℝ) ≤ N := by exact_mod_cast (le_max_left K (max m J))
    have hJN : (J:ℝ) ≤ N := by exact_mod_cast ((le_max_right m J).trans (le_max_right K (max m J)))
    have hc : height X φ c < (N:ℝ)+1 := lt_of_lt_of_le hJ (by linarith)
    have hH : ∀ z, height X φ (H z) < (N:ℝ)+1 :=
      fun z => lt_of_le_of_lt ((hK z).trans hKN) (by linarith)
    refine ⟨N,hm,retract X φ N ⟨c,hc⟩,⟨{
      toFun := fun z => retract X φ N ⟨H z,hH z⟩
      continuous_toFun := (retract X φ N).continuous.comp (H.continuous.subtype_mk _)
      map_zero_left := ?_
      map_one_left := ?_ }⟩⟩
    · intro a
      have ha : height X φ (stage X φ m (f a)) < (N:ℝ)+1 := by
        simpa only [ContinuousMap.Homotopy.apply_zero,ContinuousMap.comp_apply] using hH (0,a)
      calc
        retract X φ N ⟨H (0,a),hH (0,a)⟩ = retract X φ N ⟨stage X φ m (f a),ha⟩ :=
          congrArg (retract X φ N) (Subtype.ext (H.map_zero_left a))
        _ = _ := retract_stage X φ N m hm (f a) ha
    · intro a
      exact congrArg (retract X φ N) (Subtype.ext (H.map_one_left a))
  · rintro ⟨N,hm,c,h⟩
    refine ⟨stage X φ N c,?_⟩
    exact ((stage_stabilize_homotopic X φ m N hm).comp (ContinuousMap.Homotopic.refl f)).trans
      ((ContinuousMap.Homotopic.refl (stage X φ N)).comp h)

end NearbyLagrangian.RayTelescope

end

noncomputable section
universe u v w


namespace NearbyLagrangian.RayTelescope
open ContinuousMap
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (φ : ∀ m n, m ≤ n → C(X m,X n))
variable [DirectedSystem X (fun {m n} h => (φ m n h : _ → _))]
variable [∀ n, PathConnectedSpace (X n)]

theorem joined_base (b : X 0) (z : Space X φ) : Joined z (stage X φ 0 b) := by
  obtain ⟨N,g,⟨H⟩⟩ := exists_finite_representative X φ (ContinuousMap.const Unit z)
  have h₁ : Joined z (stage X φ N (g ())) := ⟨H.evalAt ()⟩
  have h₂ : Joined (stage X φ N (g ())) (stage X φ N (φ 0 N (Nat.zero_le N) b)) :=
    (PathConnectedSpace.joined _ _).map (stage X φ N).continuous
  obtain ⟨K⟩ := stage_stabilize_homotopic X φ 0 N (Nat.zero_le N)
  exact (h₁.trans h₂).trans (Joined.symm ⟨K.evalAt b⟩)

instance pathConnected : PathConnectedSpace (Space X φ) where
  nonempty := ⟨stage X φ 0 (Classical.choice inferInstance)⟩
  joined z w := (joined_base X φ (Classical.choice inferInstance) z).trans
    (joined_base X φ (Classical.choice inferInstance) w).symm

end NearbyLagrangian.RayTelescope

end

end OAI

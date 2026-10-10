import Mathlib

namespace OAI

section TopologyDependencies
open CategoryTheory Opposite Simplicial
open scoped unitInterval

namespace HarmonicArtin
universe u

noncomputable def realizeSimplex (X : SSet.{u}) {n : SimplexCategory}
    (x : X.obj (op n)) : C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), |X|) :=
  TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.unit.app X).app (op n) x)

lemma realizeSimplex_natural (X : SSet.{u}) {n m : SimplexCategory}
    (f : n ⟶ m) (x : X.obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizeSimplex X (X.map f.op x) z =
      realizeSimplex X x (Convexity.StdSimplex.map f.toOrderHom z) := by
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app X).naturality f.op) x
  change (sSetTopAdj.unit.app X).app (op n) (X.map f.op x) =
    (TopCat.toSSet.obj |X|).map f.op ((sSetTopAdj.unit.app X).app (op m) x) at h
  unfold realizeSimplex
  rw [h]
  exact TopCat.toSSetObjEquiv_naturality_apply f _ z

def prependOrdinal {n m : SimplexCategory} (f : n ⟶ m) :
    ⦋n.len + 1⦌ ⟶ ⦋m.len + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.cons 0 (fun i => (f.toOrderHom i).succ)
    monotone' := by
      intro a b hab
      induction a using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ a =>
        induction b using Fin.cases with
        | zero => simp at hab
        | succ b =>
          exact Fin.succ_le_succ_iff.mpr
            (f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hab)) }

@[simp] lemma prependOrdinal_zero {n m : SimplexCategory} (f : n ⟶ m) :
    (prependOrdinal f).toOrderHom 0 = 0 := rfl
@[simp] lemma prependOrdinal_succ {n m : SimplexCategory} (f : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (prependOrdinal f).toOrderHom i.succ = (f.toOrderHom i).succ := rfl

noncomputable def coneSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)) × I, Convexity.StdSimplex ℝ (Fin (n + 2))) where
  toFun point := Convexity.convexCombPair point.2.val (1 - point.2.val)
    point.2.property.1 (sub_nonneg.mpr point.2.property.2) (add_sub_cancel _ _)
    (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.map Fin.succ point.1)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    refine continuous_pi (fun index => ?_)
    simp only [Function.comp_apply, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_subtype_val.comp continuous_snd).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        ((Convexity.StdSimplex.continuous_weights_apply ℝ index).comp
          ((Convexity.StdSimplex.continuous_map ℝ Fin.succ).comp continuous_fst)))

@[simp] lemma coneSimplex_zero (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    coneSimplex n (z, 0) = Convexity.StdSimplex.map Fin.succ z := by
  ext i
  simp [coneSimplex]

@[simp] lemma coneSimplex_one (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    coneSimplex n (z, 1) = Convexity.StdSimplex.single 0 := by
  ext i
  simp [coneSimplex]

lemma map_coneSimplex {n m : SimplexCategory} (f : n ⟶ m)
    (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    Convexity.StdSimplex.map (prependOrdinal f).toOrderHom (coneSimplex n.len (z, t)) =
      coneSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t) := by
  have hs : Convexity.StdSimplex.map (prependOrdinal f).toOrderHom (Convexity.StdSimplex.map Fin.succ z) =
      Convexity.StdSimplex.map Fin.succ (Convexity.StdSimplex.map f.toOrderHom z) := by
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    rfl
  dsimp only [coneSimplex, ContinuousMap.coe_mk]
  rw [(Convexity.StdSimplex.isAffineMap_map ℝ _).map_convexCombPair,
    Convexity.StdSimplex.map_single, hs]
  rfl

variable (P : Type u) [Preorder P] [OrderBot P]

def prependNerve {n : SimplexCategory} (x : (nerve P).obj (op n)) :
    (nerve P).obj (op ⦋n.len + 1⦌) :=
  x.precomp (homOfLE bot_le)

lemma prependNerve_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve P).obj (op m)) :
    prependNerve P ((nerve P).map f.op x) =
      (nerve P).map (prependOrdinal f).op (prependNerve P x) := by
  apply nerve.ext_of_isThin
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma prependNerve_face {n : SimplexCategory} (x : (nerve P).obj (op n)) :
    (nerve P).map (SimplexCategory.δ (0 : Fin (n.len + 2))).op (prependNerve P x) = x := by
  apply nerve.ext_of_isThin
  funext i
  rfl

noncomputable def nerveConeSimplex {n : SimplexCategory} (x : (nerve P).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), C(I, |nerve P|)) :=
  ((realizeSimplex (nerve P) (prependNerve P x)).comp (coneSimplex n.len)).curry

lemma nerveConeSimplex_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve P).obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    nerveConeSimplex P ((nerve P).map f.op x) z t =
      nerveConeSimplex P x (Convexity.StdSimplex.map f.toOrderHom z) t := by
  change realizeSimplex (nerve P) (prependNerve P ((nerve P).map f.op x))
      (coneSimplex n.len (z, t)) =
    realizeSimplex (nerve P) (prependNerve P x)
      (coneSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t))
  rw [prependNerve_natural, realizeSimplex_natural, map_coneSimplex]

@[simp] lemma nerveConeSimplex_zero {n : SimplexCategory}
    (x : (nerve P).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveConeSimplex P x z 0 = realizeSimplex (nerve P) x z := by
  change realizeSimplex (nerve P) (prependNerve P x) (coneSimplex n.len (z, 0)) = _
  rw [coneSimplex_zero]
  have h := realizeSimplex_natural (nerve P)
    (SimplexCategory.δ (0 : Fin (n.len + 2))) (prependNerve P x) z
  rw [prependNerve_face] at h
  exact h.symm

noncomputable def nerveBotPoint : |nerve P| :=
  realizeSimplex (nerve P) (ComposableArrows.mk₀ (⊥ : P)) (Convexity.StdSimplex.single 0)

@[simp] lemma nerveConeSimplex_one {n : SimplexCategory}
    (x : (nerve P).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveConeSimplex P x z 1 = nerveBotPoint P := by
  change realizeSimplex (nerve P) (prependNerve P x) (coneSimplex n.len (z, 1)) = _
  rw [coneSimplex_one]
  let f : ⦋0⦌ ⟶ ⦋n.len + 1⦌ := SimplexCategory.mkHom (OrderHom.const _ 0)
  have hf : (nerve P).map f.op (prependNerve P x) = ComposableArrows.mk₀ (⊥ : P) := by
    apply nerve.ext_of_isThin
    rfl
  have h := realizeSimplex_natural (nerve P) f (prependNerve P x) (Convexity.StdSimplex.single 0)
  rw [hf, Convexity.StdSimplex.map_single] at h
  exact h.symm

noncomputable def nerveConeMap :
    nerve P ⟶ TopCat.toSSet.obj (TopCat.of C(I, |nerve P|)) where
  app n := ↾fun x => (TopCat.toSSetObjEquiv _ n).symm (nerveConeSimplex P x)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (TopCat.toSSetObjEquiv _ m).injective
    ext z t
    exact nerveConeSimplex_natural P f.unop x z t

noncomputable def nerveCone : C(|nerve P|, C(I, |nerve P|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nerveConeMap P)).hom

noncomputable def pathEvaluate (t : I) : TopCat.of C(I, |nerve P|) ⟶ |nerve P| :=
  TopCat.ofHom ⟨fun f => f t, continuous_eval_const t⟩

lemma nerveCone_zero :
    (TopCat.ofHom (nerveCone P)) ≫ pathEvaluate P 0 = 𝟙 |nerve P| := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  exact nerveConeSimplex_zero P x z

lemma nerveCone_one :
    (TopCat.ofHom (nerveCone P)) ≫ pathEvaluate P 1 = TopCat.const (nerveBotPoint P) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  exact nerveConeSimplex_one P x z

theorem nerve_orderBot_contractible : ContractibleSpace |nerve P| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveBotPoint P, ⟨{
    toFun := fun p => nerveCone P p.2 p.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · exact (nerveCone P).uncurry.continuous.comp continuous_swap
  · intro x
    exact ConcreteCategory.congr_hom (nerveCone_zero P) x
  · intro x
    exact ConcreteCategory.congr_hom (nerveCone_one P) x

section TopCone
variable (Q : Type u) [Preorder Q] [OrderTop Q]

def appendOrdinal {n m : SimplexCategory} (f : n ⟶ m) :
    ⦋n.len + 1⦌ ⟶ ⦋m.len + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.snoc (fun i => (f.toOrderHom i).castSucc) (Fin.last (m.len + 1))
    monotone' := by
      intro a b hab
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Fin.le_last _
      | cast b =>
        induction a using Fin.lastCases with
        | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last b)) hab)
        | cast a =>
          simpa only [Fin.snoc_castSucc] using Fin.castSucc_le_castSucc_iff.mpr
            (f.toOrderHom.monotone (Fin.castSucc_le_castSucc_iff.mp hab)) }

@[simp] lemma appendOrdinal_last {n m : SimplexCategory} (f : n ⟶ m) :
    (appendOrdinal f).toOrderHom (Fin.last (n.len + 1)) = Fin.last (m.len + 1) := by
  change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Fin (m.len + 2))
    (fun j => (f.toOrderHom j).castSucc) (Fin.last (m.len + 1))) (Fin.last (n.len + 1)) = _
  exact Fin.snoc_last _ _
@[simp] lemma appendOrdinal_castSucc {n m : SimplexCategory} (f : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (appendOrdinal f).toOrderHom i.castSucc = (f.toOrderHom i).castSucc := by
  change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Fin (m.len + 2))
    (fun j => (f.toOrderHom j).castSucc) (Fin.last (m.len + 1))) i.castSucc = _
  exact Fin.snoc_castSucc _ _ _

noncomputable def topConeSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)) × I, Convexity.StdSimplex ℝ (Fin (n + 2))) where
  toFun point := Convexity.convexCombPair point.2.val (1 - point.2.val)
    point.2.property.1 (sub_nonneg.mpr point.2.property.2) (add_sub_cancel _ _)
    (Convexity.StdSimplex.single (Fin.last (n + 1)))
    (Convexity.StdSimplex.map Fin.castSucc point.1)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    refine continuous_pi (fun index => ?_)
    simp only [Function.comp_apply, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_subtype_val.comp continuous_snd).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        ((Convexity.StdSimplex.continuous_weights_apply ℝ index).comp
          ((Convexity.StdSimplex.continuous_map ℝ Fin.castSucc).comp continuous_fst)))

@[simp] lemma topConeSimplex_zero (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    topConeSimplex n (z, 0) = Convexity.StdSimplex.map Fin.castSucc z := by
  ext i
  simp [topConeSimplex]

@[simp] lemma topConeSimplex_one (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    topConeSimplex n (z, 1) = Convexity.StdSimplex.single (Fin.last (n + 1)) := by
  ext i
  simp [topConeSimplex]

lemma map_topConeSimplex {n m : SimplexCategory} (f : n ⟶ m)
    (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    Convexity.StdSimplex.map (appendOrdinal f).toOrderHom (topConeSimplex n.len (z, t)) =
      topConeSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t) := by
  have hs : Convexity.StdSimplex.map (appendOrdinal f).toOrderHom (Convexity.StdSimplex.map Fin.castSucc z) =
      Convexity.StdSimplex.map Fin.castSucc (Convexity.StdSimplex.map f.toOrderHom z) := by
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact appendOrdinal_castSucc f i
  dsimp only [topConeSimplex, ContinuousMap.coe_mk]
  rw [(Convexity.StdSimplex.isAffineMap_map ℝ _).map_convexCombPair,
    Convexity.StdSimplex.map_single, hs, appendOrdinal_last]

def appendNerve {n : SimplexCategory} (x : (nerve Q).obj (op n)) :
    (nerve Q).obj (op ⦋n.len + 1⦌) :=
  (show Monotone (Fin.snoc x.obj (⊤ : Q)) from by
    intro a b hab
    induction b using Fin.lastCases with
    | last => simp only [Fin.snoc_last, le_top]
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last b)) hab)
      | cast a =>
        simpa using (leOfHom (x.map (homOfLE (Fin.castSucc_le_castSucc_iff.mp hab))))).functor

lemma appendNerve_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve Q).obj (op m)) :
    appendNerve Q ((nerve Q).map f.op x) =
      (nerve Q).map (appendOrdinal f).op (appendNerve Q x) := by
  apply nerve.ext_of_isThin
  funext i
  induction i using Fin.lastCases with
  | last =>
    change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) _ ⊤) (Fin.last _) =
      (Fin.snoc (α := fun _ : Fin (m.len + 2) => Q) x.obj ⊤)
        ((appendOrdinal f).toOrderHom (Fin.last _))
    simp only [appendOrdinal_last, Fin.snoc_last]
  | cast i =>
    change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) _ ⊤) i.castSucc =
      (Fin.snoc (α := fun _ : Fin (m.len + 2) => Q) x.obj ⊤)
        ((appendOrdinal f).toOrderHom i.castSucc)
    simp only [appendOrdinal_castSucc, Fin.snoc_castSucc]
    rfl

lemma appendNerve_face {n : SimplexCategory} (x : (nerve Q).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (Fin.last (n.len + 1))).op (appendNerve Q x) = x := by
  apply nerve.ext_of_isThin
  funext i
  change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) x.obj ⊤)
    ((Fin.last (n.len + 1)).succAbove i) = x.obj i
  simp only [Fin.succAbove_last, Fin.snoc_castSucc]

noncomputable def nerveTopConeSimplex {n : SimplexCategory} (x : (nerve Q).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), C(I, |nerve Q|)) :=
  ((realizeSimplex (nerve Q) (appendNerve Q x)).comp (topConeSimplex n.len)).curry

lemma nerveTopConeSimplex_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (nerve Q).obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) (t : I) :
    nerveTopConeSimplex Q ((nerve Q).map f.op x) z t =
      nerveTopConeSimplex Q x (Convexity.StdSimplex.map f.toOrderHom z) t := by
  change realizeSimplex (nerve Q) (appendNerve Q ((nerve Q).map f.op x))
      (topConeSimplex n.len (z, t)) =
    realizeSimplex (nerve Q) (appendNerve Q x)
      (topConeSimplex m.len (Convexity.StdSimplex.map f.toOrderHom z, t))
  rw [appendNerve_natural, realizeSimplex_natural, map_topConeSimplex]

@[simp] lemma nerveTopConeSimplex_zero {n : SimplexCategory}
    (x : (nerve Q).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveTopConeSimplex Q x z 0 = realizeSimplex (nerve Q) x z := by
  change realizeSimplex (nerve Q) (appendNerve Q x) (topConeSimplex n.len (z, 0)) = _
  rw [topConeSimplex_zero]
  have h := realizeSimplex_natural (nerve Q)
    (SimplexCategory.δ (Fin.last (n.len + 1))) (appendNerve Q x) z
  rw [appendNerve_face] at h
  change realizeSimplex (nerve Q) x z =
    realizeSimplex (nerve Q) (appendNerve Q x)
      (Convexity.StdSimplex.map (Fin.last (n.len + 1)).succAbove z) at h
  rw [Fin.succAbove_last] at h
  exact h.symm

noncomputable def nerveTopPoint : |nerve Q| :=
  realizeSimplex (nerve Q) (ComposableArrows.mk₀ (⊤ : Q)) (Convexity.StdSimplex.single 0)

@[simp] lemma nerveTopConeSimplex_one {n : SimplexCategory}
    (x : (nerve Q).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveTopConeSimplex Q x z 1 = nerveTopPoint Q := by
  change realizeSimplex (nerve Q) (appendNerve Q x) (topConeSimplex n.len (z, 1)) = _
  rw [topConeSimplex_one]
  let f : ⦋0⦌ ⟶ ⦋n.len + 1⦌ := SimplexCategory.mkHom (OrderHom.const _ (Fin.last (n.len + 1)))
  have hf : (nerve Q).map f.op (appendNerve Q x) = ComposableArrows.mk₀ (⊤ : Q) := by
    apply nerve.ext_of_isThin
    funext i
    change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) x.obj ⊤)
      (Fin.last (n.len + 1)) = ⊤
    exact Fin.snoc_last _ _
  have h := realizeSimplex_natural (nerve Q) f (appendNerve Q x) (Convexity.StdSimplex.single 0)
  rw [hf, Convexity.StdSimplex.map_single] at h
  exact h.symm

noncomputable def nerveTopConeMap :
    nerve Q ⟶ TopCat.toSSet.obj (TopCat.of C(I, |nerve Q|)) where
  app n := ↾fun x => (TopCat.toSSetObjEquiv _ n).symm (nerveTopConeSimplex Q x)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (TopCat.toSSetObjEquiv _ m).injective
    ext z t
    exact nerveTopConeSimplex_natural Q f.unop x z t

noncomputable def nerveTopCone : C(|nerve Q|, C(I, |nerve Q|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nerveTopConeMap Q)).hom

lemma nerveTopCone_zero :
    (TopCat.ofHom (nerveTopCone Q)) ≫ pathEvaluate Q 0 = 𝟙 |nerve Q| := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveTopCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  exact nerveTopConeSimplex_zero Q x z

lemma nerveTopCone_one :
    (TopCat.ofHom (nerveTopCone Q)) ≫ pathEvaluate Q 1 = TopCat.const (nerveTopPoint Q) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nerveTopCone, TopCat.ofHom_hom, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (TopCat.toSSetObjEquiv _ n).injective
  ext z
  exact nerveTopConeSimplex_one Q x z

theorem nerve_orderTop_contractible : ContractibleSpace |nerve Q| := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨nerveTopPoint Q, ⟨{
    toFun := fun p => nerveTopCone Q p.2 p.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · exact (nerveTopCone Q).uncurry.continuous.comp continuous_swap
  · intro x
    exact ConcreteCategory.congr_hom (nerveTopCone_zero Q) x
  · intro x
    exact ConcreteCategory.congr_hom (nerveTopCone_one Q) x

end TopCone
end HarmonicArtin

end TopologyDependencies

end OAI

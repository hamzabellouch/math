import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.CellCuts

namespace OAI

/-! ## CellUnion -/

/-! Directed unions of conservative submonoids and of their presentation
pushouts. Every union here is inside the original terminal monoid. -/
namespace PartitionConsistency.ConservativeMonoids.Subobject
universe u v
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical
variable {T : Object.{u}}

/-- Directed unions do not add factors or conditional joins. -/
def directedSup {K : Type u} [Nonempty K] (F : K → Subobject T)
    (hF : Directed (· ≤ ·) (fun k => (F k).submonoid)) : Subobject T where
  submonoid := ⨆ k, (F k).submonoid
  factors := by
    intro x hx y hy
    obtain ⟨i,hi⟩ := (Submonoid.mem_iSup_of_directed hF).mp hx
    obtain ⟨j,hj⟩ := (Submonoid.mem_iSup_of_directed hF).mp hy
    obtain ⟨k,hik,hjk⟩ := hF i j
    exact (le_iSup (fun k => (F k).submonoid) k) ((F k).factors x (hik hi) y (hjk hj))
  joins := by
    intro x hx y hy
    obtain ⟨i,hi⟩ := (Submonoid.mem_iSup_of_directed hF).mp hx
    obtain ⟨j,hj⟩ := (Submonoid.mem_iSup_of_directed hF).mp hy
    obtain ⟨k,hik,hjk⟩ := hF i j
    exact (le_iSup (fun k => (F k).submonoid) k) ((F k).joins x (hik hi) y (hjk hj))

section UnionLift
variable {K : Type u} [Preorder K] [IsDirectedOrder K] [Nonempty K]
  (F : K → Subobject T) (hF : Monotone (fun k => (F k).submonoid))
  (U : Subobject T) (hle : ∀ k, (F k).submonoid ≤ U.submonoid)
  (hcovers : ∀ x ∈ U.submonoid, ∃ k, x ∈ (F k).submonoid)
  {N : Type v} [Monoid N] (f : ∀ k, (F k).object →* N)
  (hf : ∀ i j (h : i ≤ j), (f j).comp (hom (hF h)).toMonoidHom = f i)

private def unionValue (x : U.object) : N :=
  f (hcovers x.val x.property).choose
    ⟨x.val,(hcovers x.val x.property).choose_spec⟩

include hf in
omit [Nonempty K] in
private theorem unionValue_at (k : K) (x : (F k).object) :
    unionValue F U hcovers f (hom (hle k) x) = f k x := by
  let i := (hcovers x.val ((hle k) x.property)).choose
  have hi := (hcovers x.val ((hle k) x.property)).choose_spec
  obtain ⟨j,hij,hkj⟩ := exists_ge_ge i k
  have e₁ := DFunLike.congr_fun (hf i j hij) ⟨x.val,hi⟩
  have e₂ := DFunLike.congr_fun (hf k j hkj) x
  exact e₁.symm.trans e₂

/-- A compatible family of arbitrary monoid homomorphisms glues over an
actual directed union. -/
def unionLift : U.object →* N where
  toFun := unionValue F U hcovers f
  map_one' := by
    let k : K := Classical.arbitrary K
    exact (unionValue_at F hF U hle hcovers f hf k 1).trans (f k).map_one
  map_mul' x y := by
    obtain ⟨i,hi⟩ := hcovers x.val x.property
    obtain ⟨j,hj⟩ := hcovers y.val y.property
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    let a : (F k).object := ⟨x.val,hF hik hi⟩
    let b : (F k).object := ⟨y.val,hF hjk hj⟩
    have ha : hom (hle k) a = x := Subtype.ext rfl
    have hb : hom (hle k) b = y := Subtype.ext rfl
    rw [← ha,← hb,← (hom (hle k)).map_mul]
    rw [unionValue_at F hF U hle hcovers f hf k,
      unionValue_at F hF U hle hcovers f hf k,
      unionValue_at F hF U hle hcovers f hf k]
    exact (f k).map_mul a b

@[simp] theorem unionLift_comp (k : K) :
    (unionLift F hF U hle hcovers f hf).comp (hom (hle k)).toMonoidHom = f k := by
  ext x
  exact unionValue_at F hF U hle hcovers f hf k x

end UnionLift

namespace Square
variable {A B C D E F : Subobject T}

theorem identity (h : A.submonoid ≤ B.submonoid) : Square A A B B :=
  ⟨le_refl _,h,h,le_refl _,IsPushout.of_id (hom h).toMonoidHom⟩

theorem paste (h : Square A B C D) (h' : Square B E D F) : Square A E C F :=
  ⟨h.ab.trans h'.ab,h.ac,h'.bd,h.cd.trans h'.cd,h.pushout.paste h'.pushout⟩

theorem cancel_left (h : Square A B C D) (ho : Square A E C F)
    (hBE : B.submonoid ≤ E.submonoid) (hDF : D.submonoid ≤ F.submonoid) :
    Square B E D F :=
  ⟨hBE,h.bd,ho.bd,hDF,h.pushout.cancel_left (by ext x; rfl) ho.pushout⟩

/-- The pushout of a fixed base change with a directed union is the union
of the actual pushout stages. -/
theorem union {K : Type u} [Preorder K] [IsDirectedOrder K] [Nonempty K]
    {A C Bup Dup : Subobject T} (B D : K → Subobject T)
    (hB : Monotone (fun k => (B k).submonoid))
    (hD : Monotone (fun k => (D k).submonoid))
    (hBL : ∀ k, (B k).submonoid ≤ Bup.submonoid)
    (hDL : ∀ k, (D k).submonoid ≤ Dup.submonoid)
    (hBU : ∀ x ∈ Bup.submonoid, ∃ k, x ∈ (B k).submonoid)
    (hDU : ∀ x ∈ Dup.submonoid, ∃ k, x ∈ (D k).submonoid)
    (h : ∀ k, Square A (B k) C (D k)) : Square A Bup C Dup := by
  let k₀ : K := Classical.arbitrary K
  have hab : A.submonoid ≤ Bup.submonoid := (h k₀).ab.trans (hBL k₀)
  have hac : A.submonoid ≤ C.submonoid := (h k₀).ac
  have hbd : Bup.submonoid ≤ Dup.submonoid := by
    intro x hx
    obtain ⟨i,hi⟩ := hBU x hx
    exact hDL i ((h i).bd hi)
  have hcd : C.submonoid ≤ Dup.submonoid := (h k₀).cd.trans (hDL k₀)
  refine ⟨hab,hac,hbd,hcd,⟨by ext x; rfl,?_⟩⟩
  intro N _ b c hc
  have hi (i : K) : (b.comp (hom (hBL i)).toMonoidHom).comp (hom (h i).ab).toMonoidHom =
      c.comp (hom (h i).ac).toMonoidHom := hc
  let t (i : K) := (h i).pushout.lift (b.comp (hom (hBL i)).toMonoidHom) c (hi i)
  have ht₁ (i : K) : (t i).comp (hom (h i).bd).toMonoidHom =
      b.comp (hom (hBL i)).toMonoidHom := (h i).pushout.lift_comp_left _ _ _
  have ht₂ (i : K) : (t i).comp (hom (h i).cd).toMonoidHom = c :=
    (h i).pushout.lift_comp_right _ _ _
  have ht (i j : K) (hij : i ≤ j) :
      (t j).comp (hom (hD hij)).toMonoidHom = t i := by
    apply (h i).pushout.hom_ext
    · ext x
      have e₁ := DFunLike.congr_fun (ht₁ j) (hom (hB hij) x)
      have e₂ := DFunLike.congr_fun (ht₁ i) x
      exact e₁.trans e₂.symm
    · ext x
      exact (DFunLike.congr_fun (ht₂ j) x).trans (DFunLike.congr_fun (ht₂ i) x).symm
  let l := unionLift D hD Dup hDL hDU t ht
  have hl₁ : l.comp (hom hbd).toMonoidHom = b := by
    ext x
    obtain ⟨i,hi⟩ := hBU x.val x.property
    have e₁ := DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht i)
      (hom (h i).bd ⟨x.val,hi⟩)
    have e₂ := DFunLike.congr_fun (ht₁ i) ⟨x.val,hi⟩
    exact e₁.trans e₂
  have hl₂ : l.comp (hom hcd).toMonoidHom = c := by
    ext x
    exact (DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht k₀)
      (hom (h k₀).cd x)).trans (DFunLike.congr_fun (ht₂ k₀) x)
  refine ⟨l,⟨hl₁,hl₂⟩,?_⟩
  intro m hm
  have he (i : K) : m.comp (hom (hDL i)).toMonoidHom = t i := by
    apply (h i).pushout.hom_ext
    · ext x
      exact (DFunLike.congr_fun hm.1 (hom (hBL i) x)).trans
        (DFunLike.congr_fun (ht₁ i) x).symm
    · ext x
      exact (DFunLike.congr_fun hm.2 x).trans (DFunLike.congr_fun (ht₂ i) x).symm
  ext x
  obtain ⟨i,hi⟩ := hDU x.val x.property
  exact (DFunLike.congr_fun (he i) ⟨x.val,hi⟩).trans
    (DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht i) ⟨x.val,hi⟩).symm

end Square
end
end PartitionConsistency.ConservativeMonoids.Subobject


/-! ## CellReorder -/

/-! Rearranging the actual tower: a countable dependency-closed submonoid
can be performed first, and every omitted cell can then be appended in its
original order. The construction uses full monoid pushouts at all cuts. -/
namespace PartitionConsistency.ConservativeMonoids.CellTower
universe u
open CategoryTheory DiagramOrder MonoidPushout _root_.OAI.PartitionConsistency.ConservativeMonoids.Subobject
noncomputable section
open scoped Classical
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J] (D : CellTower T J) (S : Subobject T)

/-- Simulate the selected future cells over any original earlier cut. The
result has exactly the union presentation, not a further conservative hull. -/
theorem future_cut (hS : D.Closed S) (a b : J) (hab : a ≤ b) :
    ∃ R : Subobject T, R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S b).submonoid ∧
      Square (D.restrict S a) (D.restrict S b) (D.stage a) R := by
  have base (a : J) : ∃ R : Subobject T,
      R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S a).submonoid ∧
      Square (D.restrict S a) (D.restrict S a) (D.stage a) R :=
    ⟨D.stage a,(sup_eq_left.mpr (D.restrict_le S a)).symm,
      Square.identity (D.restrict_le S a)⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_of_le hab
    exact base a
  | succ b hb ih =>
    by_cases hab' : a ≤ b
    · obtain ⟨R,hR,hp⟩ := ih hab'
      by_cases hs : D.selected S b
      · obtain ⟨hd,hpush⟩ := D.restrict_selected S hS hs
        let hsquare : Square (D.restrict S b) (D.restrict S (Order.succ b))
            (D.stage b) (D.stage (Order.succ b)) :=
          ⟨D.restrict_mono S (Order.le_succ b),D.restrict_le S b,
            D.restrict_le S (Order.succ b),D.mono (Order.le_succ b),hpush⟩
        have hRb : R.submonoid ≤ (D.stage b).submonoid := by
          rw [hR]
          exact sup_le (D.mono hab') (D.restrict_le S b)
        obtain ⟨F,hF,hFb,hdF,hpF⟩ := hsquare.intermediate hd.some hp.bd hRb
        refine ⟨F,?_,hp.paste hpF⟩
        rw [hF,hR]
        exact (sup_comm _ _).trans (sup_assoc _ _ _ |>.trans
          (congrArg ((D.stage a).submonoid ⊔ ·)
            (sup_eq_right.mpr (D.restrict_mono S (Order.le_succ b)))))
      · have he : D.restrict S b = D.restrict S (Order.succ b) :=
          Subobject.ext (D.restrict_omitted S hs)
        exact ⟨R,by simpa only [he] using hR,by simpa only [he] using hp⟩
    · have ha : a = Order.succ b :=
        le_antisymm hab ((Order.succ_le_iff_of_not_isMax hb).mpr (lt_of_not_ge hab'))
      subst a
      exact base (Order.succ b)
  | isSuccLimit b hb ih =>
    by_cases he : a = b
    · subst a; exact base b
    have hab' : a < b := lt_of_le_of_ne hab he
    let K := {k : J // a ≤ k ∧ k < b}
    have : Nonempty K := ⟨⟨a,le_refl _,hab'⟩⟩
    have hR (k : K) : ∃ R : Subobject T,
        R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S k.val).submonoid ∧
        Square (D.restrict S a) (D.restrict S k.val) (D.stage a) R :=
      ih k.val k.property.2 k.property.1
    let R (k : K) := (hR k).choose
    have hReq (k : K) := (hR k).choose_spec.1
    have hRp (k : K) := (hR k).choose_spec.2
    have hmono : Monotone (fun k => (R k).submonoid) := by
      intro i j hij
      dsimp only [R]
      rw [hReq i,hReq j]
      exact sup_le_sup_left (D.restrict_mono S hij) _
    let U := Subobject.directedSup R hmono.directed_le
    have hRL (k : K) : (R k).submonoid ≤ U.submonoid :=
      (le_iSup (fun k : K => (R k).submonoid) k)
    have hRU (x : T) (hx : x ∈ U.submonoid) : ∃ k, x ∈ (R k).submonoid :=
      (Submonoid.mem_iSup_of_directed hmono.directed_le).mp hx
    have hBL (k : K) : (D.restrict S k.val).submonoid ≤ (D.restrict S b).submonoid :=
      D.restrict_mono S k.property.2.le
    have hBU (x : T) (hx : x ∈ (D.restrict S b).submonoid) :
        ∃ k : K, x ∈ (D.restrict S k.val).submonoid := by
      obtain ⟨j,hj,hxj⟩ := D.continuous b hb x hx.2
      exact ⟨⟨max a j,le_max_left _ _,max_lt hab' hj⟩,hx.1,D.mono (le_max_right _ _) hxj⟩
    have hpu := Square.union (fun k : K => D.restrict S k.val) R
      (fun _ _ h => D.restrict_mono S h) hmono hBL hRL hBU hRU hRp
    refine ⟨U,?_,hpu⟩
    exact hpu.apex_eq_sup.trans (sup_comm _ _)

/-- The original cut, followed by all its selected future cells. -/
def future (hS : D.Closed S) (a : J) : Subobject T :=
  (D.future_cut S hS a ⊤ le_top).choose

theorem future_eq (hS : D.Closed S) (a : J) :
    (D.future S hS a).submonoid = (D.stage a).submonoid ⊔ S.submonoid := by
  have hh := (D.future_cut S hS a ⊤ le_top).choose_spec.1
  change (D.future S hS a).submonoid = (D.stage a).submonoid ⊔
    (S.submonoid ⊓ (D.stage ⊤).submonoid) at hh
  simpa only [D.terminal,inf_top_eq] using hh

theorem future_square (hS : D.Closed S) (a : J) :
    Square (D.restrict S a) S (D.stage a) (D.future S hS a) := by
  have he : D.restrict S ⊤ = S := Subobject.ext (by
    change S.submonoid ⊓ (D.stage ⊤).submonoid = S.submonoid
    rw [D.terminal,inf_top_eq])
  have hh := (D.future_cut S hS a ⊤ le_top).choose_spec.2
  exact (congrArg (fun R => Square (D.restrict S a) R (D.stage a) (D.future S hS a)) he).mp hh

theorem future_mono (hS : D.Closed S) : Monotone (fun a => (D.future S hS a).submonoid) := by
  intro a b hab
  dsimp only
  rw [D.future_eq S hS a,D.future_eq S hS b]
  exact sup_le_sup_right (D.mono hab) _

theorem future_selected (hS : D.Closed S) {a : J} (ha : D.selected S a) :
    (D.future S hS a).submonoid = (D.future S hS (Order.succ a)).submonoid := by
  obtain ⟨_,hp⟩ := D.restrict_selected S hS ha
  let h : Square (D.restrict S a) (D.restrict S (Order.succ a))
      (D.stage a) (D.stage (Order.succ a)) :=
    ⟨D.restrict_mono S (Order.le_succ a),D.restrict_le S a,
      D.restrict_le S (Order.succ a),D.mono (Order.le_succ a),hp⟩
  apply le_antisymm (D.future_mono S hS (Order.le_succ a))
  dsimp only
  rw [D.future_eq S hS (Order.succ a),D.future_eq S hS a,h.apex_eq_sup]
  apply sup_le (sup_le ?_ le_sup_left) le_sup_right
  intro x hx
  exact (show S.submonoid ≤ (D.stage a).submonoid ⊔ S.submonoid from le_sup_right) hx.1

theorem future_omitted_square (hS : D.Closed S) {a : J} (ha : ¬ D.selected S a) :
    Square (D.stage a) (D.stage (Order.succ a))
      (D.future S hS a) (D.future S hS (Order.succ a)) := by
  have he : D.restrict S a = D.restrict S (Order.succ a) :=
    Subobject.ext (D.restrict_omitted S ha)
  have h₁ := (D.future_square S hS a).flip
  have h₂ : Square (D.restrict S a) (D.stage (Order.succ a)) S
      (D.future S hS (Order.succ a)) := by
    rw [he]; exact (D.future_square S hS (Order.succ a)).flip
  exact h₁.cancel_left h₂ (D.mono (Order.le_succ a)) (D.future_mono S hS (Order.le_succ a))

/-- The reordered tower, inside the same `T`. Its initial submonoid is
`S` whenever `S` contains the original initial stage. -/
def reordered (hS : D.Closed S) : CellTower T J where
  stage := D.future S hS
  mono := D.future_mono S hS
  terminal := by rw [D.future_eq S hS ⊤,D.terminal,top_sup_eq]
  continuous := by
    intro i hi x hx
    have : Nonempty (Set.Iio i) := hi.nonempty_Iio.to_subtype
    let F (k : Set.Iio i) := D.future S hS k.val
    have hF : Monotone (fun k => (F k).submonoid) := fun _ _ h => D.future_mono S hS h
    have hle : (D.future S hS i).submonoid ≤ ⨆ k : Set.Iio i, (F k).submonoid := by
      rw [D.future_eq S hS i]
      apply sup_le
      · intro y hy
        obtain ⟨j,hj,hyj⟩ := D.continuous i hi y hy
        apply le_iSup (fun k : Set.Iio i => (F k).submonoid) ⟨j,hj⟩
        change y ∈ (D.future S hS j).submonoid
        rw [D.future_eq S hS j]
        exact (show (D.stage j).submonoid ≤ (D.stage j).submonoid ⊔ S.submonoid from le_sup_left) hyj
      · let k : Set.Iio i := Classical.arbitrary _
        apply le_trans ?_ (le_iSup (fun k : Set.Iio i => (F k).submonoid) k)
        change S.submonoid ≤ (D.future S hS k.val).submonoid
        rw [D.future_eq S hS k.val]
        exact le_sup_right
    obtain ⟨k,hk⟩ := (Submonoid.mem_iSup_of_directed hF.directed_le).mp (hle hx)
    exact ⟨k.val,k.property,hk⟩
  step := by
    intro a
    by_cases h : D.selected S a
    · exact Or.inl (D.future_selected S hS h)
    · rcases D.step a with he | hd
      · left
        rw [D.future_eq S hS a,D.future_eq S hS (Order.succ a),he]
      · exact Or.inr ⟨(D.future_omitted_square S hS h).attachment hd.some⟩

theorem reordered_bottom (hS : D.Closed S) (hbottom : (D.stage ⊥).submonoid ≤ S.submonoid) :
    ((D.reordered S hS).stage ⊥).submonoid = S.submonoid := by
  change (D.future S hS ⊥).submonoid = S.submonoid
  rw [D.future_eq S hS ⊥,sup_eq_right.mpr hbottom]

/-- Every countable set is contained in a countable initial base for a
reordering by the original two kinds of cells. -/
theorem countable_reordering (hbot : ((D.stage ⊥).submonoid : Set T).Countable)
    (s : Set T) (hs : s.Countable) :
    ∃ E : CellTower T J, ((E.stage ⊥).submonoid : Set T).Countable ∧
      s ⊆ (E.stage ⊥).submonoid := by
  let S := D.hull s
  have hS : D.Closed S := fun _ hx => D.hull_closed hx
  refine ⟨D.reordered S hS,?_,?_⟩
  all_goals rw [D.reordered_bottom S hS (D.bottom_le_hull s)]
  · exact D.hull_countable hs hbot
  · exact D.subset_hull s

end
end PartitionConsistency.ConservativeMonoids.CellTower

end OAI

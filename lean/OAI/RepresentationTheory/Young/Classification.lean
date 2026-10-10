import Mathlib
import OAI.RepresentationTheory.Unitary.Basic

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.YoungCorner

abbrev Boxes (μ : YoungDiagram) := ↥μ.cells

def colorStabilizer {X A : Type*} (f : X → A) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, f (σ x)=f x}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb x; exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using (ha (a⁻¹ x)).symm

def rows (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) := colorStabilizer (fun x => x.val.1)
def cols (μ : YoungDiagram) : Subgroup (Equiv.Perm (Boxes μ)) := colorStabilizer (fun x => x.val.2)

lemma row_lt (μ : YoungDiagram) (x : Boxes μ) : x.val.1 < μ.colLen 0 := by
  apply YoungDiagram.mem_iff_lt_colLen.mp
  exact μ.up_left_mem le_rfl (Nat.zero_le _) x.property

lemma col_lt (μ : YoungDiagram) (x : Boxes μ) : x.val.2 < μ.rowLen x.val.1 :=
  YoungDiagram.mem_iff_lt_rowLen.mp x.property

def rowDecomp (μ : YoungDiagram) : Boxes μ ≃ Σ i : Fin (μ.colLen 0), Fin (μ.rowLen i) where
  toFun x := ⟨⟨x.val.1,row_lt μ x⟩,⟨x.val.2,col_lt μ x⟩⟩
  invFun x := ⟨(x.1,x.2),YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by rcases x with ⟨i,j⟩; rfl

lemma strictMono_fin_nat_ge {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) : i.val ≤ f i := by
  suffices hh : ∀ k, ∀ h : k < n, k ≤ f ⟨k,h⟩ from hh i.val i.isLt
  intro k
  induction k with
  | zero => intro h; exact Nat.zero_le _
  | succ k ih =>
    intro h
    have hk : k < n := by omega
    have hh := hf (show (⟨k,hk⟩ : Fin n) < ⟨k+1,h⟩ from by simp)
    have hi := ih hk
    omega

def values {n : ℕ} (f : Fin n → ℕ) : Finset ℕ := Finset.univ.image f

lemma values_card {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : (values f).card=n := by
  simp [values,Finset.card_image_of_injective _ hf]

def valuesEquiv {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : Fin n ≃ ↥(values f) :=
  Equiv.ofBijective (fun x => ⟨f x,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun x y h => hf (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x,rfl⟩⟩

/- Sort a finite injective natural-valued list without changing its indices. -/
def sortPerm {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) : Equiv.Perm (Fin n) :=
  ((values f).orderIsoOfFin (values_card f hf)).toEquiv.trans (valuesEquiv f hf).symm

lemma sortPerm_ge {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) (i : Fin n) :
    i.val ≤ f (sortPerm f hf i) := by
  have he : f (sortPerm f hf i) = ((values f).orderEmbOfFin (values_card f hf)) i := by
    have hh := (valuesEquiv f hf).apply_symm_apply (((values f).orderIsoOfFin (values_card f hf)) i)
    exact congrArg Subtype.val hh
  rw [he]
  exact strictMono_fin_nat_ge _ ((values f).orderEmbOfFin (values_card f hf)).strictMono i

/- Row-column noncollision: at most one source cell in any row can land in
any destination column. -/
def NoCollision (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) : Prop :=
  ∀ x y, x.val.1=y.val.1 → (σ x).val.2=(σ y).val.2 → x=y

def rowColumn (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ))
    (i : Fin (μ.colLen 0)) (j : Fin (μ.rowLen i)) : ℕ :=
  (σ ((rowDecomp μ).symm ⟨i,j⟩)).val.2

lemma rowColumn_injective (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ))
    (h : NoCollision μ σ) (i : Fin (μ.colLen 0)) : Function.Injective (rowColumn μ σ i) := by
  intro j k hjk
  have hx := h ((rowDecomp μ).symm ⟨i,j⟩) ((rowDecomp μ).symm ⟨i,k⟩) rfl hjk
  exact Fin.ext (congrArg (fun x : Boxes μ => x.val.2) hx)

def sortingRows (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    Equiv.Perm (Boxes μ) :=
  (rowDecomp μ).trans ((Equiv.sigmaCongrRight fun i => sortPerm (rowColumn μ σ i)
    (rowColumn_injective μ σ h i)).trans (rowDecomp μ).symm)

lemma sortingRows_mem (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    sortingRows μ σ h ∈ rows μ := by
  intro x
  rfl

lemma sortingRows_col_ge (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ)
    (x : Boxes μ) : x.val.2 ≤ (σ (sortingRows μ σ h x)).val.2 := by
  exact sortPerm_ge (rowColumn μ σ ⟨x.val.1,row_lt μ x⟩)
    (rowColumn_injective μ σ h _) ⟨x.val.2,col_lt μ x⟩

/- The essential Ferrers uniqueness lemma. Sorting inside rows can only
increase columns; preservation of the total column sum forces equality. -/
theorem factor_column_row (μ : YoungDiagram) (σ : Equiv.Perm (Boxes μ)) (h : NoCollision μ σ) :
    ∃ c ∈ cols μ, ∃ r ∈ rows μ, σ=c*r := by
  let r := sortingRows μ σ h
  have hr : r ∈ rows μ := sortingRows_mem μ σ h
  have hge : ∀ x : Boxes μ, x.val.2 ≤ ((σ*r) x).val.2 := sortingRows_col_ge μ σ h
  have hsum : ∑ x : Boxes μ, x.val.2 = ∑ x : Boxes μ, ((σ*r) x).val.2 :=
    (Fintype.sum_equiv (σ*r) (fun x : Boxes μ => ((σ*r) x).val.2)
      (fun x : Boxes μ => x.val.2) (fun _ => rfl)).symm
  have heq : ∀ x : Boxes μ, x.val.2=((σ*r) x).val.2 := by
    intro x
    exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hge x)).mp hsum x (Finset.mem_univ _)
  refine ⟨σ*r,(fun x => (heq x).symm),r⁻¹,(rows μ).inv_mem hr,?_⟩
  simp

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def rowPrefix (μ : YoungDiagram) (t : ℕ) : Finset (Boxes μ) :=
  Finset.univ.filter (fun x => x.val.1<t)

def columnPrefixEquiv (μ : YoungDiagram) (t j : ℕ) :
    {x : Boxes μ // x ∈ (rowPrefix μ t).filter (fun x => x.val.2=j)} ≃ Fin (min t (μ.colLen j)) where
  toFun x := ⟨x.val.val.1,by
    have hx := Finset.mem_filter.mp x.property
    have ht := (Finset.mem_filter.mp hx.1).2
    have hc := YoungDiagram.mem_iff_lt_colLen.mp x.val.property
    rw [hx.2] at hc
    exact lt_min ht hc⟩
  invFun i := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_lt_of_le i.isLt (min_le_right _ _))⟩,by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rowPrefix,and_true]
    exact lt_of_lt_of_le i.isLt (min_le_left _ _)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (Finset.mem_filter.mp x.property).2.symm
  right_inv i := rfl

lemma card_column_prefix (μ : YoungDiagram) (t j : ℕ) :
    ((rowPrefix μ t).filter (fun x => x.val.2=j)).card=min t (μ.colLen j) := by
  have h := Fintype.card_congr (columnPrefixEquiv μ t j)
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

lemma card_source_column_le (μ ν : YoungDiagram) (e : Boxes μ ≃ Boxes ν)
    (hnc : ∀ x y, x.val.1=y.val.1 → (e x).val.2=(e y).val.2 → x=y) (t j : ℕ) :
    ((rowPrefix μ t).filter (fun x => (e x).val.2=j)).card ≤ min t (ν.colLen j) := by
  let F := (rowPrefix μ t).filter (fun x => (e x).val.2=j)
  have hr : F.card≤t := by
    let f : ↥F → Fin t := fun x => ⟨x.val.val.1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp x.property).1).2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply hnc
      · exact congrArg Fin.val hxy
      · exact (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp y.property).2.symm
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hc : F.card≤ν.colLen j := by
    let f : ↥F → Fin (ν.colLen j) := fun x => ⟨(e x.val).val.1,by
      have hx := YoungDiagram.mem_iff_lt_colLen.mp (e x.val).property
      rw [(Finset.mem_filter.mp x.property).2] at hx
      exact hx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Fin.val hxy
      · exact (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp y.property).2.symm
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact le_min hr hc

/- The actual Ferrers dominance consequence of a collision-free matching. -/
theorem prefix_dominance (μ ν : YoungDiagram) (e : Boxes μ ≃ Boxes ν)
    (hnc : ∀ x y, x.val.1=y.val.1 → (e x).val.2=(e y).val.2 → x=y) (t : ℕ) :
    (rowPrefix μ t).card≤(rowPrefix ν t).card := by
  have hμ : Set.MapsTo (fun x : Boxes μ => (e x).val.2) (rowPrefix μ t)
      (Finset.range (ν.rowLen 0)) := by
    intro x hx
    exact Finset.mem_range.mpr ((col_lt ν (e x)).trans_le (ν.rowLen_anti _ _ (Nat.zero_le _)))
  have hν : Set.MapsTo (fun x : Boxes ν => x.val.2) (rowPrefix ν t)
      (Finset.range (ν.rowLen 0)) := by
    intro x hx
    exact Finset.mem_range.mpr ((col_lt ν x).trans_le (ν.rowLen_anti _ _ (Nat.zero_le _)))
  rw [Finset.card_eq_sum_card_fiberwise hμ,Finset.card_eq_sum_card_fiberwise hν]
  apply Finset.sum_le_sum
  intro j hj
  rw [card_column_prefix]
  exact card_source_column_le μ ν e hnc t j

def rowEquiv (μ : YoungDiagram) (i : ℕ) :
    {x : Boxes μ // x.val.1=i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨x.val.val.2,by
    have hx := YoungDiagram.mem_iff_lt_rowLen.mp x.val.property
    rwa [x.property] at hx⟩
  invFun j := ⟨⟨(i,j),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.symm rfl
  right_inv j := rfl

lemma card_row (μ : YoungDiagram) (i : ℕ) :
    (Finset.univ.filter (fun x : Boxes μ => x.val.1=i)).card=μ.rowLen i := by
  have h := Fintype.card_congr (rowEquiv μ i)
  rw [Fintype.card_subtype] at h
  simpa only [Fintype.card_fin] using h

lemma prefix_succ (μ : YoungDiagram) (t : ℕ) :
    (rowPrefix μ (t+1)).card=(rowPrefix μ t).card+μ.rowLen t := by
  have he : rowPrefix μ (t+1)=rowPrefix μ t ∪ Finset.univ.filter (fun x : Boxes μ => x.val.1=t) := by
    ext x
    simp only [rowPrefix,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    omega
  have hd : Disjoint (rowPrefix μ t) (Finset.univ.filter (fun x : Boxes μ => x.val.1=t)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxt := (Finset.mem_filter.mp hx).2
    have hyt := (Finset.mem_filter.mp hy).2
    omega
  rw [he,Finset.card_union_of_disjoint hd,card_row]

/- Opposite Young dominance determines the diagram. -/
lemma eq_of_prefix_dominance (μ ν : YoungDiagram)
    (hμν : ∀ t, (rowPrefix μ t).card≤(rowPrefix ν t).card)
    (hνμ : ∀ t, (rowPrefix ν t).card≤(rowPrefix μ t).card) : μ=ν := by
  have he (t : ℕ) : (rowPrefix μ t).card=(rowPrefix ν t).card := le_antisymm (hμν t) (hνμ t)
  have hr (t : ℕ) : μ.rowLen t=ν.rowLen t := by
    have hh := he (t+1)
    rw [prefix_succ,prefix_succ,he t] at hh
    omega
  apply SetLike.ext
  rintro ⟨i,j⟩
  simp only [YoungDiagram.mem_iff_lt_rowLen,hr]

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma subrep_bot (τ : Representation ℂ G V) :
    (⊥ : Subrepresentation τ).toSubmodule=⊥ := rfl
omit [Fintype G] [FiniteDimensional ℂ V] in
@[simp] lemma subrep_top (τ : Representation ℂ G V) :
    (⊤ : Subrepresentation τ).toSubmodule=⊤ := rfl

def nested {τ : Representation ℂ G V} (S : Subrepresentation τ)
    (T : Subrepresentation S.toRepresentation) : Subrepresentation τ where
  toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨S.toRepresentation g w,T.apply_mem_toSubmodule g hw,rfl⟩

theorem exists_irreducible_detecting (τ : Representation ℂ G V)
    (A : Module.End ℂ V) (hA : A ≠ 0) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧
      ∃ v : S.toSubmodule, A v ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, A v ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (LinearMap.ext h)
  have hp : ∃ n, ∃ S : Subrepresentation τ,
      (∃ v : S.toSubmodule, A v ≠ 0) ∧ Module.finrank ℂ S.toSubmodule=n :=
    ⟨Module.finrank ℂ V,⊤,⟨⟨v,Submodule.mem_top⟩,hv⟩,by simp⟩
  obtain ⟨S,⟨w,hw⟩,hSdim⟩ := Nat.find_spec hp
  have hmin (T : Subrepresentation τ) (ht : ∃ v : T.toSubmodule, A v ≠ 0) :
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    rw [hSdim]
    exact Nat.find_min' hp ⟨T,ht,rfl⟩
  have : Nontrivial S.toSubmodule := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    have hz : w=0 := Subsingleton.elim _ _
    simp [hz] at hw
  refine ⟨S,?_,w,hw⟩
  refine { exists_pair_ne := ⟨⊥,⊤,?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro T
    by_cases hT : T=⊥
    · exact Or.inl hT
    right
    by_contra htop
    let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    obtain ⟨U,hU⟩ := exists_isCompl T
    have hUt : U ≠ ⊤ := by
      intro he
      have hh := hU.inf_eq_bot
      rw [he,inf_top_eq] at hh
      exact hT hh
    have hw' : w ∈ T.toSubmodule ⊔ U.toSubmodule := by
      have he := congrArg Subrepresentation.toSubmodule hU.sup_eq_top
      rw [← Subrepresentation.toSubmodule_sup,he]
      exact Submodule.mem_top
    obtain ⟨t,ht,u,hu,hwu⟩ := Submodule.mem_sup.mp hw'
    have hdetect : (A (t : V) ≠ 0) ∨ (A (u : V) ≠ 0) := by
      by_contra hn
      push Not at hn
      apply hw
      rw [← hwu]
      simp [map_add,hn]
    rcases hdetect with htA | huA
    · have hlow := hmin (nested S T) ⟨⟨t,⟨t,ht,rfl⟩⟩,htA⟩
      have hdim : Module.finrank ℂ (nested S T).toSubmodule = Module.finrank ℂ T.toSubmodule :=
        S.toSubmodule.finrank_map_subtype_eq T.toSubmodule
      have hhigh : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ S.toSubmodule :=
        Submodule.finrank_lt (fun he => htop (Subrepresentation.toSubmodule_injective he))
      omega
    · have hlow := hmin (nested S U) ⟨⟨u,⟨u,hu,rfl⟩⟩,huA⟩
      have hdim : Module.finrank ℂ (nested S U).toSubmodule = Module.finrank ℂ U.toSubmodule :=
        S.toSubmodule.finrank_map_subtype_eq U.toSubmodule
      have hhigh : Module.finrank ℂ U.toSubmodule < Module.finrank ℂ S.toSubmodule :=
        Submodule.finrank_lt (fun he => hUt (Subrepresentation.toSubmodule_injective he))
      omega

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.RepDetection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/- Irreducibility supplies the cross-corner nonvanishing needed for Young
shape uniqueness via the orbit-span argument. -/
theorem exists_cross_nonzero (τ : Representation ℂ G V) [τ.IsIrreducible]
    (P Q : Module.End ℂ V) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ g, P * τ g * Q ≠ 0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (LinearMap.ext h)
  let S : Subrepresentation τ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => τ g (Q v)))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k,rfl⟩ := hw
          apply Submodule.subset_span
          exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
        | zero => simp
        | add x y hx hy ix iy => simpa using Submodule.add_mem _ ix iy
        | smul c x hx ix => simpa using Submodule.smul_mem _ c ix }
  have hSne : S ≠ ⊥ := by
    intro hs
    have hm : Q v ∈ S := by
      apply Submodule.subset_span
      exact ⟨1,by simp⟩
    rw [hs] at hm
    exact hv hm
  have hStop : S=⊤ := (eq_bot_or_eq_top S).resolve_left hSne
  by_contra hn
  push Not at hn
  have hs : S.toSubmodule ≤ LinearMap.ker P := by
    apply Submodule.span_le.mpr
    rintro x ⟨g,rfl⟩
    have hh := congrArg (fun (A : Module.End ℂ V) => A v) (hn g)
    exact hh
  rw [hStop] at hs
  apply hP
  apply LinearMap.ext
  intro x
  exact hs Submodule.mem_top

end CoordinateSweeps.RepDetection

namespace CoordinateSweeps.YoungCorner
variable {X A : Type*} [Fintype X] [DecidableEq X] [Ring A] [Algebra ℂ A]

/- Ordinary source sign. -/
def signScalar {X : Type*} [Fintype X] [DecidableEq X] : Equiv.Perm X →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp] lemma signScalar_swap {X : Type*} [Fintype X] [DecidableEq X] (a b : X) (hab : a ≠ b) :
    signScalar (Equiv.swap a b) = -1 := by
  simp [signScalar,Equiv.Perm.sign_swap hab]

def fixedSum (f : X → ℕ) (ρ : Equiv.Perm X →* A) : A :=
  ∑ r : colorStabilizer f, ρ r

def alternatingSum (f : X → ℕ) (ρ : Equiv.Perm X →* A) : A :=
  ∑ r : colorStabilizer f, signScalar (r : Equiv.Perm X) • ρ r
omit [Algebra ℂ A] in
lemma fixedSum_right (f : X → ℕ) (ρ : Equiv.Perm X →* A)
    (r : colorStabilizer f) : fixedSum f ρ * ρ r = fixedSum f ρ := by
  rw [fixedSum,Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight r) _ _ (fun _ => rfl)

lemma alternatingSum_left (f : X → ℕ) (ρ : Equiv.Perm X →* A)
    (c : colorStabilizer f) : ρ c * alternatingSum f ρ = (signScalar (c : Equiv.Perm X))⁻¹ • alternatingSum f ρ := by
  rw [alternatingSum,Finset.mul_sum,Finset.smul_sum]
  have hc : signScalar (c : Equiv.Perm X) ≠ 0 := by
    intro hzero
    have hh : signScalar (c : Equiv.Perm X)*signScalar (c : Equiv.Perm X)⁻¹=1 := by
      rw [← map_mul,mul_inv_cancel,map_one]
    rw [hzero,zero_mul] at hh
    exact zero_ne_one hh
  apply Fintype.sum_equiv (Equiv.mulLeft c)
  intro d
  change ρ (c : Equiv.Perm X) * (signScalar (d : Equiv.Perm X) • ρ (d : Equiv.Perm X)) =
    (signScalar (c : Equiv.Perm X))⁻¹ • (signScalar ((c : Equiv.Perm X) * (d : Equiv.Perm X)) • ρ ((c : Equiv.Perm X) * (d : Equiv.Perm X)))
  rw [mul_smul_comm,smul_smul,map_mul,map_mul,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

omit [Fintype X] in
lemma swap_mem_color (f : X → ℕ) (x y : X) (h : f x=f y) :
    Equiv.swap x y ∈ colorStabilizer f := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

/- Literal transposition cancellation in a Young row/column corner. -/
lemma colored_corner_zero (f g : X → ℕ) (ρ : Equiv.Perm X →* A)
    (σ : Equiv.Perm X) (x y : X) (hxy : x ≠ y)
    (hrow : f x=f y) (hcol : g (σ⁻¹ x)=g (σ⁻¹ y)) :
    fixedSum f ρ * ρ σ * alternatingSum g ρ=0 := by
  let r : colorStabilizer f := ⟨Equiv.swap x y,swap_mem_color f x y hrow⟩
  let c : colorStabilizer g := ⟨Equiv.swap (σ⁻¹ x) (σ⁻¹ y),swap_mem_color g _ _ hcol⟩
  have hcxy : σ⁻¹ x ≠ σ⁻¹ y := fun h => hxy ((σ⁻¹).injective h)
  have he : (r : Equiv.Perm X)*σ = σ*(c : Equiv.Perm X) := by
    apply Equiv.ext
    intro z
    change Equiv.swap x y (σ z) = σ (Equiv.swap (σ⁻¹ x) (σ⁻¹ y) z)
    by_cases hx : z=σ⁻¹ x
    · subst z; simp
    by_cases hy : z=σ⁻¹ y
    · subst z; simp
    have hx' : σ z ≠ x := by
      intro he; apply hx
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    have hy' : σ z ≠ y := by
      intro he; apply hy
      have hh := congrArg (fun a => σ⁻¹ a) he
      simpa using hh
    rw [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have hc : (signScalar (c : Equiv.Perm X))⁻¹ = -1 := by rw [show (c : Equiv.Perm X)=Equiv.swap (σ⁻¹ x) (σ⁻¹ y) from rfl,signScalar_swap _ _ hcxy]; norm_num
  have hh : fixedSum f ρ * ρ σ * alternatingSum g ρ = -(fixedSum f ρ * ρ σ * alternatingSum g ρ) := by
    calc
      _ = (fixedSum f ρ * ρ r)*ρ σ*alternatingSum g ρ := by rw [fixedSum_right]
      _ = fixedSum f ρ * (ρ σ * ρ c) * alternatingSum g ρ := by rw [mul_assoc (fixedSum f ρ) (ρ r) (ρ σ),← map_mul,he,map_mul]
      _ = fixedSum f ρ * ρ σ * (ρ c * alternatingSum g ρ) := by simp only [mul_assoc]
      _ = _ := by rw [alternatingSum_left,hc]; simp
  have htwo : (2 : ℂ) • (fixedSum f ρ * ρ σ * alternatingSum g ρ)=0 := by
    rw [two_smul,← eq_neg_iff_add_eq_zero]
    exact hh
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

def rowColor {μ : YoungDiagram} (t : X ≃ Boxes μ) : X → ℕ := fun x => (t x).val.1
def colColor {μ : YoungDiagram} (t : X ≃ Boxes μ) : X → ℕ := fun x => (t x).val.2

def hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) (τ : Representation ℂ (Equiv.Perm X) V) : Prop :=
  fixedSum (rowColor t) τ * alternatingSum (colColor t) τ ≠ 0

lemma cross_dominance (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : X ≃ Boxes ν)
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible]
    (hP : fixedSum (rowColor t) τ ≠ 0) (hQ : alternatingSum (colColor u) τ ≠ 0) (k : ℕ) :
    (rowPrefix μ k).card≤(rowPrefix ν k).card := by
  obtain ⟨σ,hσ⟩ := RepDetection.exists_cross_nonzero τ _ _ hP hQ
  let e : Boxes μ ≃ Boxes ν := (t.symm.trans σ.symm).trans u
  apply prefix_dominance μ ν e _ k
  intro x y hrow hcol
  apply t.symm.injective
  by_contra hxy
  apply hσ
  apply colored_corner_zero (rowColor t) (colColor u) τ σ (t.symm x) (t.symm y) hxy
  · simpa [rowColor] using hrow
  · exact hcol

/- A genuine irreducible cannot carry two different Young shapes. -/
theorem shape_unique (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : X ≃ Boxes ν)
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible]
    (hμ : hasShape μ t τ) (hν : hasShape ν u τ) : μ=ν := by
  have hPμ : fixedSum (rowColor t) τ ≠ 0 := left_ne_zero_of_mul hμ
  have hQμ : alternatingSum (colColor t) τ ≠ 0 := right_ne_zero_of_mul hμ
  have hPν : fixedSum (rowColor u) τ ≠ 0 := left_ne_zero_of_mul hν
  have hQν : alternatingSum (colColor u) τ ≠ 0 := right_ne_zero_of_mul hν
  exact eq_of_prefix_dominance μ ν
    (cross_dominance μ ν t u τ hPμ hQν) (cross_dominance ν μ u t τ hPν hQμ)

lemma hasShape_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (μ : YoungDiagram) (t : X ≃ Boxes μ)
    (τ : Representation ℂ (Equiv.Perm X) V) (σ : Representation ℂ (Equiv.Perm X) W)
    (e : Representation.Equiv τ σ) (h : hasShape μ t τ) : hasShape μ t σ := by
  have hg (g : Equiv.Perm X) : e.toLinearEquiv.conjAlgEquiv ℂ (τ g)=σ g :=
    Representation.Equiv.conj_apply_self g e
  have he : e.toLinearEquiv.conjAlgEquiv ℂ (fixedSum (rowColor t) τ * alternatingSum (colColor t) τ)=
      fixedSum (rowColor t) σ * alternatingSum (colColor t) σ := by
    simp only [fixedSum,alternatingSum,map_mul,map_sum,map_smul,hg]
  intro hz
  apply h
  apply (e.toLinearEquiv.conjAlgEquiv ℂ).injective
  rw [he,hz,map_zero]

variable (G : Type*) [Group G]

def regular : Representation ℂ G (G → ℂ) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹*x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev,mul_assoc]

@[simp] lemma regular_apply (g : G) (f : G → ℂ) (x : G) : regular G g f x=f (g⁻¹*x) := rfl

omit [AddCommGroup V] [Module ℂ V] [Fintype X] [DecidableEq X] in
lemma row_column_intersection (μ : YoungDiagram) (t : X ≃ Boxes μ)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t)) :
    (r : Equiv.Perm X)*(c : Equiv.Perm X)=1 ↔ r=1 ∧ c=1 := by
  constructor
  · intro h
    have he : (r : Equiv.Perm X)=(c : Equiv.Perm X)⁻¹ := by
      calc
        _ = ((r : Equiv.Perm X)*(c : Equiv.Perm X))*(c : Equiv.Perm X)⁻¹ := by simp [mul_assoc]
        _ = _ := by rw [h,one_mul]
    have hr : r=1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      apply t.injective
      apply Subtype.ext
      apply Prod.ext
      · exact r.property x
      · have hc := (colorStabilizer (colColor t)).inv_mem c.property
        change colColor t ((r : Equiv.Perm X) x)=colColor t x
        rw [he]
        exact hc x
    refine ⟨hr,?_⟩
    apply Subtype.ext
    simpa [hr] using h
  · rintro ⟨rfl,rfl⟩
    simp

/- Every diagram has a nonzero row-column corner in the genuine regular law. -/
lemma regular_hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    hasShape μ t (regular (Equiv.Perm X)) := by
  let v : Equiv.Perm X → ℂ := fun g => if g=1 then 1 else 0
  have hv : (fixedSum (rowColor t) (regular (Equiv.Perm X)) *
      alternatingSum (colColor t) (regular (Equiv.Perm X))) v 1=1 := by
    simp only [fixedSum,alternatingSum,Module.End.mul_apply,LinearMap.sum_apply,regular_apply,
      Finset.sum_apply,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,mul_one,v,
      ← mul_inv_rev,inv_eq_one,row_column_intersection]
    simp [ite_and]
  intro hz
  have hh := congrArg (fun A : Module.End ℂ (Equiv.Perm X → ℂ) => A v 1) hz
  rw [hv] at hh
  exact one_ne_zero hh

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X V : Type*} [Fintype X] [DecidableEq X] [AddCommGroup V] [Module ℂ V]

lemma fixedSum_subrepresentation (f : X → ℕ) (τ : Representation ℂ (Equiv.Perm X) V)
    (S : Subrepresentation τ) (v : S.toSubmodule) :
    (fixedSum f S.toRepresentation v : V)=fixedSum f τ (v : V) := by
  simp [fixedSum,Subrepresentation.toRepresentation]

lemma alternatingSum_subrepresentation (f : X → ℕ) (τ : Representation ℂ (Equiv.Perm X) V)
    (S : Subrepresentation τ) (v : S.toSubmodule) :
    (alternatingSum f S.toRepresentation v : V)=alternatingSum f τ (v : V) := by
  simp [alternatingSum,Subrepresentation.toRepresentation]

lemma exists_shape_constituent (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    ∃ S : Subrepresentation (regular (Equiv.Perm X)),
      S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation := by
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting (regular (Equiv.Perm X))
    (fixedSum (rowColor t) (regular (Equiv.Perm X))*alternatingSum (colColor t) (regular (Equiv.Perm X)))
    (regular_hasShape μ t)
  refine ⟨S,hS,?_⟩
  intro hh
  apply hv
  have hz := congrArg (fun A : Module.End ℂ S.toSubmodule => (A v : Equiv.Perm X → ℂ)) hh
  simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hz
  exact hz

/- Chosen regular constituent. -/
def shapeSubrep (μ : YoungDiagram) (t : X ≃ Boxes μ) : Subrepresentation (regular (Equiv.Perm X)) :=
  Classical.choose (exists_shape_constituent μ t)

instance shapeSubrep_irreducible (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    (shapeSubrep μ t).toRepresentation.IsIrreducible :=
  (Classical.choose_spec (exists_shape_constituent μ t)).1

lemma shapeSubrep_hasShape (μ : YoungDiagram) (t : X ≃ Boxes μ) :
    hasShape μ t (shapeSubrep μ t).toRepresentation :=
  (Classical.choose_spec (exists_shape_constituent μ t)).2

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def diagramOfPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionRows_pos {n : ℕ} (p : Nat.Partition n) (x : ℕ)
    (hx : x ∈ p.parts.sort (· ≥ ·)) : 0 < x := by
  apply p.parts_pos
  have hh : x ∈ (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ) := hx
  simpa only [Multiset.sort_eq] using hh

lemma diagramOfPartition_rowLens {n : ℕ} (p : Nat.Partition n) :
    (diagramOfPartition p).rowLens=p.parts.sort (· ≥ ·) :=
  YoungDiagram.rowLens_ofRowLens_eq_self (partitionRows_pos p)

lemma diagramOfPartition_injective {n : ℕ} : Function.Injective (@diagramOfPartition n) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hh := congrArg YoungDiagram.rowLens hpq
  rw [diagramOfPartition_rowLens,diagramOfPartition_rowLens] at hh
  have hm := congrArg (fun t : List ℕ => (t : Multiset ℕ)) hh
  simpa only [Multiset.sort_eq] using hm

lemma card_boxes_eq_rowLens_sum (μ : YoungDiagram) :
    Fintype.card (Boxes μ)=μ.rowLens.sum := by
  rw [Fintype.card_congr (rowDecomp μ),Fintype.card_sigma]
  simp only [Fintype.card_fin,YoungDiagram.rowLens]
  have he : List.map μ.rowLen (List.range (μ.colLen 0)) =
      List.ofFn (fun i : Fin (μ.colLen 0) => μ.rowLen i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [he,List.sum_ofFn]

lemma card_diagramOfPartition {n : ℕ} (p : Nat.Partition n) :
    Fintype.card (Boxes (diagramOfPartition p))=n := by
  rw [card_boxes_eq_rowLens_sum,diagramOfPartition_rowLens,← Multiset.sum_coe,
    Multiset.sort_eq,p.parts_sum]

def partitionFilling {X : Type*} [Fintype X] (p : Nat.Partition (Fintype.card X)) :
    X ≃ Boxes (diagramOfPartition p) := Fintype.equivOfCardEq (card_diagramOfPartition p).symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.CharacterCount
universe u v w
variable {G : Type u} [Group G] [Fintype G]
variable {I : Type v} (V : I → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
  (τ : ∀ i, Representation ℂ G (V i)) [∀ i, (τ i).IsIrreducible]

def pairing (i : I) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Fintype.card G : ℂ)⁻¹ * ∑ g, f g * (τ i).character g⁻¹
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib,mul_add]
  map_smul' c f := by simp [Finset.mul_sum,mul_assoc,mul_left_comm]

lemma characters_independent
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j))) :
    LinearIndependent ℂ (fun i => (τ i).character) := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have hp (i j : I) : pairing V τ i (τ j).character=if j=i then 1 else 0 := by
    change (Fintype.card G : ℂ)⁻¹ * _ = _
    have hh := Representation.char_orthonormal (τ j) (τ i)
    rw [Nat.card_eq_fintype_card] at hh
    by_cases he : j=i
    · subst j
      have hi : Nonempty (Representation.Equiv (τ i) (τ i)) := ⟨Representation.Equiv.refl _⟩
      simpa [hi] using hh
    · have hi : ¬Nonempty (Representation.Equiv (τ i) (τ j)) := by
        intro ⟨e⟩
        exact (hne i j (Ne.symm he)).false e
      simpa [he,hi] using hh
  apply linearIndependent_iff'.mpr
  intro s c hs i hi
  have hh := congrArg (pairing V τ i) hs
  simp only [map_sum,map_smul,map_zero,hp,smul_eq_mul,mul_ite,mul_one,mul_zero] at hh
  simpa [hi] using hh

/- Pulling characters through any finite conjugacy classifier bounds how many
inequivalent irreducibles there can be. The classifier need not be surjective. -/
theorem card_le_of_classifier [Fintype I] {C : Type*} [Fintype C]
    (classifier : G → C)
    (hclass : ∀ i g h, classifier g=classifier h → (τ i).character g=(τ i).character h)
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j))) :
    Fintype.card I ≤ Fintype.card C := by
  classical
  let f : I → C → ℂ := fun i c =>
    if h : ∃ g, classifier g=c then (τ i).character (Classical.choose h) else 0
  have hf (i : I) (g : G) : f i (classifier g)=(τ i).character g := by
    dsimp [f]
    rw [dite_eq_left ⟨g,rfl⟩]
    exact hclass i _ _ (Classical.choose_spec (show ∃ k, classifier k=classifier g from ⟨g,rfl⟩))
  let L : (C → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => f ∘ classifier
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : (L ∘ f)=(fun i => (τ i).character) := by funext i g; exact hf i g
  have hind : LinearIndependent ℂ f := LinearIndependent.of_comp L
    (he ▸ characters_independent V τ hne)
  have hh := hind.fintype_card_le_finrank
  simpa using hh

end CoordinateSweeps.CharacterCount

namespace CoordinateSweeps.CharacterCount
universe u w
variable {G C : Type u} [Group G] [Fintype G] [Fintype C]
  (V : C → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (τ : ∀ i, Representation ℂ G (V i)) [∀ i, (τ i).IsIrreducible]

/- An inequivalent family as large as a finite conjugacy classifier is complete.
This finite counting argument establishes the Young classification. -/
theorem complete_of_classifier (classifier : G → C)
    (hτ : ∀ i g h, classifier g=classifier h → (τ i).character g=(τ i).character h)
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (τ i) (τ j)))
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (hσ : ∀ g h, classifier g=classifier h → σ.character g=σ.character h) :
    ∃ i, Nonempty (Representation.Equiv (τ i) σ) := by
  classical
  by_contra hn
  push Not at hn
  let E : Option C → Type w := fun i => match i with | none => W | some i => V i
  let : ∀ i, AddCommGroup (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let : ∀ i, Module ℂ (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let : ∀ i, FiniteDimensional ℂ (E i) := fun i => by cases i <;> dsimp [E] <;> infer_instance
  let υ : ∀ i, Representation ℂ G (E i) := fun i => match i with | none => σ | some i => τ i
  let : ∀ i, (υ i).IsIrreducible := fun i => by cases i <;> dsimp [υ] <;> infer_instance
  have huclass : ∀ i g h, classifier g=classifier h → (υ i).character g=(υ i).character h := by
    intro i g h he
    cases i with
    | none => exact hσ g h he
    | some i => exact hτ i g h he
  have hune : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (υ i) (υ j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact ⟨fun e => (hn j).false e.symm⟩
    | some i =>
      cases j with
      | none => exact ⟨fun e => (hn i).false e⟩
      | some j => exact hne i j (fun he => hij (congrArg some he))
  have hh := card_le_of_classifier E υ classifier huclass hune
  simp only [Fintype.card_option] at hh
  omega

lemma permutation_character_factors {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Equiv.Perm X) V)
    (g h : Equiv.Perm X) (he : g.partition=h.partition) : τ.character g=τ.character h := by
  obtain ⟨c,hc⟩ := isConj_iff.mp (Equiv.Perm.partition_eq_of_isConj.mpr he)
  rw [← hc,τ.char_conj]

end CoordinateSweeps.CharacterCount

namespace CoordinateSweeps.YoungCorner
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev PartitionSpace (p : Nat.Partition (Fintype.card X)) :=
  (shapeSubrep (diagramOfPartition p) (partitionFilling p (X := X))).toSubmodule

def partitionRep (p : Nat.Partition (Fintype.card X)) :
    Representation ℂ (Equiv.Perm X) (PartitionSpace (X := X) p) :=
  (shapeSubrep (diagramOfPartition p) (partitionFilling p (X := X))).toRepresentation

instance partitionRep_irreducible (p : Nat.Partition (Fintype.card X)) :
    (partitionRep (X := X) p).IsIrreducible := shapeSubrep_irreducible _ _

lemma partitionRep_hasShape (p : Nat.Partition (Fintype.card X)) :
    hasShape (diagramOfPartition p) (partitionFilling p (X := X)) (partitionRep p (X := X)) :=
  shapeSubrep_hasShape _ _

lemma partitionRep_inequivalent (p q : Nat.Partition (Fintype.card X)) (hpq : p ≠ q) :
    IsEmpty (Representation.Equiv (partitionRep p (X := X)) (partitionRep q (X := X))) := by
  refine ⟨fun e => ?_⟩
  apply hpq
  apply diagramOfPartition_injective
  exact shape_unique _ _ (partitionFilling p) (partitionFilling q) (partitionRep q)
    (hasShape_equiv _ _ _ _ e (partitionRep_hasShape p)) (partitionRep_hasShape q)

/- Young classification from regular constituents, Ferrers dominance and
finite-group character orthogonality. -/
theorem partitionRep_complete {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p : Nat.Partition (Fintype.card X),
      Nonempty (Representation.Equiv (partitionRep p (X := X)) τ) := by
  let E : Nat.Partition (Fintype.card X) → Type := fun p => ↥(PartitionSpace (X := X) p)
  let υ : (p : Nat.Partition (Fintype.card X)) → Representation ℂ (Equiv.Perm X) (E p) :=
    fun p => partitionRep (X := X) p
  have hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (υ i) (υ j)) := by
    intro i j hij
    exact partitionRep_inequivalent (X := X) i j hij
  have hc : ∀ i g h, g.partition=h.partition → (υ i).character g=(υ i).character h :=
    fun i g h he => CharacterCount.permutation_character_factors (υ i) g h he
  exact CharacterCount.complete_of_classifier E υ Equiv.Perm.partition hc hne τ
    (CharacterCount.permutation_character_factors τ)

/- Every literal irreducible carries exactly one diagram shape. -/
theorem exists_partitionShape {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p : Nat.Partition (Fintype.card X), hasShape (diagramOfPartition p) (partitionFilling p) τ := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete τ
  exact ⟨p,hasShape_equiv _ _ _ _ e (partitionRep_hasShape p)⟩

/- Two actual irreps of the same diagram are equivalent, even for unrelated
fillings. This is the uniqueness fact needed for the hook/removal argument. -/
theorem equiv_of_same_shape {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ (Equiv.Perm X) V) (σ : Representation ℂ (Equiv.Perm X) W)
    [τ.IsIrreducible] [σ.IsIrreducible]
    (μ : YoungDiagram) (t u : X ≃ Boxes μ) (hτ : hasShape μ t τ) (hσ : hasShape μ u σ) :
    Nonempty (Representation.Equiv τ σ) := by
  obtain ⟨p,⟨ep⟩⟩ := partitionRep_complete τ
  obtain ⟨q,⟨eq⟩⟩ := partitionRep_complete σ
  have hp : μ=diagramOfPartition p := shape_unique _ _ t (partitionFilling p) τ hτ
    (hasShape_equiv _ _ _ _ ep (partitionRep_hasShape p))
  have hq : μ=diagramOfPartition q := shape_unique _ _ u (partitionFilling q) σ hσ
    (hasShape_equiv _ _ _ _ eq (partitionRep_hasShape q))
  have hpq : p=q := diagramOfPartition_injective (hp.symm.trans hq)
  subst q
  exact ⟨ep.symm.trans eq⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable (X : Type) [Fintype X] [DecidableEq X]

def partitionUnitary (p : Nat.Partition (Fintype.card X)) : UnitaryIrrep (Equiv.Perm X) :=
  Classical.choose (UnitaryRealization.exists_unitary (partitionRep p (X := X)))

lemma partitionUnitary_equiv (p : Nat.Partition (Fintype.card X)) :
    Nonempty (Representation.Equiv (partitionRep p (X := X))
      (partitionUnitary X p).asRepresentation) :=
  Classical.choose_spec (UnitaryRealization.exists_unitary (partitionRep p (X := X)))

lemma partitionUnitary_inequivalent (p q : Nat.Partition (Fintype.card X)) (hpq : p ≠ q) :
    ¬Nonempty (Representation.Equiv (partitionUnitary X p).asRepresentation
      (partitionUnitary X q).asRepresentation) := by
  rintro ⟨e⟩
  obtain ⟨ep⟩ := partitionUnitary_equiv X p
  obtain ⟨eq⟩ := partitionUnitary_equiv X q
  exact (partitionRep_inequivalent p q hpq).false ((ep.trans e).trans eq.symm)

lemma partitionUnitary_complete {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm X) V) [τ.IsIrreducible] :
    ∃ p, Nonempty (Representation.Equiv (partitionUnitary X p).asRepresentation τ) := by
  obtain ⟨p,⟨e⟩⟩ := partitionRep_complete τ
  obtain ⟨ep⟩ := partitionUnitary_equiv X p
  exact ⟨p,⟨ep.symm.trans e⟩⟩

/- The chosen Young projectors resolve identity in every finite representation.
The proof detects a simple constituent if the residual operator is nonzero. -/
theorem partition_projector_resolution {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ (Equiv.Perm X) V) :
    ∑ p, (partitionUnitary X p).projector τ=1 := by
  by_contra hn
  have hz : (∑ p, (partitionUnitary X p).projector τ) - 1 ≠ 0 := sub_ne_zero.mpr hn
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ _ hz
  let : AddCommGroup S.toSubmodule := inferInstance
  let : Module ℂ S.toSubmodule := inferInstance
  have : S.toRepresentation.IsIrreducible := hS
  obtain ⟨p,⟨ep⟩⟩ := partitionUnitary_complete X S.toRepresentation
  have hval (q) (w : Fin (partitionUnitary X p).dimension → ℂ) :
      ((partitionUnitary X q).projector τ) (ep w : V)=
        if q=p then (ep w : V) else 0 := by
    have hh := (partitionUnitary X q).projector_intertwiner
      (partitionUnitary X p).asRepresentation S.toRepresentation ep.toIntertwiningMap w
    have hincl : ∀ u : S.toSubmodule,
        (((partitionUnitary X q).projector S.toRepresentation) u : V)=
          ((partitionUnitary X q).projector τ) (u : V) := by
      intro u
      simp [UnitaryIrrep.projector,Subrepresentation.toRepresentation]
    rw [← hincl]
    have hh' : ((partitionUnitary X q).projector S.toRepresentation) (ep w)=
        ep (((partitionUnitary X q).projector (partitionUnitary X p).asRepresentation) w) := by
      exact hh
    rw [hh',UnitaryIrrep.projector_matrix_asRepresentation]
    split_ifs with he
    · subst q
      rw [UnitaryIrrep.projector_self,map_one]
      rfl
    · rw [UnitaryIrrep.projector_other _ _ (partitionUnitary_inequivalent X q p he),map_zero]
      simp
  have hs : (∑ q, (partitionUnitary X q).projector τ) (v : V)=(v : V) := by
    obtain ⟨w,rfl⟩ := ep.surjective v
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ q, (if q=p then (ep w : V) else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hval q w
      _ = _ := by simp
  exact hv (by simp only [LinearMap.sub_apply,Module.End.one_apply,hs,sub_self])

end CoordinateSweeps.YoungCorner
namespace CoordinateSweeps.YoungCorner
variable (X : Type) [Fintype X] [DecidableEq X]
lemma partition_matrix_resolution {J : Type} [Fintype J] [DecidableEq J]
    (τ : Equiv.Perm X →* Matrix J J ℂ) :
    ∑ p, (partitionUnitary X p).projector τ=1 := by
  apply Matrix.toLinAlgEquiv'.injective
  have hh := partition_projector_resolution X (UnitaryIrrep.matrixRepresentation τ)
  have hm (p : Nat.Partition (Fintype.card X)) :
      Matrix.toLinAlgEquiv' ((partitionUnitary X p).projector τ)=
        (partitionUnitary X p).projector (UnitaryIrrep.matrixRepresentation τ) := by
    simp only [UnitaryIrrep.projector,map_sum,map_smul]
    rfl
  rw [map_sum,map_one]
  simpa only [hm] using hh

end CoordinateSweeps.YoungCorner

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI

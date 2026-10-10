import Mathlib
import OAI.RepresentationTheory.Young.Classification

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.CommutingRestriction
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- The action of a commuting group on the multiplicity space. -/
def homAction (τ : Representation ℂ G V) (σ : Representation ℂ H V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W) :
    Representation ℂ H (ρ.IntertwiningMap τ) where
  toFun h :=
    { toFun f :=
        { toLinearMap := σ h ∘ₗ f.toLinearMap
          isIntertwining' g := by
            rw [LinearMap.comp_assoc,f.isIntertwining',← LinearMap.comp_assoc]
            exact congrArg (fun B : Module.End ℂ V => B ∘ₗ f.toLinearMap) (hc g h).eq.symm }
      map_add' f g := by ext w; simp
      map_smul' c f := by ext w; simp }
  map_one' := by ext f w; simp
  map_mul' h k := by ext f w; simp [map_mul]

@[simp] lemma homAction_apply (τ : Representation ℂ G V) (σ : Representation ℂ H V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (h : H) (f : ρ.IntertwiningMap τ) (w : W) : homAction τ σ hc ρ h f w=σ h (f w) := rfl

def inclusion (τ : Representation ℂ G V) (S : Subrepresentation τ) :
    S.toRepresentation.IntertwiningMap τ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

lemma homAction_fixedSum {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (color : Y → ℕ) (f : ρ.IntertwiningMap τ) (w : W) :
    (YoungCorner.fixedSum color (homAction τ σ hc ρ) f) w=YoungCorner.fixedSum color σ (f w) := by
  simp [YoungCorner.fixedSum,Representation.IntertwiningMap.sum_apply]

lemma homAction_alternatingSum {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (ρ : Representation ℂ G W)
    (color : Y → ℕ) (f : ρ.IntertwiningMap τ) (w : W) :
    (YoungCorner.alternatingSum color (homAction τ σ hc ρ) f) w=
      YoungCorner.alternatingSum color σ (f w) := by
  simp [YoungCorner.alternatingSum,Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply]

lemma sum_intertwine {Y : Type*} [Fintype Y] [DecidableEq Y]
    (τ : Representation ℂ G V) (σ : Representation ℂ (Equiv.Perm Y) V)
    (hc : ∀ g h, Commute (τ g) (σ h)) (f g : Y → ℕ) (x : G) :
    Commute (τ x) (YoungCorner.fixedSum f σ * YoungCorner.alternatingSum g σ) := by
  apply Commute.mul_right
  · apply Commute.sum_right
    intro y hy
    exact hc x y
  · apply Commute.sum_right
    intro y hy
    exact (hc x y).smul_right _

end CoordinateSweeps.CommutingRestriction

namespace CoordinateSweeps.CommutingRestriction
open YoungCorner
variable {X Y V Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup Z] [Module ℂ Z] [FiniteDimensional ℂ Z]

/- Exact multiplicity lower bound from two commuting Young corners for the
removed-hook argument. -/
theorem joint_corner_multiplicity (τ : Representation ℂ (Equiv.Perm X) V)
    (σ : Representation ℂ (Equiv.Perm Y) V) (hc : ∀ g h, Commute (τ g) (σ h))
    (μ ν : YoungDiagram) (t : X ≃ Boxes μ) (u : Y ≃ Boxes ν)
    (δ : Representation ℂ (Equiv.Perm Y) Z) [δ.IsIrreducible] (hδ : hasShape ν u δ)
    (hne : (fixedSum (rowColor t) τ * alternatingSum (colColor t) τ) *
      (fixedSum (rowColor u) σ * alternatingSum (colColor u) σ) ≠ 0) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation ∧
      Module.finrank ℂ Z ≤ Module.finrank ℂ (S.toRepresentation.IntertwiningMap τ) := by
  let A := fixedSum (rowColor t) τ * alternatingSum (colColor t) τ
  let B := fixedSum (rowColor u) σ * alternatingSum (colColor u) σ
  have hAB : Commute A B := by
    apply Commute.mul_left
    · apply Commute.sum_left
      intro g hg
      exact sum_intertwine τ σ hc _ _ g
    · apply Commute.sum_left
      intro g hg
      exact (sum_intertwine τ σ hc _ _ g).smul_left _
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ (A*B) hne
  have hShape : hasShape μ t S.toRepresentation := by
    intro hz
    have hh:=congrArg (fun L : Module.End ℂ S.toSubmodule => (L v : V)) hz
    simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hh
    have hAv : A (v : V)=0 := hh
    apply hv
    rw [hAB.eq]
    simp only [Module.End.mul_apply,hAv,map_zero]
  let υ := homAction τ σ hc S.toRepresentation
  have hν : hasShape ν u υ := by
    intro hz
    have hh:=congrArg (fun L : Module.End ℂ (S.toRepresentation.IntertwiningMap τ) =>
      (L (inclusion τ S)) v) hz
    simp only [υ,Module.End.mul_apply,homAction_fixedSum,homAction_alternatingSum] at hh
    have hBv : B (v : V)=0 := hh
    apply hv
    simp only [Module.End.mul_apply,hBv,map_zero]
  obtain ⟨T,hT,w,hw⟩ := RepDetection.exists_irreducible_detecting υ
    (fixedSum (rowColor u) υ*alternatingSum (colColor u) υ) hν
  have hTshape : hasShape ν u T.toRepresentation := by
    intro hz
    apply hw
    have hh:=congrArg (fun L : Module.End ℂ T.toSubmodule => (L w : S.toRepresentation.IntertwiningMap τ)) hz
    simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hh
    exact hh
  let := hT
  obtain ⟨e⟩ := equiv_of_same_shape δ T.toRepresentation ν u u hδ hTshape
  refine ⟨S,hS,hShape,?_⟩
  rw [e.toLinearEquiv.finrank_eq]
  exact Submodule.finrank_le T.toSubmodule

end CoordinateSweeps.CommutingRestriction

namespace CoordinateSweeps.YoungCorner
variable {X Y Z A : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] [Ring A] [Algebra ℂ A]

lemma signScalar_ne_zero (g : Equiv.Perm X) : signScalar g ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h|h <;> simp [signScalar,h]

lemma fixedSum_absorb (f : X → ℕ) (g : Y → ℕ) (τ : Equiv.Perm X →* A)
    (φ : Equiv.Perm Y →* Equiv.Perm X)
    (hφ : ∀ r : colorStabilizer g, φ r.val ∈ colorStabilizer f) :
    fixedSum f τ * fixedSum g (τ.comp φ)=
      (Fintype.card (colorStabilizer g) : ℂ) • fixedSum f τ := by
  change fixedSum f τ * (∑ r : colorStabilizer g, τ (φ r.val))=_
  rw [Finset.mul_sum]
  have he (r : colorStabilizer g) : fixedSum f τ * τ (φ r.val)=fixedSum f τ :=
    fixedSum_right f τ ⟨φ r.val,hφ r⟩
  simp only [he,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

lemma alternatingSum_absorb (f : X → ℕ) (g : Y → ℕ) (τ : Equiv.Perm X →* A)
    (φ : Equiv.Perm Y →* Equiv.Perm X)
    (hφ : ∀ c : colorStabilizer g, φ c.val ∈ colorStabilizer f)
    (hs : ∀ c : Equiv.Perm Y, signScalar (φ c)=signScalar c) :
    alternatingSum g (τ.comp φ) * alternatingSum f τ=
      (Fintype.card (colorStabilizer g) : ℂ) • alternatingSum f τ := by
  change (∑ c : colorStabilizer g, signScalar c.val • τ (φ c.val))*alternatingSum f τ=_
  rw [Finset.sum_mul]
  have he (c : colorStabilizer g) : (signScalar c.val • τ (φ c.val))*alternatingSum f τ=alternatingSum f τ := by
    rw [smul_mul_assoc,alternatingSum_left f τ ⟨φ c.val,hφ c⟩]
    change signScalar c.val • (signScalar (φ c.val))⁻¹ • alternatingSum f τ=_
    rw [hs,smul_smul,mul_inv_cancel₀ (signScalar_ne_zero _),one_smul]
  simp only [he,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/- A split of the row and column stabilizers preserves a nonzero Young corner. -/
lemma joint_of_full_corner (τ : Equiv.Perm X →* A)
    (fR fC : X → ℕ) (gR gC : Y → ℕ) (hR hC : Z → ℕ)
    (φ : Equiv.Perm Y →* Equiv.Perm X) (ψ : Equiv.Perm Z →* Equiv.Perm X)
    (hφR : ∀ r : colorStabilizer gR, φ r.val ∈ colorStabilizer fR)
    (hφC : ∀ c : colorStabilizer gC, φ c.val ∈ colorStabilizer fC)
    (hψR : ∀ r : colorStabilizer hR, ψ r.val ∈ colorStabilizer fR)
    (hψC : ∀ c : colorStabilizer hC, ψ c.val ∈ colorStabilizer fC)
    (hφs : ∀ g : Equiv.Perm Y, signScalar (φ g)=signScalar g)
    (hψs : ∀ g : Equiv.Perm Z, signScalar (ψ g)=signScalar g)
    (hcomm : ∀ g h, Commute (φ g) (ψ h))
    (hne : fixedSum fR τ * alternatingSum fC τ ≠ 0) :
    (fixedSum gR (τ.comp φ)*alternatingSum gC (τ.comp φ)) *
      (fixedSum hR (τ.comp ψ)*alternatingSum hC (τ.comp ψ)) ≠ 0 := by
  let P : A :=fixedSum fR τ
  let Q : A :=alternatingSum fC τ
  let PR : A :=fixedSum gR (τ.comp φ)
  let QR : A :=alternatingSum gC (τ.comp φ)
  let PC : A :=fixedSum hR (τ.comp ψ)
  let QC : A :=alternatingSum hC (τ.comp ψ)
  let a : ℂ:=Fintype.card (colorStabilizer gR)
  let b : ℂ:=Fintype.card (colorStabilizer hR)
  let c : ℂ:=Fintype.card (colorStabilizer gC)
  let d : ℂ:=Fintype.card (colorStabilizer hC)
  have hP : P*PR=a•P := fixedSum_absorb fR gR τ φ hφR
  have hP' : P*PC=b•P := fixedSum_absorb fR hR τ ψ hψR
  have hQ : QR*Q=c•Q := alternatingSum_absorb fC gC τ φ hφC hφs
  have hQ' : QC*Q=d•Q := alternatingSum_absorb fC hC τ ψ hψC hψs
  have hcross : Commute QR PC := by
    apply Commute.sum_left
    intro g hg
    apply Commute.smul_left
    apply Commute.sum_right
    intro h hh
    exact (hcomm g.val h.val).map τ
  have he : P*((PR*QR)*(PC*QC))*Q=(a*b*d*c) • (P*Q) := by
    calc
      _ = ((P*PR)*PC)*(QR*(QC*Q)) := by
        simp only [mul_assoc]
        rw [← mul_assoc QR PC, hcross.eq]
        simp only [mul_assoc]
      _ = (a*b*d*c) • (P*Q) := by
        rw [hP,smul_mul_assoc,hP',hQ',mul_smul_comm,hQ]
        simp only [smul_smul,smul_mul_assoc,mul_smul_comm]
        congr 1
        ring
  intro hz
  change (PR*QR)*(PC*QC)=0 at hz
  rw [hz,mul_zero,zero_mul] at he
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer gR))
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer hR))
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer gC))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Fintype.card_ne_zero (α := colorStabilizer hC))
  exact (smul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hd) hc) hne) he.symm

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

def hookPart (μ : YoungDiagram) (p : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1<p ∨ x.2<p)
  isLowerSet := by
    intro a b hab hb
    obtain ⟨hμ,hp⟩:=Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨μ.isLowerSet hab hμ,?_⟩
    rcases hp with h|h
    · exact Or.inl (lt_of_le_of_lt hab.1 h)
    · exact Or.inr (lt_of_le_of_lt hab.2 h)

@[simp] lemma mem_hookPart (μ : YoungDiagram) (p : ℕ) (x : ℕ × ℕ) :
    x ∈ hookPart μ p ↔ x ∈ μ ∧ (x.1<p ∨ x.2<p) := by
  exact Finset.mem_filter

def shifted (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := (x.1+p,x.2+p)
lemma shifted_injective (p : ℕ) : Function.Injective (shifted p) := by
  intro x y h
  apply Prod.ext
  · exact Nat.add_right_cancel (congrArg Prod.fst h)
  · exact Nat.add_right_cancel (congrArg Prod.snd h)

def removedPart (μ : YoungDiagram) (p : ℕ) : YoungDiagram where
  cells := μ.cells.preimage (shifted p) (shifted_injective p).injOn
  isLowerSet := by
    intro a b hab hb
    apply Finset.mem_preimage.mpr
    apply μ.isLowerSet (show shifted p b ≤ shifted p a from ⟨Nat.add_le_add_right hab.1 p,Nat.add_le_add_right hab.2 p⟩)
    exact Finset.mem_preimage.mp hb

@[simp] lemma mem_removedPart (μ : YoungDiagram) (p : ℕ) (x : ℕ × ℕ) :
    x ∈ removedPart μ p ↔ shifted p x ∈ μ := by
  change x ∈ μ.cells.preimage (shifted p) (shifted_injective p).injOn ↔ _
  exact Finset.mem_preimage

def boxesSplit (μ : YoungDiagram) (p : ℕ) :
    Boxes (hookPart μ p) ⊕ Boxes (removedPart μ p) ≃ Boxes μ where
  toFun x := match x with
    | Sum.inl x => ⟨x.val,(mem_hookPart μ p x.val).mp x.property |>.1⟩
    | Sum.inr x => ⟨shifted p x.val,(mem_removedPart μ p x.val).mp x.property⟩
  invFun x := if h : x.val.1<p ∨ x.val.2<p then
    Sum.inl ⟨x.val,(mem_hookPart μ p x.val).mpr ⟨x.property,h⟩⟩ else
    Sum.inr ⟨(x.val.1-p,x.val.2-p),(mem_removedPart μ p _).mpr (by
      have hx : p≤x.val.1 ∧ p≤x.val.2 := by push Not at h; exact h
      simp [shifted,Nat.sub_add_cancel hx.1,Nat.sub_add_cancel hx.2])⟩
  left_inv := by
    intro x
    cases x with
    | inl x =>
      have hx: x.val.1<p ∨ x.val.2<p := ((mem_hookPart μ p x.val).mp x.property).2
      simp only [dite_eq_left hx]
    | inr x =>
      simp [shifted]
  right_inv := by
    intro x
    dsimp
    split_ifs with h
    · rfl
    · apply Subtype.ext
      have hx : p≤x.val.1 ∧ p≤x.val.2 := by push Not at h; exact h
      simp [shifted,Nat.sub_add_cancel hx.1,Nat.sub_add_cancel hx.2]

@[simp] lemma boxesSplit_inl (μ : YoungDiagram) (p : ℕ) (x : Boxes (hookPart μ p)) :
    (boxesSplit μ p (Sum.inl x)).val=x.val := rfl
@[simp] lemma boxesSplit_inr (μ : YoungDiagram) (p : ℕ) (x : Boxes (removedPart μ p)) :
    (boxesSplit μ p (Sum.inr x)).val=shifted p x.val := rfl

variable {X Y Z : Type*}

def leftPerm (e : Y ⊕ Z ≃ X) : Equiv.Perm Y →* Equiv.Perm X where
  toFun g := e.permCongr (Equiv.sumCongr g (Equiv.refl Z))
  map_one' := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]

def rightPerm (e : Y ⊕ Z ≃ X) : Equiv.Perm Z →* Equiv.Perm X where
  toFun g := e.permCongr (Equiv.sumCongr (Equiv.refl Y) g)
  map_one' := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]
  map_mul' g h := by
    ext x
    obtain ⟨y,rfl⟩:=e.surjective x
    cases y <;> simp [Equiv.permCongr_apply]

@[simp] lemma leftPerm_inl (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (x : Y) :
    leftPerm e g (e (Sum.inl x))=e (Sum.inl (g x)) := by simp [leftPerm,Equiv.permCongr_apply]
@[simp] lemma leftPerm_inr (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (x : Z) :
    leftPerm e g (e (Sum.inr x))=e (Sum.inr x) := by simp [leftPerm,Equiv.permCongr_apply]
@[simp] lemma rightPerm_inl (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) (x : Y) :
    rightPerm e g (e (Sum.inl x))=e (Sum.inl x) := by simp [rightPerm,Equiv.permCongr_apply]
@[simp] lemma rightPerm_inr (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) (x : Z) :
    rightPerm e g (e (Sum.inr x))=e (Sum.inr (g x)) := by simp [rightPerm,Equiv.permCongr_apply]

lemma splitPerm_commute (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) (h : Equiv.Perm Z) :
    Commute (leftPerm e g) (rightPerm e h) := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩:=e.surjective x
  cases y <;> simp

lemma leftPerm_rows (μ : YoungDiagram) (p : ℕ) (r : rows (hookPart μ p)) :
    leftPerm (boxesSplit μ p) r.val ∈ rows μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simpa only [leftPerm_inl,boxesSplit_inl] using r.property y
  | inr y => simp only [leftPerm_inr]

lemma leftPerm_cols (μ : YoungDiagram) (p : ℕ) (c : cols (hookPart μ p)) :
    leftPerm (boxesSplit μ p) c.val ∈ cols μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simpa only [leftPerm_inl,boxesSplit_inl] using c.property y
  | inr y => simp only [leftPerm_inr]

lemma rightPerm_rows (μ : YoungDiagram) (p : ℕ) (r : rows (removedPart μ p)) :
    rightPerm (boxesSplit μ p) r.val ∈ rows μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simp only [rightPerm_inl]
  | inr y => simpa only [rightPerm_inr,boxesSplit_inr,shifted] using congrArg (·+p) (r.property y)

lemma rightPerm_cols (μ : YoungDiagram) (p : ℕ) (c : cols (removedPart μ p)) :
    rightPerm (boxesSplit μ p) c.val ∈ cols μ := by
  intro x
  obtain ⟨y,rfl⟩:=(boxesSplit μ p).surjective x
  cases y with
  | inl y => simp only [rightPerm_inl]
  | inr y => simpa only [rightPerm_inr,boxesSplit_inr,shifted] using congrArg (·+p) (c.property y)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner

lemma rectangle_card_le (μ : YoungDiagram) (x : Boxes μ) :
    (x.val.1+1)*(x.val.2+1)≤Fintype.card (Boxes μ) := by
  let f (a : Fin (x.val.1+1) × Fin (x.val.2+1)) : Boxes μ :=
    ⟨(a.1.val,a.2.val),μ.up_left_mem (Nat.le_of_lt_succ a.1.isLt) (Nat.le_of_lt_succ a.2.isLt) x.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z : Boxes μ => z.val.1) he
    · exact congrArg (fun z : Boxes μ => z.val.2) he
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma removedPart_rank_lt (μ : YoungDiagram) (p : ℕ) (x : Boxes (removedPart μ p)) :
    x.val.1+x.val.2 < 2*(Fintype.card (Boxes μ)/(p+1)) := by
  have hr:=rectangle_card_le μ ⟨shifted p x.val,(mem_removedPart μ p _).mp x.property⟩
  change (x.val.1+p+1)*(x.val.2+p+1)≤Fintype.card (Boxes μ) at hr
  have h₁ : (x.val.1+1)*(p+1)≤Fintype.card (Boxes μ) := by
    apply le_trans _ hr
    apply Nat.mul_le_mul <;> omega
  have h₂ : (x.val.2+1)*(p+1)≤Fintype.card (Boxes μ) := by
    rw [Nat.mul_comm] at hr
    apply le_trans _ hr
    apply Nat.mul_le_mul <;> omega
  have h₁' := (Nat.le_div_iff_mul_le (by omega : 0<p+1)).mpr h₁
  have h₂' := (Nat.le_div_iff_mul_le (by omega : 0<p+1)).mpr h₂
  omega

lemma hookPart_property (μ : YoungDiagram) (p : ℕ) (x : Boxes (hookPart μ p)) :
    x.val.1<p ∨ x.val.2<p := ((mem_hookPart μ p x.val).mp x.property).2

lemma split_card (μ : YoungDiagram) (p : ℕ) :
    Fintype.card (Boxes (hookPart μ p))+Fintype.card (Boxes (removedPart μ p))=
      Fintype.card (Boxes μ) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (boxesSplit μ p)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

lemma signScalar_leftPerm (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Y) :
    signScalar (leftPerm e g)=signScalar g := by
  simp [signScalar,leftPerm,Equiv.Perm.sign_permCongr,Equiv.Perm.sign_sumCongr]

lemma signScalar_rightPerm (e : Y ⊕ Z ≃ X) (g : Equiv.Perm Z) :
    signScalar (rightPerm e g)=signScalar g := by
  simp [signScalar,rightPerm,Equiv.Perm.sign_permCongr,Equiv.Perm.sign_sumCongr]

lemma hook_removed_joint {A : Type*} [Ring A] [Algebra ℂ A]
    (μ : YoungDiagram) (p : ℕ) (τ : Equiv.Perm (Boxes μ) →* A)
    (hμ : fixedSum (fun x : Boxes μ => x.val.1) τ * alternatingSum (fun x : Boxes μ => x.val.2) τ ≠ 0) :
    (fixedSum (fun x : Boxes (hookPart μ p) => x.val.1) (τ.comp (leftPerm (boxesSplit μ p))) *
      alternatingSum (fun x : Boxes (hookPart μ p) => x.val.2) (τ.comp (leftPerm (boxesSplit μ p)))) *
    (fixedSum (fun x : Boxes (removedPart μ p) => x.val.1) (τ.comp (rightPerm (boxesSplit μ p))) *
      alternatingSum (fun x : Boxes (removedPart μ p) => x.val.2) (τ.comp (rightPerm (boxesSplit μ p)))) ≠ 0 :=
  joint_of_full_corner τ _ _ _ _ _ _ _ _
    (leftPerm_rows μ p) (leftPerm_cols μ p) (rightPerm_rows μ p) (rightPerm_cols μ p)
    (signScalar_leftPerm _) (signScalar_rightPerm _) (splitPerm_commute _) hμ

/- Retained-hook multiplicity for the hook part and translated removed partition. -/
theorem hook_removed_multiplicity {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (μ : YoungDiagram) (p : ℕ) (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V)
    (hτ : hasShape μ (Equiv.refl _) τ)
    (δ : Representation ℂ (Equiv.Perm (Boxes (removedPart μ p))) W) [δ.IsIrreducible]
    (hδ : hasShape (removedPart μ p) (Equiv.refl _) δ) :
    ∃ S : Subrepresentation (τ.comp (leftPerm (boxesSplit μ p))),
      S.toRepresentation.IsIrreducible ∧ hasShape (hookPart μ p) (Equiv.refl _) S.toRepresentation ∧
      Module.finrank ℂ W ≤ Module.finrank ℂ
        (S.toRepresentation.IntertwiningMap (τ.comp (leftPerm (boxesSplit μ p)))) := by
  apply CommutingRestriction.joint_corner_multiplicity
    (τ.comp (leftPerm (boxesSplit μ p))) (τ.comp (rightPerm (boxesSplit μ p)))
    (fun g h => (splitPerm_commute (boxesSplit μ p) g h).map τ)
    (hookPart μ p) (removedPart μ p) (Equiv.refl _) (Equiv.refl _) δ hδ
  exact hook_removed_joint μ p τ hτ

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
lemma leftPerm_range_of_fix_right (e : Y ⊕ Z ≃ X) (g : Equiv.Perm X)
    (hfix : ∀ z, g (e (Sum.inr z))=e (Sum.inr z)) : ∃ h, leftPerm e h=g := by
  let g' := e.permCongr.symm g
  have hf (z : Z) : g' (Sum.inr z)=Sum.inr z := by
    change e.symm (g (e (Sum.inr z)))=Sum.inr z
    rw [hfix,Equiv.symm_apply_apply]
  have hmaps : Set.MapsTo g' (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro x ⟨z,rfl⟩
    exact ⟨z,(hf z).symm⟩
  have hm:=Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr g').mpr hmaps)
  obtain ⟨⟨h,k⟩,he⟩:=hm
  have hk : k=1 := by
    apply Equiv.ext
    intro z
    have hh:=congrArg (fun q : Equiv.Perm (Y ⊕ Z) => q (Sum.inr z)) he
    simpa only [Equiv.Perm.sumCongrHom_apply,Equiv.sumCongr_apply,Sum.map_inr,hf,Sum.inr.injEq,Equiv.Perm.one_apply] using hh
  refine ⟨h,?_⟩
  subst k
  change e.permCongr (Equiv.sumCongr h (Equiv.refl Z))=g
  calc
    _ = e.permCongr g' := congrArg e.permCongr he
    _ = g := e.permCongr.apply_symm_apply g

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.RestrictionBound
variable {Ω I V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [Fintype Ω] [DecidableEq Ω] [FiniteDimensional ℂ V] in
lemma orbit_span_top (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (v : V) (hv : v ≠ 0) : Submodule.span ℂ (Set.range (fun g => ρ g v))=⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k,rfl⟩:=hw
          apply Submodule.subset_span
          exact ⟨g*k,by simp only [map_mul,Module.End.mul_apply]⟩
        | zero => simp
        | add x y hx hy ix iy => simpa only [map_add] using Submodule.add_mem _ ix iy
        | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih }
  have hn : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := Submodule.subset_span ⟨1,by simp⟩
    rw [he] at hm
    exact hv hm
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top S).resolve_left hn)

/- A pointwise-stabilizer constituent generates at most n^k copies of its
vector space. This is the exact logarithmic dimension upper bound in06:eq22. -/
theorem dimension_le_pow_mul (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (a : I → Ω) (W : Submodule ℂ V) (hW : W ≠ ⊥)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ i, g (a i)=a i) → ∀ w ∈ W, ρ g w ∈ W) :
    Module.finrank ℂ V ≤ (Fintype.card Ω)^(Fintype.card I)*Module.finrank ℂ W := by
  classical
  have hn : ∃ v ∈ W, v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hW
    apply bot_unique
    intro v hv
    exact hh v hv
  obtain ⟨v,hvW,hv⟩:=hn
  let restrict (g : Equiv.Perm Ω) : I → Ω := fun i => g (a i)
  let chooseG (x : I → Ω) : Equiv.Perm Ω := if hx : ∃ g, restrict g=x then hx.choose else 1
  have hchoose (g : Equiv.Perm Ω) : restrict (chooseG (restrict g))=restrict g := by
    simp only [chooseG,dite_eq_left (show ∃ t, restrict t=restrict g from ⟨g,rfl⟩)]
    exact Exists.choose_spec (show ∃ t, restrict t=restrict g from ⟨g,rfl⟩)
  let b := Module.finBasis ℂ W
  let u (x : (I → Ω) × Fin (Module.finrank ℂ W)) : V := ρ (chooseG x.1) (b x.2).val
  have hspan : Submodule.span ℂ (Set.range u)=⊤ := by
    rw [eq_top_iff,← orbit_span_top ρ v hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    let r:=chooseG (restrict g)
    have hfix : ∀ i, (r⁻¹*g) (a i)=a i := by
      intro i
      have he:=congrFun (hchoose g) i
      change r (a i)=g (a i) at he
      simp only [Equiv.Perm.mul_apply]
      rw [← he]
      simp
    let w : W := ⟨ρ (r⁻¹*g) v,hstable _ hfix _ hvW⟩
    have he : ρ g v=ρ r w.val := by
      change ρ g v=ρ r (ρ (r⁻¹*g) v)
      rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel_left]
    change ρ g v ∈ Submodule.span ℂ (Set.range u)
    rw [he,← b.sum_repr w]
    simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(restrict g,i),rfl⟩
  have hd:=finrank_le_of_span_eq_top hspan
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hd

end CoordinateSweeps.RestrictionBound

namespace CoordinateSweeps.YoungCorner
/- The retained hook gives a dimension upper bound (source06:eq22). -/
theorem hook_dimension_upper {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (μ : YoungDiagram) (p : ℕ)
    (τ : Representation ℂ (Equiv.Perm (Boxes μ)) V) [τ.IsIrreducible]
    (S : Subrepresentation (τ.comp (leftPerm (boxesSplit μ p)))) (hS : S ≠ ⊥) :
    Module.finrank ℂ V ≤ (Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p))) *
      Module.finrank ℂ S.toSubmodule := by
  apply RestrictionBound.dimension_le_pow_mul τ
    (fun z => boxesSplit μ p (Sum.inr z)) S.toSubmodule
  · intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  · intro g hg w hw
    obtain ⟨f,rfl⟩ := leftPerm_range_of_fix_right (boxesSplit μ p) g hg
    exact S.apply_mem_toSubmodule f hw
end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {X Y V : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup V] [Module ℂ V]
def colorEquiv (e : X ≃ Y) (f : Y → ℕ) : colorStabilizer (fun x => f (e x)) ≃* colorStabilizer f where
  toFun g := ⟨e.permCongrHom g.val,by
    intro y
    simpa using g.property (e.symm y)⟩
  invFun g := ⟨e.symm.permCongrHom g.val,by
    intro x
    simpa using g.property (e x)⟩
  left_inv g := by apply Subtype.ext; apply Equiv.ext; intro x; simp
  right_inv g := by apply Subtype.ext; apply Equiv.ext; intro y; simp
  map_mul' g h := by apply Subtype.ext; exact map_mul e.permCongrHom g.val h.val
lemma fixedSum_reparam (e : X ≃ Y) (f : Y → ℕ) (τ : Representation ℂ (Equiv.Perm Y) V) :
    fixedSum (fun x => f (e x)) (τ.comp e.permCongrHom)=fixedSum f τ := by
  exact Fintype.sum_equiv (colorEquiv e f).toEquiv _ _ (fun _ => rfl)
lemma alternatingSum_reparam (e : X ≃ Y) (f : Y → ℕ) (τ : Representation ℂ (Equiv.Perm Y) V) :
    alternatingSum (fun x => f (e x)) (τ.comp e.permCongrHom)=alternatingSum f τ := by
  apply Fintype.sum_equiv (colorEquiv e f).toEquiv
  intro g
  change signScalar g.val • τ (e.permCongrHom g.val)=signScalar (e.permCongrHom g.val) • τ (e.permCongrHom g.val)
  congr 1
  simp [signScalar]
lemma hasShape_reparam (μ : YoungDiagram) (e : X ≃ Y) (t : Y ≃ Boxes μ)
    (τ : Representation ℂ (Equiv.Perm Y) V) :
    hasShape μ (e.trans t) (τ.comp e.permCongrHom) ↔ hasShape μ t τ := by
  unfold hasShape
  change fixedSum (fun x => rowColor t (e x)) (τ.comp e.permCongrHom)*
      alternatingSum (fun x => colColor t (e x)) (τ.comp e.permCongrHom) ≠ 0 ↔ _
  rw [fixedSum_reparam,alternatingSum_reparam]
end CoordinateSweeps.YoungCorner

namespace Representation.IntertwiningMap
open scoped _root_.Representation _root_.Representation.IntertwiningMap
variable {Γ Λ V W : Type*} [Monoid Γ] [Monoid Λ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
/- Reparameterizing a group does not alter the Hom multiplicity. -/
def reparamEquiv (ρ : Representation ℂ Γ V) (τ : Representation ℂ Γ W) (e : Λ ≃* Γ) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom) where
  toFun f := ⟨f.toLinearMap,fun g => f.isIntertwining' (e g)⟩
  invFun f := ⟨f.toLinearMap,fun g => by
    have h := f.isIntertwining' (e.symm g)
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using h⟩
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/- Changing the source realization by an equivalence preserves Hom. -/
def sourceEquiv {U : Type*} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ U}
    (e : Representation.Equiv ρ σ) (τ : Representation ℂ Γ W) :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] σ.IntertwiningMap τ where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl
end Representation.IntertwiningMap

end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI

import Mathlib
import OAI.RingTheory.Multiplicity.FiniteModuleCech

namespace OAI

noncomputable section
namespace Lech.CarrierOperators
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]

structure Carrier (ι : Type) where
  Index : Type
  support : Index → Finset ι

variable (A B C : Carrier ι)

def Agree (M : Type u) (S : Finset ι) (f g : A.Index → M) : Prop :=
  ∀ a,A.support a⊆S → f a=g a

structure Op where
  app : ∀ M : ModuleCat.{u} R, (A.Index → M) →ₗ[R] (B.Index → M)
  natural : ∀ {M N : ModuleCat.{u} R} (l : M →ₗ[R] N) (f : A.Index → M),
    app N (l ∘ f)=l ∘ app M f
  locality : ∀ (M : ModuleCat.{u} R) (S : Finset ι) (f g : A.Index → M),
    Agree A M S f g → Agree B M S (app M f) (app M g)

variable {A B C}

def Op.id (A : Carrier ι) : Op (R:=R) A A where
  app _ := LinearMap.id
  natural _ _ := rfl
  locality _ _ _ _ h := h

def Op.comp (Q : Op (R:=R) B C) (P : Op (R:=R) A B) : Op (R:=R) A C where
  app M := (Q.app M).comp (P.app M)
  natural l f := by change Q.app _ (P.app _ (l ∘ f))=_; rw [P.natural,Q.natural]; rfl
  locality M S f g h := Q.locality M S _ _ (P.locality M S f g h)

def Op.add (P Q : Op (R:=R) A B) : Op (R:=R) A B where
  app M := P.app M+Q.app M
  natural l f := by
    ext b
    change P.app _ (l ∘ f) b+Q.app _ (l ∘ f) b=l (P.app _ f b+Q.app _ f b)
    rw [P.natural,Q.natural,map_add]
    rfl
  locality M S f g h b hb := by
    change P.app M f b+Q.app M f b=P.app M g b+Q.app M g b
    rw [P.locality M S f g h b hb,Q.locality M S f g h b hb]

def Op.sub (P Q : Op (R:=R) A B) : Op (R:=R) A B where
  app M := P.app M-Q.app M
  natural l f := by
    ext b
    change P.app _ (l ∘ f) b-Q.app _ (l ∘ f) b=l (P.app _ f b-Q.app _ f b)
    rw [P.natural,Q.natural,map_sub]
    rfl
  locality M S f g h b hb := by
    change P.app M f b-Q.app M f b=P.app M g b-Q.app M g b
    rw [P.locality M S f g h b hb,Q.locality M S f g h b hb]

variable (D : FiniteModuleCech.Diagram R ι)
abbrev Sections (A : Carrier ι) := ∀ a : A.Index,D.obj (A.support a)

def toFixed (A : Carrier ι) (S : Finset ι) : Sections D A →ₗ[R] (A.Index → D.obj S) where
  toFun f a := if ha : A.support a⊆S then (D.res ha).hom (f a) else 0
  map_add' f g := by
    funext a
    split_ifs with h <;> simp [h]
  map_smul' r f := by
    funext a
    split_ifs with h <;> simp [h]

lemma toFixed_self (A : Carrier ι) (f : Sections D A) (a : A.Index) :
    toFixed D A (A.support a) f a=f a := by
  change (if ha : A.support a⊆A.support a then (D.res ha).hom (f a) else 0)=f a
  rw [dite_eq_left (Finset.Subset.refl _),D.res_self]
  rfl

lemma toFixed_restrict (A : Carrier ι) {S T : Finset ι} (hST : S⊆T) (f : Sections D A) :
    Agree A (D.obj T) S (toFixed D A T f) ((D.res hST).hom ∘ toFixed D A S f) := by
  intro a ha
  change (if ht : A.support a⊆T then _ else _) =
    (D.res hST).hom (if hs : A.support a⊆S then _ else _)
  rw [dite_eq_left (ha.trans hST),dite_eq_left ha]
  exact congrArg (fun g : D.obj (A.support a) ⟶ D.obj T => g.hom (f a)) (D.res_comp ha hST).symm

 
def lift (P : Op (R:=R) A B) : Sections D A →ₗ[R] Sections D B :=
  LinearMap.pi (fun b => (LinearMap.proj b).comp
    ((P.app (D.obj (B.support b))).comp (toFixed D A (B.support b))))

lemma toFixed_lift (P : Op (R:=R) A B) (S : Finset ι) (f : Sections D A) :
    Agree B (D.obj S) S (toFixed D B S (lift D P f)) (P.app (D.obj S) (toFixed D A S f)) := by
  intro b hb
  change (if hb : B.support b⊆S then _ else _) = _
  rw [dite_eq_left hb]
  change (D.res hb).hom (P.app (D.obj (B.support b)) (toFixed D A (B.support b) f) b)=_
  have he := P.locality (D.obj S) (B.support b) _ _ (toFixed_restrict D A hb f) b (Finset.Subset.refl _)
  rw [P.natural] at he
  exact he.symm

lemma lift_comp (Q : Op (R:=R) B C) (P : Op (R:=R) A B) :
    lift D (Q.comp P)=(lift D Q).comp (lift D P) := by
  apply LinearMap.ext
  intro f
  funext c
  exact (Q.locality (D.obj (C.support c)) (C.support c) _ _ (toFixed_lift D P _ f)
    c (Finset.Subset.refl _)).symm

lemma lift_id (A : Carrier ι) : lift D (Op.id A)=LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext a
  exact toFixed_self D A f a

lemma lift_add (P Q : Op (R:=R) A B) : lift D (P.add Q)=lift D P+lift D Q := rfl
lemma lift_sub (P Q : Op (R:=R) A B) : lift D (P.sub Q)=lift D P-lift D Q := rfl

lemma lift_congr {P Q : Op (R:=R) A B} (h : ∀ M,P.app M=Q.app M) : lift D P=lift D Q := by
  apply LinearMap.ext
  intro f
  funext b
  change P.app (D.obj (B.support b)) (toFixed D A (B.support b) f) b=_
  rw [h]
  rfl
end Lech.CarrierOperators

end

end OAI

import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverAllowedEmpty

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set
open AlternatingCech
universe u
variable (R : Type u) [CommRing R] (ι : Type) [Fintype ι] [LinearOrder ι]

 

structure Diagram where
  obj : Finset ι → ModuleCat.{u} R
  res : ∀ {s t : Finset ι}, s ⊆ t → (obj s ⟶ obj t)
  res_self : ∀ s, res (Finset.Subset.refl s) = 𝟙 (obj s)
  res_comp : ∀ {s t v : Finset ι} (hst : s ⊆ t) (htv : t ⊆ v),
    res hst ≫ res htv = res (hst.trans htv)

variable {R ι}
variable (D : Diagram R ι)
abbrev cochains (n : ℕ) := ∀ s : powersetCard ι n, D.obj s.val

def d (n : ℕ) : cochains D n →ₗ[R] cochains D (n+1) where
  toFun f s := ∑ i : Fin (n+1), (-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

 

lemma raw_square (N : Type u) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : powersetCard ι n → N) :
    rawDelta R N (n+1) (rawDelta R N n f) = 0 := by
  have he := sortedDelta_square R N (fun _ : Finset ι => ⊤) (fun _ _ _ => le_rfl) n
    (fun s => (⟨f s,Submodule.mem_top⟩ : (⊤ : Submodule R N)))
  funext s
  have hh := congrArg (fun g => (g s : N)) he
  simpa only [sortedDelta,rawDelta,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sum,
    Submodule.coe_smul_of_tower,Submodule.coe_zero,Pi.zero_apply,Submodule.inclusion_apply] using hh

 

def toFixed (S : Finset ι) (n : ℕ) (f : cochains D n) : powersetCard ι n → D.obj S :=
  fun t => if ht : t.val ⊆ S then (D.res ht).hom (f t) else 0

omit [Fintype ι] in
lemma toFixed_d (S : Finset ι) (n : ℕ) (f : cochains D n)
    (t : powersetCard ι (n+1)) (ht : t.val ⊆ S) :
    rawDelta R (D.obj S) n (toFixed D S n f) t = (D.res ht).hom (d D n f t) := by
  change (∑ i : Fin (n+1), (-1:ℤ)^i.val • toFixed D S n f (delete t i)) =
    (D.res ht).hom (∑ i : Fin (n+1), (-1:ℤ)^i.val •
      (D.res (delete_subset t i)).hom (f (delete t i)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  rw [toFixed,dite_eq_left ((delete_subset t i).trans ht)]
  exact congrArg (fun φ : D.obj (delete t i).val ⟶ D.obj S => φ.hom (f (delete t i)))
    (D.res_comp (delete_subset t i) ht).symm

lemma d_square (n : ℕ) (f : cochains D n) : d D (n+1) (d D n f) = 0 := by
  funext s
  calc
    d D (n+1) (d D n f) s =
      rawDelta R (D.obj s.val) (n+1)
        (rawDelta R (D.obj s.val) n (toFixed D s.val n f)) s := by
      change (∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (D.res (delete_subset s i)).hom (d D n f (delete s i))) =
        ∑ i : Fin (n+2), (-1:ℤ)^i.val •
          rawDelta R (D.obj s.val) n (toFixed D s.val n f) (delete s i)
      apply Finset.sum_congr rfl
      intro i _
      rw [toFixed_d D _ _ _ _ (delete_subset s i)]
    _ = 0 := congrFun (raw_square (R:=R) (ι:=ι) (D.obj s.val) n (toFixed D s.val n f)) s

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains D n))
    (fun n => ModuleCat.ofHom (d D n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact d_square D n)

lemma complex_d (n : ℕ) : (complex D).d n (n+1) = ModuleCat.ofHom (d D n) := by
  unfold complex
  exact CochainComplex.of_d (fun j => ModuleCat.of R (cochains D j))
    (fun j => ModuleCat.ofHom (d D j)) n

lemma bounded (n : ℕ) (hn : Fintype.card ι < n) : IsZero ((complex D).X n) := by
  have : Subsingleton (cochains D n) := ⟨fun f g => funext fun s => by
    have hs : s.val.card = n := s.property
    have hl := Finset.card_le_univ s.val
    omega⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (cochains D n))

variable {D} {E : Diagram R ι}
 
structure Map (D E : Diagram R ι) where
  app : ∀ s, D.obj s ⟶ E.obj s
  naturality : ∀ {s t : Finset ι} (hst : s ⊆ t), D.res hst ≫ app t = app s ≫ E.res hst

namespace Map
variable (φ : Map D E)
def cochains (n : ℕ) : FiniteModuleCech.cochains D n →ₗ[R] FiniteModuleCech.cochains E n where
  toFun f s := (φ.app s.val).hom (f s)
  map_add' _ _ := by funext s; exact map_add _ _ _
  map_smul' _ _ := by funext s; exact map_smul _ _ _
omit [Fintype ι] in
lemma cochains_d (n : ℕ) (f : FiniteModuleCech.cochains D n) :
    cochains φ (n+1) (d D n f) = d E n (cochains φ n f) := by
  funext s
  change (φ.app s.val).hom (∑ i : Fin (n+1), (-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i))) = _
  rw [map_sum]
  change (∑ i : Fin (n+1), (φ.app s.val).hom ((-1:ℤ)^i.val •
    (D.res (delete_subset s i)).hom (f (delete s i)))) =
    ∑ i : Fin (n+1), (-1:ℤ)^i.val •
      (E.res (delete_subset s i)).hom ((φ.app (delete s i).val).hom (f (delete s i)))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact congrArg (fun ψ : D.obj (delete s i).val ⟶ E.obj s.val => ψ.hom (f (delete s i)))
    (φ.naturality (delete_subset s i))
def complex : FiniteModuleCech.complex D ⟶ FiniteModuleCech.complex E :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (cochains φ n)) (fun n => by
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (cochains_d φ n f).symm)
end Map
end Lech.FiniteModuleCech

end

end OAI

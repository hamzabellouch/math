import Mathlib
import OAI.RingTheory.Multiplicity.StandardFactorChartsL

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u

abbrev PowerIndex : ℕ → Type
  | 0 => Unit
  | n+1 => Fin (n+1) × PowerIndex n

def powerMonomial {S : Type*} [CommMonoid S] :
    (n : ℕ) → (Fin n → S) → PowerIndex n → S
  | 0,_,_ => 1
  | n+1,rs,e => rs 0 ^ e.1.val * powerMonomial n (fun i => rs i.succ) e.2

lemma map_powerMonomial {S T : Type*} [CommMonoid S] [CommMonoid T]
    (φ : S →* T) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    φ (powerMonomial n rs e)=powerMonomial n (fun i => φ (rs i)) e := by
  induction n with
  | zero => exact map_one φ
  | succ n ih =>
      simp only [powerMonomial,map_mul,map_pow]
      rw [ih]

theorem exists_power_data (n : ℕ) : ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (f : R[X]), f.Monic → f.natDegree=n → ∃ d : Data R n f, ∃ b : Module.Basis (PowerIndex n) R d.S,
      ∀ e, b e=powerMonomial n d.roots e := by
  induction n with
  | zero =>
    intro R _ _ f hf hn
    have hf1 : f=1 := hf.natDegree_eq_zero.mp hn
    refine ⟨{
      S := R
      basis := Module.Basis.singleton (Fin 1) R
      roots := Fin.elim0
      factorization := by simp [hf1]
      universal := by
        intro T _ _ xs _
        refine ⟨Algebra.ofId R T, fun i => Fin.elim0 i, ?_⟩
        intro φ _
        ext },Module.Basis.singleton Unit R,?_⟩
    intro e
    simp [powerMonomial, Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ _ f hf hn
    let B := AdjoinRoot f
    let b : Module.Basis (Fin (n+1)) R B :=
      (AdjoinRoot.powerBasisAux' hf).reindex (finCongr hn)
    let : Nontrivial B := b.repr.symm.injective.nontrivial
    let g : B[X] := f.map (algebraMap R B) /ₘ (X-C (AdjoinRoot.root f))
    have hfac : f.map (algebraMap R B) = (X-C (AdjoinRoot.root f))*g := by
      apply Eq.symm
      exact (mul_divByMonic_eq_iff_isRoot).mpr (AdjoinRoot.isRoot_root f)
    have hg : g.Monic := (monic_X_sub_C _).of_mul_monic_left (hfac ▸ hf.map _)
    have hdeg : g.natDegree=n := by
      rw [show g = _ from rfl, natDegree_divByMonic _ (monic_X_sub_C _),
        hf.natDegree_map, natDegree_X_sub_C, hn]
      omega
    obtain ⟨d,bd,hbd⟩ := ih B g hg hdeg
    let : Algebra R d.S := ((algebraMap B d.S).comp (algebraMap R B)).toAlgebra
    let : IsScalarTower R B d.S := IsScalarTower.of_algebraMap_eq fun r => rfl
    let bb : Module.Basis (Fin (n+1) × Fin n.factorial) R d.S := b.smulTower d.basis
    let c : Module.Basis (Fin (n+1).factorial) R d.S :=
      bb.reindex (finProdFinEquiv.trans (finCongr (Nat.factorial_succ n).symm))
    let rs : Fin (n+1) → d.S := Fin.cons
      (algebraMap B d.S (AdjoinRoot.root f)) d.roots
    refine ⟨{
      S := d.S
      basis := c
      roots := rs
      factorization := ?_
      universal := ?_ },b.smulTower bd,?_⟩
    · have hmap := congrArg (Polynomial.map (algebraMap B d.S)) hfac
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, d.factorization] at hmap
      simpa [rs, Fin.prod_univ_succ, Polynomial.map_map,
        IsScalarTower.algebraMap_eq R B d.S] using hmap

    · intro T _ _ xs hxs
      have hx0 : f.eval₂ (algebraMap R T) (xs 0)=0 := by
        rw [← Polynomial.eval_map, hxs, Fin.prod_univ_succ]
        simp
      let β : B →ₐ[R] T := AdjoinRoot.liftAlgHom f (Algebra.ofId R T) (xs 0) hx0
      have hβ : β (AdjoinRoot.root f)=xs 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      let : Algebra B T := β.toRingHom.toAlgebra
      let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r => (β.commutes r).symm
      have hgxs : g.map (algebraMap B T)=∏ i : Fin n, (X-C (xs i.succ)) := by
        apply (monic_X_sub_C (xs 0)).isRegular.left
        have hmap := congrArg (Polynomial.map β.toRingHom) hfac
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, show β.toRingHom (AdjoinRoot.root f)=xs 0 from hβ] at hmap
        have heq : (f.map (algebraMap R B)).map β.toRingHom =
            f.map (algebraMap R T) := by
          rw [Polynomial.map_map]
          congr 1
          exact β.comp_algebraMap
        rw [heq, hxs, Fin.prod_univ_succ] at hmap
        exact hmap.symm
      obtain ⟨φ, hφ, huniq⟩ := d.universal T (fun i => xs i.succ) hgxs
      refine ⟨φ.restrictScalars R, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change φ (algebraMap B d.S (AdjoinRoot.root f))=xs 0
          rw [φ.commutes]
          exact hβ
        · exact hφ j
      · intro ψ hψ
        have hc : ψ.toRingHom.comp (algebraMap B d.S)=β.toRingHom := by
          apply AdjoinRoot.ringHom_ext
          · ext r
            change ψ ((algebraMap B d.S) ((algebraMap R B) r))=β ((algebraMap R B) r)
            rw [← IsScalarTower.algebraMap_apply R B d.S, ψ.commutes, β.commutes]
          · change ψ (algebraMap B d.S (AdjoinRoot.root f))=β (AdjoinRoot.root f)
            rw [hβ]
            exact hψ 0
        let ψB : d.S →ₐ[B] T := {
          toRingHom := ψ.toRingHom
          commutes' := fun b => DFunLike.congr_fun hc b }
        have hψB : ψB=φ := huniq ψB (fun i => hψ i.succ)
        ext x
        exact DFunLike.congr_fun hψB x

    · intro e
      change (b.smulTower bd) e =
        (algebraMap B d.S (AdjoinRoot.root f))^e.1.val * powerMonomial n d.roots e.2
      rw [Module.Basis.smulTower_apply,hbd]
      have hb (i : Fin (n+1)) : b i=(AdjoinRoot.root f)^i.val := by
        dsimp only [b]
        rw [Module.Basis.reindex_apply]
        exact (AdjoinRoot.powerBasis' hf).basis_eq_pow _
      rw [hb,Algebra.smul_def,map_pow]

variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

 

theorem Data.exists_equiv (d e : Data R n f) :
    ∃ h : d.S ≃ₐ[R] e.S, ∀ i,h (d.roots i)=e.roots i := by
  obtain ⟨φ,hφ,hφu⟩ := d.universal e.S e.roots e.factorization
  obtain ⟨ψ,hψ,hψu⟩ := e.universal d.S d.roots d.factorization
  refine ⟨AlgEquiv.ofAlgHom φ ψ ?_ ?_,hφ⟩
  · apply e.hom_ext
    intro i
    change φ (ψ (e.roots i))=e.roots i
    rw [hψ,hφ]
  · apply d.hom_ext
    intro i
    change ψ (φ (d.roots i))=d.roots i
    rw [hφ,hψ]

 

theorem Data.exists_power_basis_of_top (d : Data R n f)
    (hf : f.natDegree≤n) (ht : f.coeff n=1) :
    ∃ b : Module.Basis (PowerIndex n) R d.S, ∀ e,b e=powerMonomial n d.roots e := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let : Subsingleton d.S := Module.subsingleton R _
      exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton d.S (PowerIndex n →₀ R)),
        fun _ => Subsingleton.elim _ _⟩
  | inr h =>
      have hn : f.natDegree=n := le_antisymm hf (le_natDegree_of_ne_zero (ht ▸ one_ne_zero))
      obtain ⟨e,b,hb⟩ := exists_power_data n R f (monic_of_natDegree_le_of_coeff_eq_one n hf ht) hn
      obtain ⟨φ,hφ⟩ := e.exists_equiv d
      refine ⟨b.map φ.toLinearEquiv,?_⟩
      intro x
      rw [Module.Basis.map_apply,hb]
      change φ (powerMonomial n e.roots x)=_
      have hh := map_powerMonomial φ.toMonoidHom n e.roots x
      change φ (powerMonomial n e.roots x)=powerMonomial n (fun i => φ (e.roots i)) x at hh
      rw [hh]
      congr 1
      funext i
      exact hφ i

end Lech.UniversalSplitting

end

end OAI

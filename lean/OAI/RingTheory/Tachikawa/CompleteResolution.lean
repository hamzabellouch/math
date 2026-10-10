import OAI.RingTheory.Tachikawa.StableDuality

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

def CokerAt (P : ChainComplex (ModuleCat R) ℤ) (j : ℤ) :=
  P.X j ⧸ LinearMap.range (P.d (j+1) j).hom

namespace CokerAt
variable (P : ChainComplex (ModuleCat R) ℤ) (j : ℤ)
instance : AddCommGroup (CokerAt P j) :=
  inferInstanceAs (AddCommGroup (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))
instance : Module R (CokerAt P j) :=
  inferInstanceAs (Module R (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))

def π : P.X j →ₗ[R] CokerAt P j := (LinearMap.range (P.d (j+1) j).hom).mkQ

lemma π_surjective : Function.Surjective (π P j) := Submodule.mkQ_surjective _

lemma π_d : (π P j).comp (P.d (j+1) j).hom = 0 := by
  apply LinearMap.ext
  intro x
  exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨x, rfl⟩

def ι : CokerAt P j →ₗ[R] P.X (j-1) :=
  (LinearMap.range (P.d (j+1) j).hom).liftQ (P.d j (j-1)).hom (by
    rintro x ⟨y, rfl⟩
    have h := P.d_comp_d (j+1) j (j-1)
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) y)

@[simp] lemma ι_π (x : P.X j) : ι P j (π P j x) = P.d j (j-1) x := rfl

lemma ι_comp_π : (ι P j).comp (π P j) = (P.d j (j-1)).hom := rfl

lemma ι_injective (h : Function.Exact (P.d (j+1) j) (P.d j (j-1))) :
    Function.Injective (ι P j) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := π_surjective P j x
  apply Submodule.Quotient.mk_eq_zero _ |>.mpr
  exact (h y).mp hx

def descend {N : Type} [AddCommGroup N] [Module R N] (f : P.X j →ₗ[R] N)
    (hf : f.comp (P.d (j+1) j).hom = 0) : CokerAt P j →ₗ[R] N :=
  (LinearMap.range (P.d (j+1) j).hom).liftQ f (by
    rintro x ⟨y, rfl⟩
    exact LinearMap.congr_fun hf y)

@[simp] lemma descend_π {N : Type} [AddCommGroup N] [Module R N]
    (f : P.X j →ₗ[R] N) (hf) (x : P.X j) : descend P j f hf (π P j x) = f x := rfl

lemma descend_comp_π {N : Type} [AddCommGroup N] [Module R N]
    (f : P.X j →ₗ[R] N) (hf) : (descend P j f hf).comp (π P j) = f := rfl
end CokerAt

def ComplexExact (P : ChainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ j, Function.Exact (P.d (j+1) j) (P.d j (j-1))

def TotallyAcyclic (P : ChainComplex (ModuleCat R) ℤ) : Prop :=
  ComplexExact P ∧ ∀ (j : ℤ) (f : P.X j →ₗ[R] R),
    f.comp (P.d (j+1) j).hom = 0 →
    ∃ g : P.X (j-1) →ₗ[R] R, g.comp (P.d j (j-1)).hom = f

namespace TotallyAcyclic
variable {P : ChainComplex (ModuleCat R) ℤ} (hP : TotallyAcyclic P)
include hP

lemma projective_boundaries {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (j : ℤ) (f : P.X j →ₗ[R] N)
    (hf : f.comp (P.d (j+1) j).hom = 0) :
    ∃ g : P.X (j-1) →ₗ[R] N, g.comp (P.d j (j-1)).hom = f := by
  let c := finiteFreeCover (R := R) (M := N)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := N))
    c.surjective
  have hc (i : Fin c.rank) :
      ((LinearMap.proj i).comp (s.comp f)).comp (P.d (j+1) j).hom = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hf, LinearMap.comp_zero, LinearMap.comp_zero]
  choose g hg using fun i : Fin c.rank => hP.2 j ((LinearMap.proj i).comp (s.comp f)) (hc i)
  refine ⟨c.map.comp (LinearMap.pi g), ?_⟩
  have heq : (LinearMap.pi g).comp (P.d j (j-1)).hom = s.comp f := by
    apply LinearMap.ext
    intro x
    funext i
    exact LinearMap.congr_fun (hg i) x
  rw [LinearMap.comp_assoc, heq, ← LinearMap.comp_assoc, hs, LinearMap.id_comp]

lemma extend_coker {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (j : ℤ) (f : CokerAt P j →ₗ[R] N) :
    ∃ g : P.X (j-1) →ₗ[R] N, g.comp (CokerAt.ι P j) = f := by
  obtain ⟨g, hg⟩ := hP.projective_boundaries j (f.comp (CokerAt.π P j)) (by
    rw [LinearMap.comp_assoc, CokerAt.π_d, LinearMap.comp_zero])
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P j x
  exact LinearMap.congr_fun hg y
end TotallyAcyclic
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ)

namespace CokerAt
instance (j : ℤ) : Module k (CokerAt P j) :=
  Module.compHom (CokerAt P j) (algebraMap k R)
instance (j : ℤ) : IsScalarTower k R (CokerAt P j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
end CokerAt

lemma ComplexExact.adjacent (hex : ComplexExact P) (i j l : ℤ)
    (hi : i = j+1) (hl : l = j-1) :
    Function.Exact (P.d i j) (P.d j l) := by
  subst i
  subst l
  exact hex j

def completeResolutionTail (hex : ComplexExact P)
    (proj : ∀ j, Module.Projective R (P.X j)) :
    ProjectiveResolution (ModuleCat.of R (CokerAt P 0)) := by
  let X (n : ℕ) : ModuleCat R := P.X (n : ℤ)
  let d (n : ℕ) : X (n+1) ⟶ X n := P.d ((n+1 : ℕ) : ℤ) (n : ℤ)
  let ε : X 0 ⟶ ModuleCat.of R (CokerAt P 0) := ModuleCat.ofHom (CokerAt.π P 0)
  apply resolutionOfExact _ X d ε
  · intro n
    exact hex.adjacent P _ _ _ (by omega) (by omega)
  · intro x
    change CokerAt.π P 0 x = 0 ↔ ∃ y, P.d 1 0 y = x
    exact Submodule.Quotient.mk_eq_zero _
  · exact CokerAt.π_surjective P 0
  · intro n
    let := proj (n : ℤ)
    infer_instance

lemma completeResolutionTail_d (hex : ComplexExact P)
    (proj : ∀ j, Module.Projective R (P.X j)) (n : ℕ) :
    (completeResolutionTail P hex proj).complex.d (n+1) n =
      P.d ((n+1 : ℕ) : ℤ) (n : ℤ) := by
  dsimp only [completeResolutionTail, resolutionOfExact]
  exact ChainComplex.of_d _ _ n

namespace TotallyAcyclic
variable {P}

lemma factors_iff_boundary (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    (j : ℤ) (f : P.X j →ₗ[R] N) (hf : f.comp (P.d (j+1) j).hom = 0) :
    CokerAt.descend P j f hf ∈ projectiveFactors (k := k) ↔
      ∃ g : P.X (j-1) →ₗ[R] N, g.comp (P.d j (j-1)).hom = f := by
  constructor
  · rintro ⟨J, hJf, hJp, a, b, hab⟩
    let := hJf
    let := hJp
    obtain ⟨a', ha'⟩ := hP.extend_coker j a
    refine ⟨b.comp a', ?_⟩
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun ha' (CokerAt.π P j x)
    change a' (P.d j (j-1) x) = a (CokerAt.π P j x) at hx
    change b (a' (P.d j (j-1) x)) = f x
    rw [hx]
    exact LinearMap.congr_fun hab (CokerAt.π P j x)
  · rintro ⟨g, hg⟩
    refine ⟨P.X (j-1), fin _, proj _, CokerAt.ι P j, g, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := CokerAt.π_surjective P j x
    exact LinearMap.congr_fun hg y

lemma boundaries_of_stableHom (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (N : ModuleCat R) (i j l : ℤ) (hi : i = j+1) (hl : l = j-1)
    (h : Subsingleton (StableHom (k := k) (R := R) (M := CokerAt P j) (N := N)))
    (f : P.X j →ₗ[R] N) (hf : f.comp (P.d i j).hom = 0) :
    ∃ g : P.X l →ₗ[R] N, g.comp (P.d j l).hom = f := by
  subst i
  subst l
  apply (hP.factors_iff_boundary (k := k) fin proj j f hf).mp
  apply (stableClass_eq_zero_iff _).mp
  exact h.elim _ _

lemma ext_subsingleton_of_stableHom (hP : TotallyAcyclic P)
    (fin : ∀ j, Module.Finite R (P.X j))
    (proj : ∀ j, Module.Projective R (P.X j))
    (N : ModuleCat R) (n : ℕ)
    (h : Subsingleton (StableHom (k := k) (R := R) (M := CokerAt P ((n+1 : ℕ) : ℤ))
      (N := N))) :
    Subsingleton (Abelian.Ext (ModuleCat.of R (CokerAt P 0)) N (n+1)) := by
  let Q := completeResolutionTail P hP.1 proj
  apply ext_subsingleton_of_boundaries Q n
  intro f hf
  have hf' : f.hom.comp (P.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [completeResolutionTail_d] at hf
    exact ModuleCat.hom_ext_iff.mp hf
  obtain ⟨g, hg⟩ := hP.boundaries_of_stableHom fin proj N
    ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ) (n : ℤ) (by omega) (by omega) h f.hom hf'
  refine ⟨ModuleCat.ofHom g, ?_⟩
  rw [completeResolutionTail_d]
  exact ModuleCat.hom_ext hg
end TotallyAcyclic
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

namespace CokerAt
variable (P : ChainComplex (ModuleCat R) ℤ)

def δ (i j : ℤ) : CokerAt P i →ₗ[R] P.X j :=
  descend P i (P.d i j).hom (ModuleCat.hom_ext_iff.mp (P.d_comp_d (i+1) i j))

@[simp] lemma δ_π (i j : ℤ) (x : P.X i) : δ P i j (π P i x) = P.d i j x := rfl

lemma δ_comp_π (i j : ℤ) : (δ P i j).comp (π P i) = (P.d i j).hom := rfl

lemma δ_injective (hex : ComplexExact P) (i j : ℤ) (h : i = j+1) :
    Function.Injective (δ P i j) := by
  have hj : j = i-1 := by omega
  subst j
  exact ι_injective P i (hex i)

lemma π_comp_δ (i j : ℤ) (h : i = j+1) : (π P j).comp (δ P i j) = 0 := by
  subst i
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := π_surjective P (j+1) x
  exact LinearMap.congr_fun (π_d P j) y

lemma δ_π_exact (i j : ℤ) (h : i = j+1) :
    Function.Exact (δ P i j) (π P j) := by
  subst i
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨π P (j+1) y, hy⟩
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (π_comp_δ P _ _ rfl) y

def factorThrough {L M N : Type} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) (f : L →ₗ[R] N)
    (hf : ∀ x, f x ∈ LinearMap.range i) : L →ₗ[R] M :=
  (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp (f.codRestrict _ hf)

lemma factorThrough_spec {L M N : Type} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) (f : L →ₗ[R] N)
    (hf : ∀ x, f x ∈ LinearMap.range i) :
    i.comp (factorThrough i hi f hf) = f := by
  ext x
  change i ((LinearEquiv.ofInjective i hi).symm ⟨f x, hf x⟩) = f x
  exact LinearEquiv.ofInjective_symm_apply i _
end CokerAt

namespace TotallyAcyclic
variable {P : ChainComplex (ModuleCat R) ℤ}

lemma extend_at (hP : TotallyAcyclic P) {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (i j : ℤ) (h : i = j+1)
    (f : CokerAt P i →ₗ[R] N) :
    ∃ g : P.X j →ₗ[R] N, g.comp (CokerAt.δ P i j) = f := by
  have hj : j = i-1 := by omega
  subst j
  exact hP.extend_coker i f
end TotallyAcyclic

variable (P Q : ChainComplex (ModuleCat R) ℤ)

structure ComparisonStep (i j : ℤ) (u : CokerAt P i →ₗ[R] CokerAt Q i)
    (v : CokerAt P j →ₗ[R] CokerAt Q j) where
  map : P.X j →ₗ[R] Q.X j
  upper : map.comp (CokerAt.δ P i j) = (CokerAt.δ Q i j).comp u
  lower : (CokerAt.π Q j).comp map = v.comp (CokerAt.π P j)

lemma comparison_step_up (hq : ComplexExact Q)
    (proj : ∀ j, Module.Projective R (P.X j)) (i j : ℤ) (h : i = j+1)
    (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    ∃ u : CokerAt P i →ₗ[R] CokerAt Q i, Nonempty (ComparisonStep P Q i j u v) := by
  let := proj j
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (CokerAt.π Q j)
    (v.comp (CokerAt.π P j)) (CokerAt.π_surjective Q j)
  have hr (x : CokerAt P i) : f (CokerAt.δ P i j x) ∈ LinearMap.range (CokerAt.δ Q i j) := by
    apply (CokerAt.δ_π_exact Q i j h _).mp
    change ((CokerAt.π Q j).comp f) (CokerAt.δ P i j x) = 0
    rw [hf]
    change v (((CokerAt.π P j).comp (CokerAt.δ P i j)) x) = 0
    rw [CokerAt.π_comp_δ P i j h]
    exact map_zero v
  let u := CokerAt.factorThrough (CokerAt.δ Q i j) (CokerAt.δ_injective Q hq i j h)
    (f.comp (CokerAt.δ P i j)) hr
  exact ⟨u, ⟨⟨f, (CokerAt.factorThrough_spec _ _ _ _).symm, hf⟩⟩⟩

lemma comparison_step_down (hp : TotallyAcyclic P)
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (i j : ℤ) (h : i = j+1) (u : CokerAt P i →ₗ[R] CokerAt Q i) :
    ∃ v : CokerAt P j →ₗ[R] CokerAt Q j, Nonempty (ComparisonStep P Q i j u v) := by
  let := qfin j
  let := qproj j
  obtain ⟨f, hf⟩ := hp.extend_at i j h ((CokerAt.δ Q i j).comp u)
  subst i
  have hf' : ((CokerAt.π Q j).comp f).comp (P.d (j+1) j).hom = 0 := by
    ext x
    have hfx := LinearMap.congr_fun hf (CokerAt.π P (j+1) x)
    change f (P.d (j+1) j x) = CokerAt.δ Q (j+1) j (u (CokerAt.π P (j+1) x)) at hfx
    change CokerAt.π Q j (f (P.d (j+1) j x)) = 0
    rw [hfx]
    exact LinearMap.congr_fun (CokerAt.π_comp_δ Q _ _ rfl) _
  exact ⟨CokerAt.descend P j ((CokerAt.π Q j).comp f) hf', ⟨⟨f, hf, rfl⟩⟩⟩

namespace CompleteLift
variable (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))

def up (j : ℤ) (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    CokerAt P (j+1) →ₗ[R] CokerAt Q (j+1) :=
  (comparison_step_up P Q hq pproj (j+1) j rfl v).choose

def upSquare (j : ℤ) (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    ComparisonStep P Q (j+1) j (up P Q hq pproj j v) v :=
  (comparison_step_up P Q hq pproj (j+1) j rfl v).choose_spec.some

def down (j : ℤ) (u : CokerAt P j →ₗ[R] CokerAt Q j) :
    CokerAt P (j-1) →ₗ[R] CokerAt Q (j-1) :=
  (comparison_step_down P Q hp qfin qproj j (j-1) (by omega) u).choose

def downSquare (j : ℤ) (u : CokerAt P j →ₗ[R] CokerAt Q j) :
    ComparisonStep P Q j (j-1) u (down P Q hp qfin qproj j u) :=
  (comparison_step_down P Q hp qfin qproj j (j-1) (by omega) u).choose_spec.some

variable (u₀ : CokerAt P 0 →ₗ[R] CokerAt Q 0)

def cokerMap (j : ℤ) : CokerAt P j →ₗ[R] CokerAt Q j :=
  j.inductionOn' 0 u₀ (fun j _ => up P Q hq pproj j) (fun j _ => down P Q hp qfin qproj j)

lemma cokerMap_zero : cokerMap P Q hp hq pproj qfin qproj u₀ 0 = u₀ :=
  Int.inductionOn'_self

lemma cokerMap_up (j : ℤ) (hj : 0 ≤ j) :
    cokerMap P Q hp hq pproj qfin qproj u₀ (j+1) =
      up P Q hq pproj j (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  Int.inductionOn'_add_one hj

lemma cokerMap_down (j : ℤ) (hj : j ≤ 0) :
    cokerMap P Q hp hq pproj qfin qproj u₀ (j-1) =
      down P Q hp qfin qproj j (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  Int.inductionOn'_sub_one hj

lemma hasSquare_down (i j : ℤ) (h : i-1=j) (hi : i ≤ 0) :
    Nonempty (ComparisonStep P Q i j
      (cokerMap P Q hp hq pproj qfin qproj u₀ i)
      (cokerMap P Q hp hq pproj qfin qproj u₀ j)) := by
  subst j
  rw [cokerMap_down P Q hp hq pproj qfin qproj u₀ i hi]
  exact ⟨downSquare P Q hp qfin qproj i _⟩

lemma hasSquare (j : ℤ) : Nonempty (ComparisonStep P Q (j+1) j
    (cokerMap P Q hp hq pproj qfin qproj u₀ (j+1))
    (cokerMap P Q hp hq pproj qfin qproj u₀ j)) := by
  by_cases hj : 0 ≤ j
  · rw [cokerMap_up P Q hp hq pproj qfin qproj u₀ j hj]
    exact ⟨upSquare P Q hq pproj j _⟩
  · exact hasSquare_down P Q hp hq pproj qfin qproj u₀ (j+1) j (by omega) (by omega)

def square (j : ℤ) : ComparisonStep P Q (j+1) j
    (cokerMap P Q hp hq pproj qfin qproj u₀ (j+1))
    (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  (hasSquare P Q hp hq pproj qfin qproj u₀ j).some

def chainMap : P ⟶ Q :=
  ChainComplex.ofHom
    (fun j => ModuleCat.ofHom (square P Q hp hq pproj qfin qproj u₀ j).map) (fun j => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s := square P Q hp hq pproj qfin qproj u₀ j
      let s' := square P Q hp hq pproj qfin qproj u₀ (j+1)
      change Q.d (j+1) j (s'.map x) = s.map (P.d (j+1) j x)
      rw [← CokerAt.δ_π Q (j+1) j]
      have h₁ := LinearMap.congr_fun s'.lower x
      have h₂ := LinearMap.congr_fun s.upper (CokerAt.π P (j+1) x)
      change CokerAt.π Q (j+1) (s'.map x) = _ at h₁
      rw [h₁]
      exact h₂.symm)

end CompleteLift

namespace CokerAt
variable {P Q}

def map (f : P ⟶ Q) (j : ℤ) : CokerAt P j →ₗ[R] CokerAt Q j :=
  descend P j ((π Q j).comp (f.f j).hom) (by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm (j+1) j)) x
    change Q.d (j+1) j (f.f (j+1) x) = f.f j (P.d (j+1) j x) at h
    change π Q j (f.f j (P.d (j+1) j x)) = 0
    rw [← h]
    exact LinearMap.congr_fun (π_d Q j) (f.f (j+1) x))

@[simp] lemma map_π (f : P ⟶ Q) (j : ℤ) (x : P.X j) :
    map f j (π P j x) = π Q j (f.f j x) := rfl

lemma map_comp {S : ChainComplex (ModuleCat R) ℤ} (f : P ⟶ Q) (g : Q ⟶ S) (j : ℤ) :
    map (f ≫ g) j = (map g j).comp (map f j) := by
  ext x
  obtain ⟨y, rfl⟩ := π_surjective P j x
  rfl

lemma map_id (j : ℤ) : map (𝟙 P) j = LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := π_surjective P j x
  rfl
end CokerAt

theorem exists_complete_lift (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (u : CokerAt P 0 →ₗ[R] CokerAt Q 0) :
    ∃ f : P ⟶ Q, CokerAt.map f 0 = u := by
  refine ⟨CompleteLift.chainMap P Q hp hq pproj qfin qproj u, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P 0 x
  change CokerAt.π Q 0 ((CompleteLift.square P Q hp hq pproj qfin qproj u 0).map y) = _
  have h := LinearMap.congr_fun (CompleteLift.square P Q hp hq pproj qfin qproj u 0).lower y
  exact h.trans (LinearMap.congr_fun
    (CompleteLift.cokerMap_zero P Q hp hq pproj qfin qproj u) (CokerAt.π P 0 y))

end Tachikawa



namespace Tachikawa.CokerAt
open CategoryTheory
variable {R : Type} [Ring R] (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (N : ModuleCat.{0} R) (j : ℤ) (a : P.X j →ₗ[R] N)
  (he : Function.Exact (P.d (j+1) j) a) (hs : Function.Surjective a)

def augmentationEquiv : CokerAt P j ≃ₗ[R] N :=
  LinearEquiv.ofBijective (descend P j a he.linearMap_comp_eq_zero) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y,rfl⟩ := π_surjective P j x
      change a y = 0 at hx
      obtain ⟨z,hz⟩ := (he y).mp hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z,hz⟩
    · intro x
      obtain ⟨y,rfl⟩ := hs x
      exact ⟨π P j y,rfl⟩)

@[simp] lemma augmentationEquiv_π (x : P.X j) :
    augmentationEquiv P N j a he hs (π P j x) = a x := rfl
end Tachikawa.CokerAt

end

end OAI

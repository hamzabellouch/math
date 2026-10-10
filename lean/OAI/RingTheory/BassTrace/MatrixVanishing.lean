import OAI.RingTheory.BassTrace.SparseBounds

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.PathChains

open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains Sparse.GraphGeometry

open scoped Classical Pointwise BassTrace.Detector

variable {G : Type*} [Group G] [Countable G] {ι : Type*} [Fintype ι]

lemma totalWeight_zero_of_finite_generators
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (hgen : Subgroup.closure (S : Set G)=⊤)
    (heS : support e⊆S) (g : G) (hg : ¬IsOfFinOrder g) : totalWeight e g 0=0 := by
  let H := ActingGroup g
  let Y := Vertex g
  have : Countable Y := inferInstanceAs (Countable (Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))))
  have : Countable H := inferInstanceAs (Countable (ActingGroup g))
  let _ : LinearOrder Y := linearOrderOfSTO WellOrderingRel
  let _ : LinearOrder (Y →₀ ℝ) := linearOrderOfSTO WellOrderingRel
  let D := max 2 S.card
  let M := volumeThreshold D
  let n := 2*(M+1)
  let K := pathSupport e g n
  let _ : Fact (∀(h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces) :=
    ⟨generatedComplex_invariant (topPaths e g n)⟩
  let act : MulAction H (SourceTop K n) := sourceTopAction K n (generatedComplex_invariant (topPaths e g n))
  let _ : Finite (MulAction.orbitRel.Quotient H (SourceTop K n)) :=
    by
      convert generatedTop_finite (H := H) (topPaths e g n) n (fun _ ht=>topPaths_card e g n ht) using 1
      congr 3
      dsimp only [act]
      congr 1
      exact Subsingleton.elim _ _
  let Γ := supportGraph g S hS
  have hΓ : Γ.Connected := supportGraph_connected g S hS hgen
  have hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v := supportGraph_smul g S hS
  have hK := pathSupport_pure e g S hS heS n
  obtain ⟨β,hβ,hβc,hβl⟩ := exists_complex_beta g hg
  let ψ := cosetCocycle g (M+1) β
  have hInv : (augmentedComplex K).IsInvariant (H := H) := augmentedComplex_invariant
  have hinv (h : H) (c : Degree Y (n+1)) : ψ (relabel (n+1) (fun y=>h•y) c)=ψ c := by
    induction h using Quotient.inductionOn with | _ h =>
      exact cosetCocycle_invariant g (M+1) β hβc hβl h c
  let c : (augmentedComplex K).chains (n+1) := ⟨liftPath e g n,liftPath_mem e g n⟩
  have hv : ψ c=0 := sparse_vanishing (H := H) (X := FreeParameter.Space H)
    Γ hΓ hAut (graphMetric_action_isometry Γ hΓ hAut)
    (by dsimp [n]; omega) hK (FreeParameter.probability H) (FreeParameter.probability_preserving H)
    D (le_max_left _ _) (fun v=>by simpa only [SimpleGraph.card_neighborSet_eq_degree] using
      (supportGraph_degree_le g S hS v).trans (le_max_right 2 _))
    (by dsimp [n,M]; omega)
    (generatedReps (topPaths e g n)) (fun _ hs=>generatedReps_mem _ hs)
    (fun _ hs=>generatedReps_complete _ hs) (project g 1) ψ hinv
    (cosetCocycle_closed g (M+1) β hβ) c (internal_path_cycle e he g M hInv)
  have hp : quotientCocycle g β hβc hβl (M+1) (pathChain e g (2*(M+1)))=0 := by
    rw [←liftPath_quotient]
    exact hv
  rw [quotientCocycle_pairing g β hβc hβl e he hβ (M+1)] at hp
  exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ (inv_ne_zero (by norm_num)))

end BassTrace.PathChains

namespace BassTrace

open scoped Classical BigOperators

lemma classCoefficient_zero_finitely_generated {G : Type*} [Group G] [Countable G] [Group.FG G]
    {ι : Type*} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    classCoefficient g (Matrix.trace e)=0 := by
  obtain ⟨S,hS,hgen,heS⟩ := exists_symmetric_generators e
  rw [←totalWeight_eq_classCoefficient e he]
  exact PathChains.totalWeight_zero_of_finite_generators e he S hS hgen heS g hg

theorem bassTrace {G : Type*} [Group G] {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    idempotentTraceCoefficient e g=0 := by
  let K := Subgroup.closure (Paths.support e : Set G)
  have hs : ∀s∈Paths.support e,s∈K := fun _ hs=>Subgroup.subset_closure hs
  let _ : Group.FG K := Group.closure_finset_fg (Paths.support e)
  let _ : Countable K := by
    dsimp [K]
    rw [FreeGroup.closure_eq_range]
    exact (MonoidHom.rangeRestrict_surjective _).countable
  let a := Matrix.trace (restrictMatrix K e)
  change classCoefficient g (Matrix.trace e)=0
  rw [←map_trace_restrict K e hs,classCoefficient_map_subgroup]
  apply sum_conjugacy_invariant_zero a (fun h=>IsConj (h : G) g)
  · intro h k hc
    have hc' := K.subtype.map_isConj hc
    exact ⟨fun hh=>hc'.symm.trans hh,fun hk=>hc'.trans hk⟩
  · intro h hh
    apply classCoefficient_zero_finitely_generated (restrictMatrix K e)
      (restrictMatrix_idempotent K e he hs) h
    intro ho
    exact hg (hh.isOfFinOrder (K.subtype.isOfFinOrder ho))

end BassTrace

end

end OAI

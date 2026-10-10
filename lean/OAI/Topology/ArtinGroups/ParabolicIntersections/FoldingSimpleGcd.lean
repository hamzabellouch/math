import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingPositive
import OAI.Topology.ArtinGroups.ParabolicIntersections.PositiveTransport

namespace OAI

/-! Folding preserves greatest common prefixes of simple elements. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "Φ" => foldedPositiveHom M Y hY
local notation "P" => positiveSimpleLift R

private lemma folded_prefix {a b : PositiveArtin R} (h : PositivePrefix R a b) :
    PositivePrefix N (Φ a) (Φ b) := by
  obtain ⟨c,rfl⟩ := h
  exact ⟨_,map_mul _ _ _⟩

/-- Greatest common prefixes of simples are preserved by the color folding.
The induction removes one complete color at a time. -/
theorem folded_simple_gcd (u v g : (R).Group)
    (hgu : PositivePrefix R (P g) (P u)) (hgv : PositivePrefix R (P g) (P v))
    (hg : ∀ e, PositivePrefix R e (P u) → PositivePrefix R e (P v) → PositivePrefix R e (P g)) :
    ∀ e, PositivePrefix N e (Φ (P u)) → PositivePrefix N e (Φ (P v)) →
      PositivePrefix N e (Φ (P g)) := by
  let : Finite (N).Group := unfolded_finite M Y hY
  let : LinearOrder (Y × FusionLabel (fusionLabelSize M)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have cancelR := spherical_positive_cancel_left M Y hY
  have cancelN := finite_positive_cancel_left N
  induction u using (measure (fun u => (R).toCoxeterSystem.length u)).wf.induction
      generalizing v g with
  | h u ih =>
    intro e heu hev
    obtain ⟨d,hdu,hdv,hd⟩ := exists_greatest_common_simplePrefix N
      (unfoldedHom M Y hY u) (unfoldedHom M Y hY v)
    simp only [←foldedPositiveHom_simpleLift] at hdu hdv hd
    apply positivePrefix_trans N (hd e heu hev)
    by_cases hd1 : positiveSimpleLift N d=1
    · rw [hd1]
      exact positivePrefix_one N _
    obtain ⟨α,hα⟩ := exists_positive_first N hd1
    have hau := positivePrefix_trans N hα hdu
    have hav := positivePrefix_trans N hα hdv
    have hiu := (folded_simple_atom_iff M Y hY u α).mp hau
    have hiv := (folded_simple_atom_iff M Y hY v α).mp hav
    have hig := hg _ hiu hiv
    obtain ⟨ur,hur⟩ := hiu
    obtain ⟨vr,hvr⟩ := hiv
    obtain ⟨gr,hgr⟩ := hig
    have su := (positive_simple_factors R _ _ _ hur.symm).2
    have sv := (positive_simple_factors R _ _ _ hvr.symm).2
    have sg := (positive_simple_factors R _ _ _ hgr.symm).2
    have pgu : PositivePrefix R gr ur :=
      (positivePrefix_mul_left_iff R cancelR _ _ _).mp (by rwa [←hur,←hgr])
    have pgv : PositivePrefix R gr vr :=
      (positivePrefix_mul_left_iff R cancelR _ _ _).mp (by rwa [←hvr,←hgr])
    have pg : ∀ x, PositivePrefix R x ur → PositivePrefix R x vr → PositivePrefix R x gr := by
      intro x hxu hxv
      apply (positivePrefix_mul_left_iff R cancelR (positiveGenerator R α.1) x gr).mp
      rw [←hgr]
      apply hg
      · rw [hur]; exact positivePrefix_mul_left R _ hxu
      · rw [hvr]; exact positivePrefix_mul_left R _ hxv
    have hcolor : PositivePrefix N (Φ (positiveGenerator R α.1)) (positiveSimpleLift N d) :=
      hd _ (folded_prefix M Y hY ⟨ur,hur⟩) (folded_prefix M Y hY ⟨vr,hvr⟩)
    obtain ⟨dr,hdr⟩ := hcolor
    have dru : PositivePrefix N dr (Φ ur) :=
      (positivePrefix_mul_left_iff N cancelN _ _ _).mp (by
        simpa only [hur,map_mul,hdr] using hdu)
    have drv : PositivePrefix N dr (Φ vr) :=
      (positivePrefix_mul_left_iff N cancelN _ _ _).mp (by
        simpa only [hvr,map_mul,hdr] using hdv)
    have hlt : (R).toCoxeterSystem.length (positiveToCoxeter R ur) <
        (R).toCoxeterSystem.length u := by
      have hdg := congrArg (positiveDegree R) hur
      simp only [positiveDegree_simpleLift,positiveDegree_mul,positiveDegree_generator] at hdg
      rw [su,positiveDegree_simpleLift] at hdg
      omega
    have hr := ih (positiveToCoxeter R ur) hlt (positiveToCoxeter R vr)
      (positiveToCoxeter R gr) (by rwa [←sg,←su]) (by rwa [←sg,←sv])
      (by simpa only [←su,←sv,←sg] using pg) dr
      (by rwa [←su]) (by rwa [←sv])
    rw [←sg] at hr
    rw [hdr,hgr,map_mul]
    exact positivePrefix_mul_left N _ hr

end HarmonicArtin.ParabolicIntersections

end OAI

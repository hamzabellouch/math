import Mathlib

namespace OAI

namespace HarmonicArtin

lemma interior_convexHull_reindex {I J B:Type*} (e:I≃J) (v:J→ℝ) (f:B→J→ℝ)
    (h:(v∘e)∈interior (convexHull ℝ (Set.range fun b=>(f b)∘e))) :
    v∈interior (convexHull ℝ (Set.range f)) := by
  let E:=ContinuousLinearEquiv.piCongrLeft ℝ (fun _:J=>ℝ) e
  have hmap (g:J→ℝ):E (g∘e)=g := by
    exact E.apply_symm_apply g
  have hr:E '' (Set.range fun b=>(f b)∘e)=Set.range f := by
    ext x
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      exact ⟨b,(hmap (f b)).symm⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(f b)∘e,⟨b,rfl⟩,hmap (f b)⟩
  have hh:E (v∘e)∈E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e)) := by
    exact ⟨v∘e,h,rfl⟩
  have hi:=E.toHomeomorph.image_interior (convexHull ℝ (Set.range fun b=>(f b)∘e))
  change E '' interior (convexHull ℝ (Set.range fun b=>(f b)∘e))=
    interior (E '' convexHull ℝ (Set.range fun b=>(f b)∘e)) at hi
  have hc:=E.toLinearMap.image_convexHull (Set.range fun b=>(f b)∘e)
  change E '' convexHull ℝ (Set.range fun b=>(f b)∘e)=
    convexHull ℝ (E '' (Set.range fun b=>(f b)∘e)) at hc
  rw [hi,hc,hr,hmap] at hh
  exact hh

end HarmonicArtin

end OAI

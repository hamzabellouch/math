import OAI.RingTheory.BassTrace.Coning

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section Restriction

def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1

lemma restrictComplex_le (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    restrictComplex B P ≤ B := fun _ hs => hs.1

lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)

lemma mem_restrict_supporting {B : Geometry.SimplicialComplex ℝ E}
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hB : ∀ x ∈ B.space, f x ≤ b)
    {s : Finset E} (hs : s ∈ B.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hfx : f x = b) :
    ∃ t ∈ (restrictComplex B {y | f y = b}).faces,
      t ⊆ s ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  let t := s.filter (fun y => f y = b)
  have ht : (t : Set E) = (s : Set E) ∩ {y | f y = b} := by
    ext y
    simp [t]
  have hxt : x ∈ convexHull ℝ (t : Set E) := by
    rw [ht, ← convexHull_inter_supporting _ f b]
    · exact ⟨hx, hfx⟩
    · exact fun y hy => hB y (B.subset_space hs hy)
  have hne : t.Nonempty := by
    exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
  refine ⟨t, ⟨B.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩,
    Finset.filter_subset _ _, hxt⟩
  intro y hy
  exact (Finset.mem_filter.mp hy).2

lemma restrictComplex_space_supporting (B : Geometry.SimplicialComplex ℝ E)
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hB : ∀ x ∈ B.space, f x ≤ b) :
    (restrictComplex B {y | f y = b}).space = B.space ∩ {y | f y = b} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨B.convexHull_subset_space hs.1 hx,
      linear_eq_on_affineSpan f (fun _ hy => hs.2 hy) (convexHull_subset_affineSpan _ hx)⟩
  · rintro ⟨hx, hfx⟩
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, _, hxt⟩ := mem_restrict_supporting f b hB hs hx hfx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, ht, hxt⟩

def glueComplex (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    Geometry.SimplicialComplex ℝ E where
  faces := B.faces ∪ C.faces
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨B.nonempty_of_mem_faces hs, fun _ ht hn => Or.inl (B.down_closed hs ht hn)⟩
    · exact ⟨C.nonempty_of_mem_faces hs, fun _ ht hn => Or.inr (C.down_closed hs ht hn)⟩
  indep := by
    intro s hs
    exact hs.elim B.indep C.indep
  inter_subset_convexHull := by
    intro s t hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact B.inter_subset_convexHull hs ht
    · exact hcross s hs t ht
    · simpa only [Set.inter_comm] using hcross t ht s hs
    · exact C.inter_subset_convexHull hs ht

lemma glueComplex_finite (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hB : B.faces.Finite) (hC : C.faces.Finite) :
    (glueComplex B C hcross).faces.Finite := hB.union hC

lemma glueComplex_space (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    (glueComplex B C hcross).space = B.space ∪ C.space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_union,
    show (glueComplex B C hcross).faces = B.faces ∪ C.faces from rfl]
  aesop

lemma cross_inter_of_supporting_agreement
    (B C : Geometry.SimplicialComplex ℝ E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hB : ∀ x ∈ B.space, f x ≤ b) (hC : ∀ x ∈ C.space, b ≤ f x)
    (hcommon : restrictComplex B {x | f x = b} = restrictComplex C {x | f x = b})
    {s t : Finset E} (hs : s ∈ B.faces) (ht : t ∈ C.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  intro x hx
  have hfx : f x = b := le_antisymm
    (hB x (B.convexHull_subset_space hs hx.1))
    (hC x (C.convexHull_subset_space ht hx.2))
  obtain ⟨u, hu, hus, hxu⟩ := mem_restrict_supporting f b hB hs hx.1 hfx
  rw [hcommon] at hu
  have hi := C.inter_subset_convexHull hu.1 ht ⟨hxu, hx.2⟩
  apply convexHull_mono _ hi
  intro y hy
  exact ⟨hus hy.1, hy.2⟩

end Restriction

section Trace

def RespectsSet (B : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ s ∈ B.faces, convexHull ℝ (s : Set E) ∩ P = convexHull ℝ ((s : Set E) ∩ P)

lemma restrictComplex_space_of_respects (B : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (h : RespectsSet B P) :
    (restrictComplex B P).space = B.space ∩ P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    refine ⟨B.convexHull_subset_space hs.1 hx, ?_⟩
    have he : (s : Set E) ∩ P = s := Set.inter_eq_left.mpr hs.2
    have hx' : x ∈ convexHull ℝ (s : Set E) ∩ P := by
      rw [h s hs.1, he]
      exact hx
    exact hx'.2
  · rintro ⟨hx, hxP⟩
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let t := s.filter (· ∈ P)
    have ht : (t : Set E) = (s : Set E) ∩ P := by ext; simp [t]
    have hxt : x ∈ convexHull ℝ (t : Set E) := by
      rw [ht, ← h s hs]
      exact ⟨hx, hxP⟩
    have hne : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    refine Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨B.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩, hxt⟩
    intro y hy
    exact (Finset.mem_filter.mp hy).2

lemma hull_inter_of_supporting_eq (s : Finset E) (P Q : Set E)
    (hsP : convexHull ℝ (s : Set E) ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    convexHull ℝ (s : Set E) ∩ Q = convexHull ℝ ((s : Set E) ∩ Q) := by
  have hiff (x : E) (hx : x ∈ P) : x ∈ Q ↔ f x = b := by
    constructor
    · intro hq
      exact (hface.subset ⟨hx, hq⟩).2
    · intro he
      exact (hface.symm.subset ⟨hx, he⟩).2
  calc
    _ = convexHull ℝ (s : Set E) ∩ {x | f x = b} := by
      ext x
      exact and_congr_right (fun hx => hiff x (hsP hx))
    _ = convexHull ℝ ((s : Set E) ∩ {x | f x = b}) :=
      convexHull_inter_supporting _ f b (fun x hx => hf x (hsP (subset_convexHull _ _ hx)))
    _ = _ := by
      congr 1
      ext x
      exact and_congr_right (fun hx => (hiff x (hsP (subset_convexHull _ _ hx))).symm)

lemma respectsSet_of_supporting_eq (B : Geometry.SimplicialComplex ℝ E)
    (P Q : Set E) (hBP : B.space ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    RespectsSet B Q := by
  intro s hs
  exact hull_inter_of_supporting_eq s P Q ((B.convexHull_subset_space hs).trans hBP)
    f b hf hface

lemma cross_inter_of_respects (B C : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (hB : RespectsSet B P) (hC : C.space ⊆ P)
    (hcommon : restrictComplex B P ≤ C)
    {s t : Finset E} (hs : s ∈ B.faces) (ht : t ∈ C.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  classical
  intro x hx
  let u := s.filter (· ∈ P)
  have hu : (u : Set E) = (s : Set E) ∩ P := by ext; simp [u]
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    rw [hu, ← hB s hs]
    exact ⟨hx.1, hC (C.convexHull_subset_space ht hx.2)⟩
  have hne : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxu⟩)
  have huB : u ∈ (restrictComplex B P).faces :=
    ⟨B.down_closed hs (Finset.filter_subset _ _) hne,
      fun _ hy => (Finset.mem_filter.mp hy).2⟩
  have hi := C.inter_subset_convexHull (hcommon huB) ht ⟨hxu, hx.2⟩
  apply convexHull_mono _ hi
  intro y hy
  exact ⟨(Finset.mem_filter.mp hy.1).1, hy.2⟩

end Trace

section GeneralBoundary

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma mem_radialBoundary_of_supporting {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ) (hf : ∀ y ∈ cell a b, f y ≤ d)
    (hfc : f c < d) (hfx : f x = d) : x ∈ radialBoundary a b c := by
  have hxc : x ≠ c := by intro he; subst x; exact (ne_of_lt hfc) hfx
  obtain ⟨i, t, ht, hy, hi, hic, _⟩ := bounded_exists_ray_boundary a b hbounded hc hx hxc
  have hfy := hf _ hy
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hfx] at hfy
  have ht1 : t = 1 := by nlinarith
  subst t
  simp only [one_smul, add_sub_cancel] at hi
  exact ⟨hx, i, hi, hic⟩

end GeneralBoundary

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def SupportingFace (Q P : Set V) : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ P, f x ≤ b) ∧
    Q = P ∩ {x | f x = b}

lemma SupportingFace.subset {Q P : Set V} (h : SupportingFace Q P) : Q ⊆ P := by
  obtain ⟨f, b, _, rfl⟩ := h
  exact Set.inter_subset_left

lemma supportingFace_self (P : Set V) : SupportingFace P P := by
  refine ⟨0, 0, by simp, ?_⟩
  simp

lemma linear_le_on_convexHull (s : Set V) (f : V →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  intro x hx
  apply convexHull_min (s := s) (t := {y | f y ≤ b}) hf _ hx
  intro y hy z hz u v hu hv huv
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at *
  calc
    u * f y + v * f z ≤ u * b + v * b :=
      add_le_add (mul_le_mul_of_nonneg_left hy hu) (mul_le_mul_of_nonneg_left hz hv)
    _ = b := by rw [← add_mul, huv, one_mul]

lemma SupportingFace.trans_finite_hull {s : Finset V} {Q R : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V)))
    (hR : SupportingFace R Q) : SupportingFace R (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hR⟩ := hR
  have hfv (x : V) (hx : x ∈ s) : f x ≤ b := hf x (subset_convexHull ℝ _ hx)
  have hgv (x : V) (hx : x ∈ s) (he : f x = b) : g x ≤ d := by
    apply hg
    rw [hQ]
    exact ⟨subset_convexHull ℝ _ hx, he⟩
  let M : ℝ := 1 + ∑ x ∈ s, |g x - d| / (b - f x)
  let k : V →ₗ[ℝ] ℝ := M • f + g
  have hk (x : V) : k x = M * f x + g x := by simp [k]
  have hstrict (x : V) (hx : x ∈ s) (he : f x ≠ b) : k x < M*b+d := by
    have hb : 0 < b - f x := sub_pos.mpr (lt_of_le_of_ne (hfv x hx) he)
    have hterm : |g x-d| / (b-f x) ≤ ∑ y ∈ s, |g y-d| / (b-f y) :=
      Finset.single_le_sum (fun y hy => div_nonneg (abs_nonneg (g y-d)) (sub_nonneg.mpr (hfv y hy))) hx
    have hratio : |g x-d| / (b-f x) < M := by dsimp [M]; linarith
    have hm := (div_lt_iff₀ hb).mp hratio
    rw [hk]
    have hab := le_abs_self (g x-d)
    nlinarith only [hm, hab]
  have hkv (x : V) (hx : x ∈ s) : k x ≤ M*b+d := by
    by_cases he : f x = b
    · rw [hk, he]
      linarith [hgv x hx he]
    · exact (hstrict x hx he).le
  have hkeq (x : V) (hx : x ∈ s) :
      k x = M*b+d ↔ f x = b ∧ g x = d := by
    by_cases he : f x = b
    · rw [hk, he]
      constructor
      · intro hh; exact ⟨rfl, by linarith⟩
      · rintro ⟨_, rfl⟩; rfl
    · exact iff_of_false (ne_of_lt (hstrict x hx he)) (fun hh => he hh.1)
  refine ⟨k, M*b+d, linear_le_on_convexHull _ k _ hkv, ?_⟩
  have hvQ : Q = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) := by
    rw [hQ, convexHull_inter_supporting _ f b hfv]
  calc
    R = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d} := by rw [hR, hvQ]
    _ = convexHull ℝ (((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d}) :=
      convexHull_inter_supporting _ g d (fun x hx => hgv x hx.1 hx.2)
    _ = convexHull ℝ ((s : Set V) ∩ {x | k x = M*b+d}) := by
      congr 1
      ext x
      constructor
      · rintro ⟨⟨hx, hfx⟩, hgx⟩
        exact ⟨hx, (hkeq x hx).mpr ⟨hfx, hgx⟩⟩
      · rintro ⟨hx, hkx⟩
        exact ⟨⟨hx, ((hkeq x hx).mp hkx).1⟩, ((hkeq x hx).mp hkx).2⟩
    _ = convexHull ℝ (s : Set V) ∩ {x | k x = M*b+d} :=
      (convexHull_inter_supporting _ k _ hkv).symm

lemma SupportingFace.restrict {Q P S : Set V} (h : SupportingFace Q P)
    (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  obtain ⟨f, b, hf, hQ⟩ := h
  refine ⟨f, b, fun x hx => hf x (hSP hx), ?_⟩
  ext x
  rw [hQ]
  exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hSP hx.1, hx.2⟩⟩

lemma SupportingFace.supporting_inter {Q S P : Set V}
    (hQ : SupportingFace Q P) (hS : SupportingFace S P) :
    SupportingFace (Q ∩ S) P := by
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hS⟩ := hS
  refine ⟨f+g, b+d, fun x hx => add_le_add (hf x hx) (hg x hx), ?_⟩
  ext x
  simp only [hQ, hS, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.add_apply]
  constructor
  · rintro ⟨⟨hxP, hfx⟩, _, hgx⟩
    exact ⟨hxP, by rw [hfx, hgx]⟩
  · rintro ⟨hxP, hfgx⟩
    exact ⟨⟨hxP, by linarith [hf x hxP, hg x hxP]⟩,
      hxP, by linarith [hf x hxP, hg x hxP]⟩

lemma SupportingFace.eq_convexHull_subset {s : Finset V} {Q : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V))) :
    ∃ t : Finset V, t ⊆ s ∧ Q = convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨f, b, hf, he⟩ := hQ
  refine ⟨s.filter (fun x => f x = b), Finset.filter_subset _ _, ?_⟩
  rw [he, convexHull_inter_supporting _ f b (fun x hx => hf x (subset_convexHull ℝ _ hx))]
  congr 1
  ext x
  simp

lemma finite_supportingFaces (s : Finset V) :
    {Q : Set V | Q.Nonempty ∧ SupportingFace Q (convexHull ℝ (s : Set V))}.Finite := by
  classical
  apply ((s.powerset.image (fun t : Finset V => convexHull ℝ (t : Set V))).finite_toSet).subset
  intro Q hQ
  obtain ⟨t, ht, rfl⟩ := hQ.2.eq_convexHull_subset
  exact Finset.mem_image_of_mem (fun t : Finset V => convexHull ℝ (t : Set V))
    (Finset.mem_powerset.mpr ht)

lemma SupportingFace.inter_of_parent_inter {s : Finset V} {P Q R S : Set V}
    (hQ : SupportingFace Q P) (hR : SupportingFace R S)
    (hPS : SupportingFace (P ∩ S) P)
    (hs : Q = convexHull ℝ (s : Set V)) : SupportingFace (Q ∩ R) Q := by
  have hQS : SupportingFace (Q ∩ S) Q := by
    have h := hPS.restrict hQ.subset
    have he : Q ∩ (P ∩ S) = Q ∩ S := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, hQ.subset hx.1, hx.2⟩⟩
    rwa [he] at h
  have hQR : SupportingFace ((Q ∩ S) ∩ R) (Q ∩ S) := hR.restrict Set.inter_subset_right
  have he : (Q ∩ S) ∩ R = Q ∩ R := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, hR.subset hx.2⟩, hx.2⟩⟩
  rw [he] at hQR
  rw [hs] at hQS ⊢
  exact hQS.trans_finite_hull (by simpa only [hs] using hQR)

structure CellData (P : Set V) where
  n : ℕ
  a : Fin n → V →ₗ[ℝ] ℝ
  b : Fin n → ℝ
  eq_cell : P = cell a b
  bounded : Bornology.IsBounded P
  center : V
  center_mem : center ∈ P
  center_support : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
    f center = d → ∀ x ∈ P, f x = d

lemma cell_reindex {I J : Type*} (e : I ≃ J) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cell (fun j => a (e.symm j)) (fun j => b (e.symm j)) = cell a b := by
  ext x
  constructor
  · intro hx i
    simpa only [Equiv.symm_apply_apply] using hx (e i)
  · intro hx j
    exact hx (e.symm j)

noncomputable def CellData.ofPresentation {I : Type*} [Fintype I]
    (P : Set V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (he : P = cell a b)
    (hb : Bornology.IsBounded P) (c : V) (hc : c ∈ P)
    (hcs : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
      f c = d → ∀ x ∈ P, f x = d) : CellData P where
  n := Fintype.card I
  a := fun i => a ((Fintype.equivFin I).symm i)
  b := fun i => b ((Fintype.equivFin I).symm i)
  eq_cell := he.trans (cell_reindex (Fintype.equivFin I) a b).symm
  bounded := hb
  center := c
  center_mem := hc
  center_support := hcs

lemma vertexMean_supports {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (hc : f (vertexMean s) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hv := (linear_vertexMean_eq_iff f hs (fun x hx =>
    hf x (subset_convexHull ℝ _ hx))).mp hc
  intro x hx
  exact linear_eq_on_affineSpan f hv (convexHull_subset_affineSpan (s : Set V) hx)

noncomputable def CellData.supportingFace {P Q : Set V} (p : CellData P)
    (s : Finset V) (hs : P = convexHull ℝ (s : Set V))
    (hQ : SupportingFace Q P) (hne : Q.Nonempty) : CellData Q := by
  classical
  refine Classical.choice ?_
  obtain ⟨f, d, hf, he⟩ := hQ
  let a' : Fin p.n ⊕ Bool → V →ₗ[ℝ] ℝ := Sum.elim p.a (fun j => if j then -f else f)
  let b' : Fin p.n ⊕ Bool → ℝ := Sum.elim p.b (fun j => if j then -d else d)
  have hcell : Q = cell a' b' := by
    ext x
    rw [he]
    constructor
    · rintro ⟨hx, hfx⟩ i
      change f x = d at hfx
      rcases i with i | i
      · exact (p.eq_cell ▸ hx) i
      · cases i <;> simp [a', b', hfx]
    · intro hx
      refine ⟨?_, le_antisymm (hx (Sum.inr false)) ?_⟩
      · rw [p.eq_cell]
        exact fun i => hx (Sum.inl i)
      · have hh := hx (Sum.inr true)
        simpa [a', b'] using hh
  have hQ' : SupportingFace Q (convexHull ℝ (s : Set V)) := hs ▸ ⟨f, d, hf, he⟩
  obtain ⟨t, _, ht⟩ := hQ'.eq_convexHull_subset
  have htn : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (ht ▸ hne))
  refine ⟨CellData.ofPresentation Q a' b' hcell (p.bounded.subset ?_) (vertexMean t) ?_ ?_⟩
  · exact fun x hx => (he.subset hx).1
  · rw [ht]
    exact vertexMean_mem_convexHull htn
  · intro g c hg heq x hx
    rw [ht] at hg hx
    exact vertexMean_supports htn g c hg heq x hx

lemma CellData.center_notMem_proper_face {P Q : Set V} (p : CellData P)
    (hQ : SupportingFace Q P) (hproper : Q ≠ P) : p.center ∉ Q := by
  obtain ⟨f, d, hf, rfl⟩ := hQ
  intro hc
  apply hproper
  exact Set.inter_eq_left.mpr (fun x hx => p.center_support f d hf hc.2 x hx)

lemma CellData.face_subset_boundary {P Q : Set V} (p : CellData P)
    (hQ : SupportingFace Q P) (hproper : Q ≠ P) :
    Q ⊆ radialBoundary p.a p.b p.center := by
  obtain ⟨f, d, hf, hQ⟩ := hQ
  have hc : f p.center < d := lt_of_le_of_ne (hf _ p.center_mem) (by
    intro he
    apply hproper
    rw [hQ]
    exact Set.inter_eq_left.mpr (fun x hx => p.center_support f d hf he x hx))
  intro x hx
  have hPx : x ∈ P := (hQ.subset hx).1
  apply mem_radialBoundary_of_supporting p.a p.b
    (p.eq_cell ▸ p.bounded) (p.eq_cell ▸ p.center_mem) (p.eq_cell ▸ hPx) f d
    (by simpa only [← p.eq_cell] using hf) hc
  exact (hQ.subset hx).2

lemma CellData.boundary_mem_face {P : Set V} (p : CellData P)
    {x : V} (hx : x ∈ radialBoundary p.a p.b p.center) :
    ∃ Q, SupportingFace Q P ∧ Q ≠ P ∧ x ∈ Q := by
  obtain ⟨hxp, i, hi, hic⟩ := hx
  refine ⟨P ∩ {y | p.a i y = p.b i}, ?_, ?_, ?_⟩
  · exact ⟨p.a i, p.b i, fun y hy => (p.eq_cell ▸ hy) i, rfl⟩
  · intro he
    have hc := he.symm.subset p.center_mem
    exact (ne_of_lt hic) hc.2
  · exact ⟨p.eq_cell.symm ▸ hxp, hi⟩

structure FiniteCellFamily (F : Finset (Set V)) : Prop where
  data : ∀ P ∈ F, Nonempty (CellData P)
  faces : ∀ P ∈ F, ∀ Q, SupportingFace Q P → Q.Nonempty → Q ∈ F
  inter : ∀ P ∈ F, ∀ Q ∈ F, SupportingFace (P ∩ Q) P

lemma FiniteCellFamily.erase_maximal {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P) :
    FiniteCellFamily (F.erase P) := by
  classical
  refine ⟨fun Q hQ => hF.data Q (Finset.mem_of_mem_erase hQ), ?_, ?_⟩
  · intro Q hQ R hR hne
    apply Finset.mem_erase.mpr
    refine ⟨?_, hF.faces Q (Finset.mem_of_mem_erase hQ) R hR hne⟩
    intro he
    subst R
    have hQP : Q ⊆ P := hm.2 (Finset.mem_of_mem_erase hQ) hR.subset
    exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hR.subset)
  · intro Q hQ R hR
    exact hF.inter Q (Finset.mem_of_mem_erase hQ) R (Finset.mem_of_mem_erase hR)

def familySpace (F : Finset (Set V)) : Set V := {x | ∃ P ∈ F, x ∈ P}

structure CellTriangulation (F : Finset (Set V)) where
  complex : Geometry.SimplicialComplex ℝ V
  finite : complex.faces.Finite
  space : complex.space = familySpace F
  trace : ∀ P ∈ F, RespectsSet complex P
  carrier : ∀ s ∈ complex.faces, ∃ P ∈ F, convexHull ℝ (s : Set V) ⊆ P

lemma CellTriangulation.respects_of_carrier {F : Finset (Set V)}
    (B : CellTriangulation F) (P : Set V)
    (hP : ∀ Q ∈ F, SupportingFace (Q ∩ P) Q) : RespectsSet B.complex P := by
  intro s hs
  obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
  obtain ⟨f, b, hf, he⟩ := hP Q hQ
  exact hull_inter_of_supporting_eq s Q P hsQ f b hf he

noncomputable def CellTriangulation.extend {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) : CellTriangulation F := by
  classical
  have hBP : RespectsSet B.complex P := B.respects_of_carrier P (fun Q hQ =>
    hF.inter Q (Finset.mem_of_mem_erase hQ) P hm.1)
  let T := restrictComplex B.complex P
  have hT : T.space = radialBoundary p.a p.b p.center := by
    rw [show T.space = B.complex.space ∩ P from
      restrictComplex_space_of_respects B.complex P hBP, B.space]
    ext x
    constructor
    · rintro ⟨⟨Q, hQ, hxQ⟩, hxP⟩
      have hproper : P ∩ Q ≠ P := by
        intro he
        have hPQ : P ⊆ Q := fun y hy => (he.symm.subset hy).2
        have hQP := hm.2 (Finset.mem_of_mem_erase hQ) hPQ
        exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hPQ)
      exact p.face_subset_boundary
        (hF.inter P hm.1 Q (Finset.mem_of_mem_erase hQ)) hproper ⟨hxP, hxQ⟩
    · intro hx
      obtain ⟨Q, hQ, hproper, hxQ⟩ := p.boundary_mem_face hx
      exact ⟨⟨Q, Finset.mem_erase.mpr ⟨hproper, hF.faces P hm.1 Q hQ ⟨x, hxQ⟩⟩,
        hxQ⟩, hQ.subset hxQ⟩
  have hspan : ∀ s ∈ T.faces, p.center ∉ affineSpan ℝ (s : Set V) :=
    fun s hs => center_notMem_affineSpan_boundaryFace p.a p.b T p.center hT.subset hs
  let C := coneComplex p.a p.b T p.center hT.subset hspan
  have hC : C.space = P := by
    rw [p.eq_cell]
    exact coneComplex_space_eq_cell p.a p.b (p.eq_cell ▸ p.bounded)
      T p.center (p.eq_cell ▸ p.center_mem) hT
  have hTC : T ≤ C := by
    intro s hs
    exact (mem_coneFaces_iff T p.center s).mpr (Or.inr (Or.inl hs))
  have hcross : ∀ s ∈ B.complex.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set V) ∩ convexHull ℝ (t : Set V) ⊆
        convexHull ℝ ((s : Set V) ∩ (t : Set V)) :=
    fun _ hs _ ht => cross_inter_of_respects B.complex C P hBP hC.subset hTC hs ht
  refine ⟨glueComplex B.complex C hcross, ?_, ?_, ?_, ?_⟩
  · exact glueComplex_finite B.complex C hcross B.finite
      (coneComplex_finite p.a p.b T p.center hT.subset hspan
        (restrictComplex_finite B.complex P B.finite))
  · rw [glueComplex_space, B.space, hC]
    ext x
    constructor
    · rintro (⟨Q, hQ, hxQ⟩ | hxP)
      · exact ⟨Q, Finset.mem_of_mem_erase hQ, hxQ⟩
      · exact ⟨P, hm.1, hxP⟩
    · rintro ⟨Q, hQ, hxQ⟩
      by_cases he : Q = P
      · exact Or.inr (he ▸ hxQ)
      · exact Or.inl ⟨Q, Finset.mem_erase.mpr ⟨he, hQ⟩, hxQ⟩
  · intro Q hQ s hs
    rcases hs with hs | hs
    · by_cases he : Q = P
      · exact he ▸ hBP s hs
      · exact B.trace Q (Finset.mem_erase.mpr ⟨he, hQ⟩) s hs
    · obtain ⟨f, b, hf, he⟩ := hF.inter P hm.1 Q hQ
      exact respectsSet_of_supporting_eq C P Q hC.subset f b hf he s hs
  · intro s hs
    rcases hs with hs | hs
    · obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      exact ⟨Q, Finset.mem_of_mem_erase hQ, hsQ⟩
    · exact ⟨P, hm.1, (C.convexHull_subset_space hs).trans hC.subset⟩

open scoped Classical

lemma CellTriangulation.mem_extend_faces {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) (s : Finset V) :
    s ∈ (B.extend hF hm p).complex.faces ↔
      s ∈ B.complex.faces ∨ s = {p.center} ∨
        ∃ t ∈ B.complex.faces, (t : Set V) ⊆ P ∧ s = insert p.center t := by
  classical
  change s ∈ B.complex.faces ∨ s ∈ coneFaces (restrictComplex B.complex P) p.center ↔ _
  rw [mem_coneFaces_iff]
  constructor
  · rintro (hs | hs | hs | ⟨t, ht, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inl hs.1
    · exact Or.inr (Or.inr ⟨t, ht.1, ht.2, rfl⟩)
  · rintro (hs | hs | ⟨t, ht, htP, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inr ⟨t, ⟨ht, htP⟩, rfl⟩))

lemma CellData.center_mem_iff_subset {P Q : Set V} (p : CellData Q)
    (h : SupportingFace (Q ∩ P) Q) : p.center ∈ P ↔ Q ⊆ P := by
  constructor
  · intro hp
    obtain ⟨f, d, hf, he⟩ := h
    have hc := he.subset ⟨p.center_mem, hp⟩
    intro x hx
    exact (he.symm.subset ⟨hx, p.center_support f d hf hc.2 x hx⟩).2
  · intro h
    exact h p.center_mem

noncomputable def chainFaces (F : Finset (Set V)) (c : Set V → V) : Set (Finset V) :=
  {s | ∃ t : Finset (Set V), t.Nonempty ∧ t ⊆ F ∧
      (t : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) ∧ s = t.image c}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma mem_chainFaces_erase_subset {F : Finset (Set V)} {P : Set V}
    {c : Set V → V} {s : Finset V} (hs : s ∈ chainFaces (F.erase P) c) :
    s ∈ chainFaces F c := by
  classical
  obtain ⟨t, hne, hsub, hchain, he⟩ := hs
  exact ⟨t, hne, hsub.trans (Finset.erase_subset _ _), hchain, he⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_maximal {F : Finset (Set V)} {P : Set V}
    (hm : Maximal (· ∈ F) P) (c : Set V → V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ↔ s ∈ chainFaces (F.erase P) c ∨
      s = {c P} ∨ ∃ t ∈ chainFaces (F.erase P) c,
        (t : Set V) ⊆ P ∧ s = insert (c P) t := by
  classical
  constructor
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    by_cases hP : P ∈ t
    · have hQP (Q : Set V) (hQ : Q ∈ t) : Q ⊆ P := by
        by_cases he : Q = P
        · exact he ▸ Set.Subset.refl _
        · rcases hchain hQ hP he with h | h
          · exact h
          · exact hm.2 (hsub hQ) h
      by_cases hempty : t.erase P = ∅
      · right; left
        have ht : t = {P} := by
          ext Q
          simp only [Finset.mem_singleton]
          constructor
          · intro hQ
            by_contra hn
            have hh : Q ∈ t.erase P := Finset.mem_erase.mpr ⟨hn, hQ⟩
            rw [hempty] at hh
            exact Finset.notMem_empty Q hh
          · rintro rfl; exact hP
        simp [ht]
      · right; right
        refine ⟨(t.erase P).image c, ?_, ?_, ?_⟩
        · exact ⟨t.erase P, Finset.nonempty_iff_ne_empty.mpr hempty,
            fun Q hQ => Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hQ).1, hsub (Finset.mem_of_mem_erase hQ)⟩,
            hchain.mono (Finset.erase_subset _ _), rfl⟩
        · intro x hx
          obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
          exact (hc Q (hsub (Finset.mem_of_mem_erase hQ))).mpr
            (hQP Q (Finset.mem_of_mem_erase hQ))
        · rw [← Finset.image_insert, Finset.insert_erase hP]
    · left
      exact ⟨t, hne, fun Q hQ => Finset.mem_erase.mpr
        ⟨fun he => hP (he ▸ hQ), hsub hQ⟩, hchain, rfl⟩
  · rintro (hs | rfl | ⟨s, ⟨t, hne, hsub, hchain, rfl⟩, hcorn, rfl⟩)
    · exact mem_chainFaces_erase_subset hs
    · exact ⟨{P}, Finset.singleton_nonempty _, by simpa using hm.1,
        by simp, by simp⟩
    · refine ⟨insert P t, Finset.insert_nonempty _ _, ?_, ?_, by simp⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact hm.1
        · exact Finset.mem_of_mem_erase (hsub hQ)
      · rw [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hchain, ?_⟩
        intro Q hQ _
        have hQF := Finset.mem_of_mem_erase (hsub hQ)
        have hQP := (hc Q hQF).mp (hcorn (Finset.mem_image_of_mem c hQ))
        exact ⟨Or.inr hQP, Or.inl hQP⟩

theorem exists_cellTriangulation (F : Finset (Set V)) (hF : FiniteCellFamily F) :
    Nonempty (CellTriangulation F) := by
  classical
  revert hF
  refine F.strongInductionOn ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · obtain ⟨P, hm⟩ := Finset.exists_maximal hne
    obtain ⟨B⟩ := ih (F.erase P) (Finset.erase_ssubset hm.1) (hF.erase_maximal hm)
    exact ⟨B.extend hF hm (hF.data P hm.1).some⟩
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    refine ⟨⟨⊥, ?_, ?_, ?_, ?_⟩⟩
    · simp [Geometry.SimplicialComplex.faces_bot]
    · ext x
      simp [familySpace, Geometry.SimplicialComplex.space_bot]
    · simp
    · simp [Geometry.SimplicialComplex.faces_bot]

theorem exists_cellTriangulation_chains (F : Finset (Set V))
    (hF : FiniteCellFamily F) (c : Set V → V)
    (hcenters : ∀ P ∈ F, ∃ p : CellData P, p.center = c P) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F c := by
  classical
  revert hF hcenters
  refine F.strongInductionOn ?_
  intro F ih hF hcenters
  by_cases hne : F.Nonempty
  · obtain ⟨P, hm⟩ := Finset.exists_maximal hne
    obtain ⟨B, hB⟩ := ih (F.erase P) (Finset.erase_ssubset hm.1)
      (hF.erase_maximal hm) (fun Q hQ => hcenters Q (Finset.mem_of_mem_erase hQ))
    obtain ⟨p, hp⟩ := hcenters P hm.1
    refine ⟨B.extend hF hm p, ?_⟩
    ext s
    rw [CellTriangulation.mem_extend_faces, hB, hp]
    exact (chainFaces_maximal hm c (fun Q hQ => by
      obtain ⟨q, hq⟩ := hcenters Q hQ
      rw [← hq]
      exact q.center_mem_iff_subset (hF.inter Q hQ P hm.1)) s).symm
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    let B : CellTriangulation (∅ : Finset (Set V)) := {
      complex := ⊥
      finite := by simp [Geometry.SimplicialComplex.faces_bot]
      space := by ext x; simp [familySpace, Geometry.SimplicialComplex.space_bot]
      trace := by simp
      carrier := by simp [Geometry.SimplicialComplex.faces_bot] }
    refine ⟨B, ?_⟩
    ext s
    simp only [B, Geometry.SimplicialComplex.faces_bot, Set.mem_empty_iff_false,
      false_iff]
    rintro ⟨t, ht, htF, _⟩
    have ht0 : t = ∅ := Finset.subset_empty.mp htF
    exact ht.ne_empty ht0

theorem exists_cellTriangulation_parents (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    Nonempty (CellTriangulation A) := by
  classical
  have hfin : (⋃ P ∈ (A : Set (Set V)),
      {Q : Set V | Q.Nonempty ∧ SupportingFace Q P}).Finite := by
    apply A.finite_toSet.biUnion
    intro P hP
    obtain ⟨s, hs⟩ := hvertices P hP
    rw [hs]
    exact finite_supportingFaces s
  let F := hfin.toFinset
  have hmem (Q : Set V) : Q ∈ F ↔ ∃ P ∈ A, Q.Nonempty ∧ SupportingFace Q P := by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_iUnion, Finset.mem_coe, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨P, hP, hQ⟩; exact ⟨P, hP, hQ⟩
    · rintro ⟨P, hP, hQ⟩; exact ⟨P, hP, hQ⟩
  have hsubset : A ⊆ F := by
    intro P hP
    apply (hmem P).mpr
    obtain ⟨p⟩ := hdata P hP
    exact ⟨P, hP, ⟨p.center, p.center_mem⟩, supportingFace_self P⟩
  have hF : FiniteCellFamily F := by
    refine ⟨?_, ?_, ?_⟩
    · intro Q hQ
      obtain ⟨P, hP, hne, hQP⟩ := (hmem Q).mp hQ
      obtain ⟨p⟩ := hdata P hP
      obtain ⟨s, hs⟩ := hvertices P hP
      exact ⟨p.supportingFace s hs hQP hne⟩
    · intro Q hQ R hRQ hne
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      obtain ⟨s, hs⟩ := hvertices P hP
      apply (hmem R).mpr
      refine ⟨P, hP, hne, ?_⟩
      rw [hs] at hQP ⊢
      exact hQP.trans_finite_hull hRQ
    · intro Q hQ R hR
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      obtain ⟨S, hS, _, hRS⟩ := (hmem R).mp hR
      obtain ⟨s, hs⟩ := hvertices P hP
      obtain ⟨t, _, ht⟩ := (hs ▸ hQP).eq_convexHull_subset
      exact hQP.inter_of_parent_inter hRS (hinter P hP S hS) ht
  obtain ⟨B⟩ := exists_cellTriangulation F hF
  refine ⟨⟨B.complex, B.finite, ?_, fun P hP => B.trace P (hsubset hP), ?_⟩⟩
  · rw [B.space]
    ext x
    constructor
    · rintro ⟨Q, hQ, hxQ⟩
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      exact ⟨P, hP, hQP.subset hxQ⟩
    · rintro ⟨P, hP, hxP⟩
      exact ⟨P, hsubset hP, hxP⟩
  · intro s hs
    obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    exact ⟨P, hP, hsQ.trans hQP.subset⟩

end BassTrace.Sparse.Cuts

end OAI

import OAI.RingTheory.BassTrace.AveragedChains

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.BarycentricChains

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence

variable {V Y : Type*} [LinearOrder V]

lemma cone_square (k : ℕ) (b : Y →₀ ℂ) (c : Degree Y k) :
    cone (k+1) b (cone k b c)=0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι ℂ b * (ExteriorAlgebra.ι ℂ b * (c : Chains.Algebra Y))=0
  rw [←mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]

lemma vertices_image {k : ℕ} (s : Set.powersetCard V k) :
    Finset.univ.image (vertices s)=s.val := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using vertices_range s

lemma labelMap_basis_recursion (b : Finset V → Y →₀ ℂ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) :
    labelMap b (k+1) (basis (k+1) s)=
      cone k (b s.val) (∑i : Fin (k+1),(-1:ℂ)^i.val • labelMap b k (basis k (eraseFace s i))) := by
  rw [basis_eq_wedge,labelMap_wedge_succ,vertices_image,←basis_eq_wedge,
    boundary_basis,map_sum]
  simp only [map_smul]

def filteredLabel (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ) :
    ∀k,Set.powersetCard V (k+1) → Degree Y (k+1)
  | 0,s => if ℓ s.val=0 then labelMap b 1 (basis 1 s) else 0
  | k+1,s => if ℓ s.val=k+1 then cone (k+1) (b s.val)
      (∑i : Fin (k+2),(-1:ℂ)^i.val • filteredLabel b ℓ k (eraseFace s i)) else 0

def filteredCount (ℓ : Finset V → ℕ) : ∀k,Set.powersetCard V (k+1) → ℕ
  | 0,s => if ℓ s.val=0 then 1 else 0
  | k+1,s => if ℓ s.val=k+1 then ∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) else 0

lemma labelMap_eq_filtered (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V))
    (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (hcard : ∀s∈P,s.card≤ℓ s+1)
    (hmono : ∀s∈P,∀t∈P,t⊆s→ℓ t≤ℓ s)
    (heq : ∀s∈P,∀t∈P,t⊆s→ℓ t=ℓ s→b t=b s)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P) (hℓ : ℓ s.val=k) :
    labelMap b (k+1) (basis (k+1) s)=filteredLabel b ℓ k s := by
  induction k with
  | zero => simp only [filteredLabel,hℓ,ite_true]
  | succ k ih =>
    rw [filteredLabel,ite_eq_left hℓ,labelMap_basis_recursion,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,map_smul]
    congr 1
    have hsub : (eraseFace s i).val⊆s.val := Finset.erase_subset _ _
    have hE : (eraseFace s i).val∈P := hP s.val hs _ hsub
      (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
    have hlow := hcard _ hE
    rw [(eraseFace s i).property] at hlow
    have hhigh := hmono s.val hs _ hE hsub
    rw [hℓ] at hhigh
    by_cases he : ℓ (eraseFace s i).val=k
    · rw [ih (eraseFace s i) hE he]
    · have he' : ℓ (eraseFace s i).val=k+1 := by omega
      have hb := heq s.val hs _ hE hsub (he'.trans hℓ.symm)
      rw [labelMap_basis_recursion,hb,cone_square]
      cases k <;> simp only [filteredLabel,ite_eq_right he,map_zero]

end

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence

variable {V : Type*} [LinearOrder V]

lemma eraseFace_injective {k : ℕ} (s : Set.powersetCard V (k+1)) :
    Function.Injective (eraseFace s) := by
  intro i j he
  apply (vertices s).injective
  exact (Finset.erase_inj s.val (vertices_mem s i)).mp (congrArg Subtype.val he)

lemma filteredCount_eq_zero (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : ℓ s.val≠k) : filteredCount ℓ k s=0 := by
  cases k <;> simp only [filteredCount,ite_eq_right hs]

lemma filteredCount_pos_level (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : 0<filteredCount ℓ k s) : ℓ s.val=k := by
  by_contra h
  rw [filteredCount_eq_zero ℓ k s h] at hs
  exact Nat.lt_irrefl 0 hs

lemma sum_facets_fiberwise (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B) (w : Set.powersetCard V (k+1) → ℕ) :
    ∑s∈A,∑i : Fin (k+2),w (eraseFace s i)=
      ∑t∈B,(incidencePairs A t).card*w t := by
  rw [←Finset.sum_product A Finset.univ (fun p=>w (eraseFace p.1 p.2))]
  symm
  calc
    _ = ∑t∈B,∑p∈incidencePairs A t,w (eraseFace p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [←Finset.sum_const_nat (s := incidencePairs A t)
        (f := fun p=>w (eraseFace p.1 p.2)) (fun p hp=>congrArg w (Finset.mem_filter.mp hp).2)]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp=>hAB p.1 (Finset.mem_product.mp hp).1 p.2) _

lemma incidencePairs_card_le (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (t : Set.powersetCard V (k+1)) :
    (incidencePairs A t).card≤(A.filter (fun s=>t.val⊆s.val)).card := by
  apply Finset.card_le_card_of_injOn (fun p=>p.1)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1,?_⟩
    rw [←he]
    exact Finset.erase_subset _ _
  · intro p hp q hq he
    apply Prod.ext he
    obtain ⟨_,hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hq⟩ := Finset.mem_filter.mp hq
    apply eraseFace_injective q.1
    simpa only [he] using hp.trans hq.symm

lemma filteredCount_sum_step (ℓ : Finset V → ℕ) (k : ℕ)
    (A : Finset (Set.powersetCard V (k+2))) (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B)
    (hbranch : ∀t∈B,0<filteredCount ℓ k t →
      ((A.filter (fun s=>ℓ s.val=k+1)).filter (fun s=>t.val⊆s.val)).card≤2) :
    ∑s∈A,filteredCount ℓ (k+1) s≤2*∑t∈B,filteredCount ℓ k t := by
  have he : (∑s∈A,filteredCount ℓ (k+1) s)=
      ∑s∈A.filter (fun s=>ℓ s.val=k+1),∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) := by
    simp only [filteredCount,Finset.sum_filter]
  rw [he,sum_facets_fiberwise k _ B (fun s hs=>hAB s (Finset.mem_filter.mp hs).1),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hw : 0<filteredCount ℓ k t
  · exact Nat.mul_le_mul_right _ ((incidencePairs_card_le k _ t).trans (hbranch t ht hw))
  · have hz : filteredCount ℓ k t=0 := by omega
    simp only [hz,mul_zero,le_refl]

end

section

open Set Finset

open scoped Classical

open OrientedIncidence Fundamental Sparse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace ActualFlags

variable (Q : Cuts.PointFiltration K n)

def level (s : Finset V) : ℕ := if hs : s∈(Q.T 0).faces then Q.faceLevel ⟨s,hs⟩ else 0

omit [LinearOrder V] in
lemma level_face (s : Finset V) (hs : s∈(Q.T 0).faces) :
    level Q s=Q.faceLevel ⟨s,hs⟩ := dite_eq_left hs

lemma count_pos_zero (k : ℕ) (s : Set.powersetCard V (k+1))
    (hs : s.val∈(Q.T 0).faces) (hp : 0<filteredCount (level Q) k s) :
    ∃z∈s.val,z∈Q.Z 0 := by
  induction k with
  | zero =>
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
    have hl := filteredCount_pos_level (level Q) 0 s hp
    rw [level_face Q s.val hs] at hl
    have hm := Q.mean_mem_faceLevel ⟨s.val,hs⟩
    rw [hl,hz] at hm
    simp only [Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul] at hm
    exact ⟨z,hz.symm ▸ Finset.mem_singleton_self z,hm⟩
  | succ k ih =>
    rw [filteredCount] at hp
    split_ifs at hp with hl
    · obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp hp
      have hE : (eraseFace s i).val∈(Q.T 0).faces :=
        (Q.T 0).down_closed hs (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
      obtain ⟨z,hz,hZ⟩ := ih (eraseFace s i) hE hi
      exact ⟨z,Finset.erase_subset _ _ hz,hZ⟩
    · omega

lemma localFaces_erase (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (k : ℕ) (s : Set.powersetCard V (k+2)) (hs : s∈faces L hL (k+2)) (i : Fin (k+2)) :
    eraseFace s i∈faces L hL (k+1) := by
  rw [mem_faces] at hs ⊢
  exact L.down_closed hs (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))

lemma count_sum_step (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k<n) :
    ∑s∈faces L hL (k+2),filteredCount (level Q) (k+1) s≤
      2*∑t∈faces L hL (k+1),filteredCount (level Q) k t := by
  apply filteredCount_sum_step (level Q) k _ _ (localFaces_erase L hL k)
  intro t ht hp
  obtain ⟨z,hzt,hz⟩ := count_pos_zero Q k t (hLT ((mem_faces L hL _ t).mp ht)) hp
  let B := ((faces L hL (k+2)).filter (fun s=>level Q s.val=k+1)).filter (fun s=>t.val⊆s.val)
  have hh : (B.image Subtype.val).card≤2 := by
    apply Q.flagged_cofaces_card_le_two hK hk hz t.property hzt
    intro E hE
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hs,hsub⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := hLT ((mem_faces L hL _ s).mp hs)
    refine ⟨hsf,s.property,?_,hsub⟩
    rw [level_face Q s.val hsf] at hl
    exact (Q.hull_mem_iff_level_le ⟨s.val,hsf⟩ (show k+1≤n by omega)).mpr hl.le
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh

lemma count_sum_bound (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k≤n) :
    ∑s∈faces L hL (k+1),filteredCount (level Q) k s≤
      2^k * ((faces L hL 1).filter (fun s=>level Q s.val=0)).card := by
  induction k with
  | zero => simp [filteredCount]
  | succ k ih =>
    calc
      _ ≤ 2*∑s∈faces L hL (k+1),filteredCount (level Q) k s :=
        count_sum_step Q hK L hL hLT k (by omega)
      _ ≤ 2*(2^k * _) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = _ := by rw [pow_succ]; ac_rfl

end ActualFlags

end

section

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse

variable {V Y : Type*} [LinearOrder V]

def coneLeft (k : ℕ) (c : Degree Y k) : (Y →₀ ℂ) →ₗ[ℂ] Degree Y (k+1) where
  toFun b:=cone k b c
  map_add' a b:=by ext; simp only [cone_coe,map_add,add_mul,Submodule.coe_add]
  map_smul' r b:=by ext; simp only [cone_coe,map_smul,smul_mul_assoc,Submodule.coe_smul,RingHom.id_apply]

lemma cone_single_wedge (k : ℕ) (y : Y) (v : Fin k → Y) :
    cone k (Finsupp.single y 1) (wedge k v)=wedge (k+1) (Fin.cons y v) := by
  apply Subtype.ext
  simp only [cone_coe,wedge,exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.cons_zero,Matrix.vecTail,Function.comp_def,Fin.cons_succ]

lemma cone_uniform_wedge (k : ℕ) (s : Finset Y) (v : Fin k → Y) :
    cone k (uniformVector s) (wedge k v)=
      ∑y∈s,(s.card : ℂ)⁻¹ • wedge (k+1) (Fin.cons y v) := by
  change coneLeft k (wedge k v) (uniformVector s)=_
  rw [uniformVector,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : Finsupp.single y (s.card : ℂ)⁻¹=(s.card : ℂ)⁻¹ • Finsupp.single y 1 := by simp
  rw [he,map_smul]
  exact congrArg ((s.card : ℂ)⁻¹ • ·) (cone_single_wedge k y v)

lemma norm_uniform_cone_wedge (k : ℕ) (W s : Finset Y) (hs : s.Nonempty) (hsW : s⊆W)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ) (M : ℝ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M)
    (v : Fin k → Y) (hv : ∀i,v i∈W) :
    ‖ψ (cone k (uniformVector s) (wedge k v))‖≤M := by
  rw [cone_uniform_wedge,map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_y∈s,(s.card : ℝ)⁻¹*M := by
      apply Finset.sum_le_sum
      intro y hy
      rw [map_smul,norm_smul,norm_inv,Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left (hM (Fin.cons y v) ?_) (inv_nonneg.mpr (Nat.cast_nonneg _))
      intro i
      exact Fin.cases (hsW hy) hv i
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul, ←mul_assoc, mul_inv_cancel₀,one_mul]
      exact_mod_cast hs.card_pos.ne'

lemma filteredLabel_norm (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V)) (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (W : Finset Y)
    (hb : ∀s∈P,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (M : ℝ) (_hM0 : 0≤M)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M) :
    ‖ψ (filteredLabel b ℓ k s)‖≤M*(filteredCount ℓ k s : ℝ) := by
  induction k with
  | zero =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [labelMap_basis_recursion,Fin.sum_univ_one]
      simp only [Fin.val_zero,pow_zero,one_smul]
      rw [basis_eq_wedge,
        labelMap_wedge_zero,hsb,Nat.cast_one,mul_one]
      exact norm_uniform_cone_wedge 0 W t ht htW ψ M hM _ (fun i=>Fin.elim0 i)
    · simp only [map_zero,norm_zero,Nat.cast_zero,mul_zero,le_refl]
  | succ k ih =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [map_sum,map_sum,Nat.cast_sum,Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,map_smul,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      apply ih (eraseFace s i)
        (hP s.val hs _ (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega)))
        (ψ.comp (cone (k+1) (b s.val)))
      intro v hv
      change ‖ψ (cone (k+1) (b s.val) (wedge (k+1) v))‖≤M
      rw [hsb]
      exact norm_uniform_cone_wedge (k+1) W t ht htW ψ M hM v hv
    · simpa only [map_zero,norm_zero,Nat.cast_zero,mul_zero] using (le_refl (0:ℝ))

end

open Set Finset

open scoped Classical

open Oriented ChainHomotopy OrientedIncidence Sparse Fundamental

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

lemma norm_sign_complex_le (r : ℝ) : ‖(Real.sign r : ℂ)‖≤1 := by
  rcases Real.sign_apply_eq r with h|h|h <;> simp [h]

lemma labeled_chain_bound (Q : Cuts.PointFiltration K n)
    (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces)
    (b : Finset V → Y →₀ ℂ)
    (heq : ∀s∈L.faces,∀t∈L.faces,t⊆s→
      ActualFlags.level Q t=ActualFlags.level Q s→b t=b s)
    (W : Finset Y) (hb : ∀s∈L.faces,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (p : V → (Fin (n+1) → ℝ))
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀v : Fin (n+1) → Y,(∀i,v i∈W)→‖ψ (wedge (n+1) v)‖≤M) :
    ‖ψ (labelMap b (n+1) (chain (faces L hL (n+1)) p))‖≤
      M*(2^n * ((faces L hL 1).filter (fun s=>ActualFlags.level Q s.val=0)).card : ℕ) := by
  have hcard s (hs : s∈L.faces) : s.card≤ActualFlags.level Q s+1 := by
    rw [ActualFlags.level_face Q s (hLT hs)]
    exact Q.final_face_card_le_level hK ⟨s,hLT hs⟩
  have hmono s (hs : s∈L.faces) t (ht : t∈L.faces) (hts : t⊆s) :
      ActualFlags.level Q t≤ActualFlags.level Q s := by
    rw [ActualFlags.level_face Q t (hLT ht),ActualFlags.level_face Q s (hLT hs)]
    exact Q.faceLevel_mono ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts
  calc
    _ ≤ ∑s∈faces L hL (n+1),‖ψ ((labelMap b (n+1))
        ((Real.sign (Matrix.det (fun i=>p (vertices s i))) : ℂ) • basis (n+1) s))‖ := by
      rw [chain,map_sum,map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑s∈faces L hL (n+1),M*(filteredCount (ActualFlags.level Q) n s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsf := (mem_faces L hL _ s).mp hs
      have hl : ActualFlags.level Q s.val=n := by
        have hlow := hcard s.val hsf
        rw [s.property] at hlow
        have hhigh := Q.faceLevel_le ⟨s.val,hLT hsf⟩
        rw [←ActualFlags.level_face Q s.val (hLT hsf)] at hhigh
        omega
      rw [map_smul,map_smul,norm_smul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (norm_sign_complex_le _)).trans
      rw [labelMap_eq_filtered b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) hcard hmono heq n s hsf hl]
      exact filteredLabel_norm b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) W hb M hM0 n s hsf ψ hM
    _ = M*((∑s∈faces L hL (n+1),filteredCount (ActualFlags.level Q) n s : ℕ):ℝ) := by
      rw [Nat.cast_sum,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast ActualFlags.count_sum_bound Q hK L hL hLT n le_rfl) hM0

end BassTrace.BarycentricChains

namespace BassTrace.BarycentricChains.ActualFlags

open Set Finset MeasureTheory

open scoped Classical

open Sparse Fundamental

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

lemma singleton_mean (s : Set.powersetCard V 1) : s.val={Cuts.vertexMean s.val} := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
  simp only [hz,Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul]

lemma zeroFaces_card_le (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    ((faces L hL 1).filter (fun s=>level Q s.val=0)).card≤hfin.toFinset.card := by
  apply Finset.card_le_card_of_injOn (fun s=>Cuts.vertexMean s.val)
  · intro s hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := (mem_faces L hL _ s).mp hs
    change Cuts.vertexMean s.val∈hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_,hLS (L.convexHull_subset_space hsf
      (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hsf)))⟩
    rw [level_face Q s.val (hLT hsf)] at hl
    exact hl ▸ Q.mean_mem_faceLevel ⟨s.val,hLT hsf⟩
  · intro s _ t _ he
    apply Subtype.ext
    dsimp only at he
    rw [singleton_mean s,singleton_mean t,he]

lemma zeroFaces_real_le_count [MeasurableSpace V] [MeasurableSingletonClass V]
    (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    (((faces L hL 1).filter (fun s=>level Q s.val=0)).card : ℝ)≤
      (Measure.count (Q.Z 0∩S)).toReal := by
  rw [Measure.count_apply_finite _ hfin,ENNReal.toReal_natCast]
  exact_mod_cast zeroFaces_card_le Q L hL hLT S hLS hfin

end BassTrace.BarycentricChains.ActualFlags

end

end OAI

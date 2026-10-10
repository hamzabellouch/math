import Mathlib
import OAI.Topology.ArtinGroups.Complexes.DiagonalVertex
import OAI.Topology.ArtinGroups.Quivers.StringArrow

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
namespace StringFunctor
variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N

lemma arrowImage_mul_of_not_composable (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (h : (U).target p ≠ (U).source q) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q = 0 := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hp : j.old = (U).target p
  · rw [arrowImage_eq_zero_left Q step hstep N hN _ _ _ _ _ k (fun hh => h (hp.symm.trans hh)),mul_zero]
  · rw [arrowImage_eq_zero_right Q step hstep N hN _ _ _ _ i _ hp,zero_mul]

include hstep hN in
omit [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B] in
lemma coefficient_square (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p q : StringArrow step N) (hb : Q.reverse p.base=q.base) (hm : p.right=q.left)
    (c : J) (hc : N p.left c) (hc' : N q.right c) :
    (∑ d : {d : J // N p.right d},
      if (if step p.base then N c d else c=d) then
        coefficient step N orient μ A p c d * coefficient step N orient μ A q d c
      else 0) = if p.left=q.right then μ c / μ p.left else 0 := by
  have hsQ : step q.base=step p.base := by rw [← hb,hstep]
  cases hs : step p.base
  · have hqs : step q.base=false := hsQ.trans hs
    have hpp : p.left=p.right := by simpa only [hs,Bool.false_eq_true,ite_false,ite_true] using (show (if step p.base then N p.left p.right else p.left=p.right) from p.property)
    have hqq : q.left=q.right := by simpa only [hqs,Bool.false_eq_true,ite_false,ite_true] using (show (if step q.base then N q.left q.right else q.left=q.right) from q.property)
    have haa : p.left=q.right := hpp.trans (hm.trans hqq)
    have haq : q.left=p.left := hm.symm.trans hpp.symm
    have hNc : N p.right c := hpp ▸ hc
    rw [ite_eq_left haa,Finset.sum_eq_single (⟨c,hNc⟩ : {d : J // N p.right d})]
    · simp only [hs,Bool.false_eq_true,ite_false,ite_true,coefficient,hqs,haq]
      have hO : orient q.base = !(orient p.base) := by rw [← hb,ho]
      rw [hO]
      cases orient p.base <;> simp
    · intro d hd hdc
      have hn : c ≠ (d : J) := by
        intro h
        apply hdc
        exact Subtype.ext h.symm
      simp [hn]
    · simp
  · have hqs : step q.base=true := hsQ.trans hs
    have hpp : N p.left p.right := by simpa only [hs,Bool.false_eq_true,ite_false,ite_true] using (show (if step p.base then N p.left p.right else p.left=p.right) from p.property)
    have hqq : N q.left q.right := by simpa only [hqs,Bool.false_eq_true,ite_false,ite_true] using (show (if step q.base then N q.left q.right else q.left=q.right) from q.property)
    simp only [hs,ite_true,coefficient,hqs]
    have heq (f : J → K) :
        (∑ d : {d : J // N p.right d}, if N c d then f d else 0) =
          ∑ d ∈ GraphConnection.neighbors N p.right ∩ GraphConnection.neighbors N c, f d := by
      rw [← Finset.sum_subtype (GraphConnection.neighbors N p.right)
        (GraphConnection.mem_neighbors N p.right) (fun d => if N c d then f d else 0),
        ← Finset.sum_filter]
      congr 1
      ext d
      simp
    rw [heq (fun d => GraphConnection.crossing μ A p.left p.right c d * GraphConnection.crossing μ A q.left q.right d c)]
    simpa only [← hm] using GraphConnection.crossing_square N μ hμ δ A hA hroot hPF
      p.left q.right p.right c (hN hpp) (hm.symm ▸ hqq) (hN hc) (hN hc')

omit [Fintype V] in
lemma arrowImage_entry_product (orient : B → Bool) (μ : J → K) (A : K)
    (p q : StringArrow step N) (i j k : I)
    (hb : Q.reverse p.base=q.base) (hm : (U).target p=(U).source q)
    (hi : i.old=(U).source p) (hk : k.old=(U).target q) (hl : i.label=k.label) :
    arrowImage Q step hstep N hN orient μ A p i j *
      arrowImage Q step hstep N hN orient μ A q j k =
    if j.old=(U).target p then
      if (if step p.base then N i.label j.label else i.label=j.label) then
        (coefficient step N orient μ A p i.label j.label *
          coefficient step N orient μ A q j.label k.label) • Zigzag.tokenBasis U i.new
      else 0
    else 0 := by
  by_cases hj : j.old=(U).target p
  swap
  · rw [ite_eq_right hj,arrowImage_eq_zero_right Q step hstep N hN _ _ _ p i j hj,zero_mul]
  rw [ite_eq_left hj]
  unfold arrowImage
  have hpold : i.old=(U).source p ∧ j.old=(U).target p := ⟨hi,hj⟩
  have hqold : j.old=(U).source q ∧ k.old=(U).target q := ⟨hj.trans hm,hk⟩
  simp only [hi,hj,hk,hm,and_self,ite_true]
  by_cases hp' : (if step p.base then N i.label j.label else i.label=j.label)
  swap
  · simp only [dite_eq_right hp',ite_eq_right hp',zero_mul]
  simp only [dite_eq_left hp',ite_eq_left hp']
  have hq' : (if step q.base then N j.label k.label else j.label=k.label) := by
    rw [← hb,hstep,← hl]
    cases hs : step p.base <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true] at hp' ⊢
    · exact hp'.symm
    · exact hN hp'
  rw [dite_eq_left hq',smul_mul_assoc,Algebra.mul_smul_comm,Zigzag.arrowBasis_mul_arrowBasis]
  have hr : (U).reverse (⟨(p.base,i.label,j.label),hp'⟩ : StringArrow step N) =
      ⟨(q.base,j.label,k.label),hq'⟩ :=
    (reverse_eq_iff Q step hstep N hN _ _).2 ⟨hb,rfl,hl⟩
  rw [ite_eq_left hr,smul_smul]
  congr 2
  apply Prod.ext
  · exact (congrArg Prod.fst hi).symm
  · rfl

lemma arrowImage_mul_arrowImage (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p q : StringArrow step N) :
    arrowImage Q step hstep N hN orient μ A p *
      arrowImage Q step hstep N hN orient μ A q =
      if (U).reverse p=q then tokenImage Q step hstep N hN μ ((U).source p) else 0 := by
  by_cases hb : Q.reverse p.base=q.base
  swap
  · rw [arrowImage_mul_of_not_reverse_base Q step hstep N hN _ _ _ _ _ hb]
    have hr : (U).reverse p ≠ q := fun hh => hb (congrArg StringArrow.base hh)
    rw [ite_eq_right hr]
  by_cases hm : (U).target p=(U).source q
  swap
  · rw [arrowImage_mul_of_not_composable Q step hstep N hN _ _ _ _ _ hm]
    rw [ite_eq_right (fun hh => hm (hh ▸ (U).source_reverse p).symm)]
  apply Matrix.ext
  intro i k
  by_cases hi : i.old=(U).source p
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [arrowImage_eq_zero_left Q step hstep N hN _ _ _ _ _ _ hi,zero_mul]
    rw [hz]
    split_ifs with hr
    · simp [tokenImage,hi]
    · rfl
  by_cases hk : k.old=(U).target q
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [arrowImage_eq_zero_right Q step hstep N hN _ _ _ _ _ _ hk,mul_zero]
    rw [hz]
    split_ifs with hr
    · have hik : i ≠ k := by
        intro H
        subst k
        apply hk
        rw [← hr,(U).target_reverse]
        exact hi
      simp [tokenImage,hik]
    · rfl
  by_cases hl : i.label=k.label
  swap
  · have hz : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun j _ => arrowImage_entry_mul_of_not_reverse
        Q step hstep N hN orient μ A p q i j k (Or.inr hl))
    rw [hz]
    split_ifs with hr
    · have hik : i ≠ k := fun H => hl (congrArg StringIndex.label H)
      simp [tokenImage,hik]
    · rfl
  have hc : N p.left i.label := by
    change N ((U).source p).2 i.label
    rw [← hi]
    exact i.property
  have hc' : N q.right i.label := by
    rw [hl]
    change N ((U).target q).2 k.label
    rw [← hk]
    exact k.property
  have hs : (arrowImage Q step hstep N hN orient μ A p *
        arrowImage Q step hstep N hN orient μ A q) i k =
      (if p.left=q.right then μ i.label / μ p.left else 0) • Zigzag.tokenBasis U i.new := by
    rw [Matrix.mul_apply]
    simp_rw [arrowImage_entry_product Q step hstep N hN orient μ A p q i _ k hb hm hi hk hl]
    rw [sum_over N ((U).target p)]
    change (∑ d : {d : J // N p.right d},
      if (if step p.base then N i.label d else i.label=d) then
        (coefficient step N orient μ A p i.label d * coefficient step N orient μ A q d k.label) •
          Zigzag.tokenBasis U i.new else 0) = _
    rw [← hl]
    have hscalar := coefficient_square Q step hstep N hN orient ho μ hμ δ A hA hroot hPF
      p q hb (congrArg Prod.snd hm) i.label hc hc'
    rw [← hscalar,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs <;> simp
  rw [hs]
  by_cases ha : p.left=q.right
  · have hr : (U).reverse p=q := (reverse_eq_iff Q step hstep N hN p q).2
      ⟨hb,congrArg Prod.snd hm,ha⟩
    have hik : i=k := by
      apply StringIndex.ext
      · rw [hi,hk,← hr,(U).target_reverse]
      · exact hl
    subst k
    rw [ite_eq_left hr,ite_eq_left ha]
    change (μ i.label / μ p.left) • Zigzag.tokenBasis U i.new =
      tokenImage Q step hstep N hN μ ((U).source p) i i
    unfold tokenImage
    rw [ite_eq_left ⟨rfl,hi⟩]
    rfl
  · have hr : (U).reverse p ≠ q := fun H => ha (congrArg StringArrow.right H)
    simp [ha,hr]

noncomputable def pathImage (orient : B → Bool) (μ : J → K) (A : K) :
    Path (V × J) (StringArrow step N) → Matrix I I (Zigzag U K)
  | .inl a => unitImage Q step hstep N hN a
  | .inr (.inl p) => arrowImage Q step hstep N hN orient μ A p
  | .inr (.inr a) => tokenImage Q step hstep N hN μ a

noncomputable def linearMap (orient : B → Bool) (μ : J → K) (A : K) :
    Zigzag U K →ₗ[K] Matrix I I (Zigzag U K) :=
  (Zigzag.pathBasis U).constr K (pathImage Q step hstep N hN orient μ A)

@[simp] lemma linearMap_pathBasis (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) :
    linearMap Q step hstep N hN orient μ A (Zigzag.pathBasis U p) =
      pathImage Q step hstep N hN orient μ A p :=
  Module.Basis.constr_basis _ _ _ _

lemma pathImage_left (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I) :
    Zigzag.vertexId U i.new * pathImage Q step hstep N hN orient μ A p i j =
      pathImage Q step hstep N hN orient μ A p i j := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage]
    split_ifs <;> simp [Zigzag.vertexId_mul_self]
  · exact arrowImage_left Q step hstep N hN orient μ A p i j
  · simp only [pathImage,tokenImage]
    split_ifs
    · rw [Algebra.mul_smul_comm, ← Zigzag.pathBasis_token]
      exact congrArg ((μ i.label/μ a.2) • ·) (Zigzag.pathBasis_left U (.inr (.inr i.new)))
    · simp

lemma pathImage_right (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I) :
    pathImage Q step hstep N hN orient μ A p i j * Zigzag.vertexId U j.new =
      pathImage Q step hstep N hN orient μ A p i j := by
  rcases p with a|p|a
  · simp only [pathImage,unitImage]
    split_ifs with h
    · rw [h.1]; exact Zigzag.vertexId_mul_self (K := K) U j.new
    · simp
  · exact arrowImage_right Q step hstep N hN orient μ A p i j
  · simp only [pathImage,tokenImage]
    split_ifs with h
    · rw [h.1,smul_mul_assoc, ← Zigzag.pathBasis_token]
      exact congrArg ((μ j.label/μ a.2) • ·) (Zigzag.pathBasis_right U (.inr (.inr j.new)))
    · simp

omit [Fintype V] in
lemma pathImage_support (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (i j : I)
    (h : i.old ≠ Path.source U p ∨ j.old ≠ Path.target U p) :
    pathImage Q step hstep N hN orient μ A p i j = 0 := by
  rcases p with a|p|a
  · change (if i=j ∧ i.old=a then Zigzag.vertexId U i.new else 0) = 0
    rw [ite_eq_right]
    rintro ⟨rfl,ha⟩
    exact h.elim (fun H => H ha) (fun H => H ha)
  · change (if i.old=(U).source p ∧ j.old=(U).target p then _ else 0) = 0
    rw [ite_eq_right]
    rintro ⟨ha,hb⟩
    exact h.elim (fun H => H ha) (fun H => H hb)
  · change (if i=j ∧ i.old=a then (μ i.label/μ a.2) • Zigzag.tokenBasis U i.new else 0) = 0
    rw [ite_eq_right]
    rintro ⟨rfl,ha⟩
    exact h.elim (fun H => H ha) (fun H => H ha)

lemma unitImage_pathImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) :
    unitImage Q step hstep N hN a * pathImage Q step hstep N hN orient μ A p =
    if Path.source U p = a then pathImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [unitImage_mul Q step hstep N hN a _ (pathImage_left Q step hstep N hN orient μ A p)]
  by_cases hp : Path.source U p=a
  · rw [ite_eq_left hp]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inl (by simpa [hp] using hi))]
  · rw [ite_eq_right hp]
    by_cases hi : i.old=a
    · rw [ite_eq_left hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inl (by simpa [hi,eq_comm] using hp))]; rfl
    · rw [ite_eq_right hi]; rfl

lemma pathImage_unitImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) :
    pathImage Q step hstep N hN orient μ A p * unitImage Q step hstep N hN a =
    if Path.target U p = a then pathImage Q step hstep N hN orient μ A p else 0 := by
  apply Matrix.ext
  intro i j
  rw [mul_unitImage Q step hstep N hN a _ (pathImage_right Q step hstep N hN orient μ A p)]
  by_cases hp : Path.target U p=a
  · rw [ite_eq_left hp]
    by_cases hi : j.old=a
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inr (by simpa [hp] using hi))]
  · rw [ite_eq_right hp]
    by_cases hi : j.old=a
    · rw [ite_eq_left hi,pathImage_support Q step hstep N hN orient μ A p i j
        (Or.inr (by simpa [hi,eq_comm] using hp))]; rfl
    · rw [ite_eq_right hi]; rfl

omit [Fintype V] in
lemma pathImage_positive (orient : B → Bool) (μ : J → K) (A : K)
    (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) (i j : I) :
    (pathImage Q step hstep N hN orient μ A p i j).vertex = 0 := by
  rcases p with a|p|a
  · exact (hp rfl).elim
  · simp only [pathImage,arrowImage]
    split_ifs <;> simp only [Zigzag.vertex_smul,Zigzag.vertex_zero]
    all_goals change (_ : K) • (0 : V × J → K) = 0
    all_goals exact smul_zero _
  · simp only [pathImage,tokenImage]
    split_ifs <;> simp only [Zigzag.vertex_smul,Zigzag.vertex_zero]
    all_goals change (_ : K) • (0 : V × J → K) = 0
    all_goals exact smul_zero _

lemma tokenImage_pathImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) :
    tokenImage Q step hstep N hN μ a * pathImage Q step hstep N hN orient μ A p = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  unfold tokenImage
  split_ifs
  · rw [smul_mul_assoc,Zigzag.tokenBasis_mul_positive U _ _
      (pathImage_positive Q step hstep N hN orient μ A p hp k j),smul_zero]
  · exact zero_mul _

lemma pathImage_tokenImage (orient : B → Bool) (μ : J → K) (A : K)
    (a : V × J) (p : Path (V × J) (StringArrow step N)) (hp : Path.length p ≠ 0) :
    pathImage Q step hstep N hN orient μ A p * tokenImage Q step hstep N hN μ a = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  unfold tokenImage
  split_ifs
  · rw [Algebra.mul_smul_comm,Zigzag.positive_mul_tokenBasis U _ _
      (pathImage_positive Q step hstep N hN orient μ A p hp i k),smul_zero]
  · exact mul_zero _

lemma linearMap_mul (orient : B → Bool)
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (x y : Zigzag U K) :
    linearMap Q step hstep N hN orient μ A (x*y) =
      linearMap Q step hstep N hN orient μ A x * linearMap Q step hstep N hN orient μ A y := by
  apply Zigzag.map_mul_of_pathBasis
  intro p q
  rw [linearMap_pathBasis,linearMap_pathBasis]
  rcases p with a|p|a
  · rw [Zigzag.pathBasis_vertex,Zigzag.vertexId_mul_pathBasis]
    simp only [apply_ite,map_zero,linearMap_pathBasis,pathImage]
    exact (unitImage_pathImage Q step hstep N hN orient μ A a q).symm
  · rcases q with b|q|b
    · rw [Zigzag.pathBasis_vertex,Zigzag.pathBasis_mul_vertexId]
      simp only [apply_ite,map_zero,linearMap_pathBasis]
      exact (pathImage_unitImage Q step hstep N hN orient μ A b (.inr (.inl p))).symm
    · rw [Zigzag.pathBasis_arrow,Zigzag.pathBasis_arrow,Zigzag.arrowBasis_mul_arrowBasis]
      simp only [apply_ite,map_zero, ← Zigzag.pathBasis_token,linearMap_pathBasis,pathImage]
      exact (arrowImage_mul_arrowImage Q step hstep N hN orient ho μ hμ δ A hA hroot hPF p q).symm
    · rw [Zigzag.pathBasis_arrow,Zigzag.pathBasis_token,
        Zigzag.positive_mul_tokenBasis U b _ rfl,map_zero]
      exact (pathImage_tokenImage Q step hstep N hN orient μ A b (.inr (.inl p)) (by norm_num [Path.length])).symm
  · rcases q with b|q|b
    · rw [Zigzag.pathBasis_vertex,Zigzag.pathBasis_mul_vertexId]
      simp only [apply_ite,map_zero,linearMap_pathBasis]
      exact (pathImage_unitImage Q step hstep N hN orient μ A b (.inr (.inr a))).symm
    · rw [Zigzag.pathBasis_token,Zigzag.pathBasis_arrow,
        Zigzag.tokenBasis_mul_positive U a _ rfl,map_zero]
      exact (tokenImage_pathImage Q step hstep N hN orient μ A a (.inr (.inl q)) (by norm_num [Path.length])).symm
    · rw [Zigzag.pathBasis_token,Zigzag.pathBasis_token,
        Zigzag.tokenBasis_mul_positive U a _ rfl,map_zero]
      exact (tokenImage_pathImage Q step hstep N hN orient μ A a (.inr (.inr b)) (by norm_num [Path.length])).symm

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI

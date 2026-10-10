import OAI.Topology.EilenbergGanea.AffineTransport
import OAI.Topology.EilenbergGanea.SeedConnection

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace LevelTransport
open TraceWords AffineTransport

variable {V : Type*} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
variable (hdim : ∀ s : Finset V, (s : Set V).Pairwise L.Adj → s.card ≤ 3)

def point (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) : TrianglePoint V :=
  ⟨artinDirection L g,by
    apply mem_triangleSet.mpr
    refine ⟨(traceCounts L (artinNormalTrace L g)).support,
      hdim _ (traceCounts_support_clique L _),⟨?_,?_⟩,?_⟩
    · exact traceDirection_nonneg L _
    · exact traceDirection_sum L hg
    · intro v hv
      simp only [Finsupp.notMem_support_iff] at hv
      simp [artinDirection,traceDirection,hv]⟩

@[simp] theorem point_val (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) :
    (point L hdim g hg : V → ℝ) = artinDirection L g := rfl

theorem point_mem_support (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g))
    {v : V} (hv : (point L hdim g hg : V → ℝ) v ≠ 0) :
    v ∈ (traceCounts L (artinNormalTrace L g)).support := by
  by_contra h
  have he := Finsupp.notMem_support_iff.mp h
  exact hv (by simp [point,artinDirection,traceDirection,he])

theorem point_clique (g : ArtinGroup L) (hg : 0 < traceLength L (artinNormalTrace L g)) :
    CliquePoint L (point L hdim g hg) := by
  intro a ha v hv
  by_cases hav : a = v
  · exact Or.inl hav
  · exact Or.inr (traceCounts_support_clique L _
      (point_mem_support L hdim g hg ha) (point_mem_support L hdim g hg hv) hav)

/-- Both hypotheses refer to actual reduced Artin lengths, not an assumed word metric. -/
theorem point_step (g : ArtinGroup L) (x : Letter V)
    (hg : 0 < traceLength L (artinNormalTrace L g))
    (hgx : 0 < traceLength L (artinNormalTrace L (g * letterValue (artinGenerator L) x)))
    (N : ℕ) (hNg : N ≤ traceLength L (artinNormalTrace L g))
    (hNgx : N ≤ traceLength L (artinNormalTrace L (g * letterValue (artinGenerator L) x))) :
    Compatible L (point L hdim g hg) (point L hdim (g * letterValue (artinGenerator L) x) hgx) ∧
    dist (point L hdim g hg) (point L hdim (g * letterValue (artinGenerator L) x) hgx) ≤
      2 / (N+1 : ℝ) := by
  classical
  obtain ⟨hs,n,_,hn,hbd⟩ := artinDirection_right_step L g x hg hgx
  have hNn : N ≤ n := by rcases hn with ⟨he,_⟩ | ⟨he,_⟩ <;> omega
  constructor
  · intro v w hv hw
    by_cases he : v = w
    · exact Or.inl he
    · apply Or.inr
      apply hs _ _ he
      · rcases hv with hv | hv
        · exact Finset.mem_union_left _ (point_mem_support L hdim g hg hv)
        · exact Finset.mem_union_right _ (point_mem_support L hdim _ hgx hv)
      · rcases hw with hw | hw
        · exact Finset.mem_union_left _ (point_mem_support L hdim g hg hw)
        · exact Finset.mem_union_right _ (point_mem_support L hdim _ hgx hw)
  · have hc : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hNn 1
    have hd : 0 < (N : ℝ) + 1 := by positivity
    have hfrac : 2 / (n+1 : ℝ) ≤ 2 / (N+1 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hd hc
    apply le_trans ?_ hfrac
    change dist (artinDirection L g) (artinDirection L (g * letterValue (artinGenerator L) x)) ≤ _
    apply (dist_pi_le_iff (by positivity)).mpr
    intro v
    rw [Real.dist_eq,abs_sub_comm]
    exact le_trans (Finset.single_le_sum (fun w _ => abs_nonneg (artinDirection L (g * letterValue (artinGenerator L) x) w - artinDirection L g w)) (Finset.mem_univ v)) hbd


/-- The integral level downstairs; the action is by left multiplication by the height kernel. -/
abbrev NegativeLevel (N : ℕ) := {g : ArtinGroup L // (height L g).toAdd = -(N : ℤ)}

omit [Fintype V] [LinearOrder V] in
theorem negative_level_length (N : ℕ) {g : ArtinGroup L}
    (hg : (height L g).toAdd = -(N : ℤ)) :
    N ≤ traceLength L (artinNormalTrace L g) := by
  have hh := height_abs_le_traceLength L g
  rw [hg,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  exact_mod_cast hh

def levelPoint (N : ℕ) (hN : 0 < N) (g : NegativeLevel L N) : TrianglePoint V :=
  point L hdim g (lt_of_lt_of_le hN (negative_level_length L N g.property))

@[simp] theorem levelPoint_val (N : ℕ) (hN : 0 < N) (g : NegativeLevel L N) :
    (levelPoint L hdim N hN g : V → ℝ) = artinDirection L g := rfl

def upperVertex (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (v : V) :
    NegativeLevel L (N-1) :=
  ⟨(g : ArtinGroup L) * artinGenerator L v,by
    rw [map_mul,height_generator]
    change (height L (g : ArtinGroup L)).toAdd + 1 = _
    rw [g.property]
    omega⟩

def edgeVertex (N : ℕ) (g : NegativeLevel L N) (q r : V) : NegativeLevel L N :=
  ⟨(g : ArtinGroup L) * artinGenerator L q * (artinGenerator L r)⁻¹,by
    simp only [map_mul,map_inv,height_generator]
    change (height L (g : ArtinGroup L)).toAdd + 1 + -1 = _
    rw [g.property]
    omega⟩

omit [Fintype V] [LinearOrder V] in
theorem edgeVertex_reverse (N : ℕ) (g : NegativeLevel L N) (q r : V) :
    edgeVertex L N (edgeVertex L N g q r) r q = g := by
  apply Subtype.ext
  change (g : ArtinGroup L) * _ * _ * _ * _ = _
  group

omit [Fintype V] [LinearOrder V] in
theorem upperVertex_reverse (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) :
    upperVertex L N hN (edgeVertex L N g q r) r = upperVertex L N hN g q := by
  apply Subtype.ext
  dsimp only [edgeVertex,upperVertex]
  group

theorem upperPoint_step (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (v : V) :
    Compatible L (levelPoint L hdim N (by omega) g)
      (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g v)) ∧
    dist (levelPoint L hdim N (by omega) g)
      (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g v)) ≤ 2 / (N : ℝ) := by
  let hu := upperVertex L N hN g v
  have hlen := negative_level_length L N g.property
  have hlen' := negative_level_length L (N-1) hu.property
  dsimp only [hu,upperVertex] at hlen'
  have H := point_step L hdim (g : ArtinGroup L) (v,true)
    (lt_of_lt_of_le (by omega : 0 < N) hlen)
    (by simpa only [letterValue_positive] using lt_of_lt_of_le (by omega : 0 < N-1) hlen')
    (N-1) (le_trans (Nat.sub_le N 1) hlen)
    (by simpa only [letterValue_positive] using hlen')
  have he : ((N-1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast (show (N-1 : ℕ) + 1 = N by omega)
  simpa only [levelPoint,upperVertex,letterValue_positive,he] using H

variable (h : V → V → SU2) (Q : V → ℍ)

def edgeLabel (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) : SU2 :=
  edgeTransport h Q (levelPoint L hdim N (by omega) g)
    (levelPoint L hdim (N-1) (by omega) (upperVertex L N hN g q))
    (levelPoint L hdim N (by omega) (edgeVertex L N g q r))

theorem edgeLabel_reverse (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) (q r : V) :
    edgeLabel L hdim h Q N hN (edgeVertex L N g q r) r q =
      (edgeLabel L hdim h Q N hN g q r)⁻¹ := by
  have h₁ := (upperPoint_step L hdim N hN g q).1
  have h₂ := (upperPoint_step L hdim N hN (edgeVertex L N g q r) r).1
  rw [upperVertex_reverse] at h₂
  unfold edgeLabel
  rw [edgeVertex_reverse,upperVertex_reverse]
  exact edgeTransport_reverse L h Q hf hQ h₁ (compatible_symm L h₂)

theorem edgeLabel_uniform (hQ : GeneralPosition h Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ∀ hN : 1 < N, ∀ g : NegativeLevel L N, ∀ q r : V,
      dist (edgeLabel L hdim h Q N hN g q r) 1 < ε := by
  obtain ⟨δ,hδ,H⟩ := edgeTransport_uniform h Q hQ hε
  obtain ⟨M,hM⟩ := exists_nat_gt (2 / δ)
  refine ⟨M,?_⟩
  intro N hMN hN g q r
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbound : 2 / (N : ℝ) < δ := by
    apply (div_lt_iff₀ hN0).mpr
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hh := (div_lt_iff₀ hδ).mp hM
    nlinarith
  apply H
  · exact lt_of_le_of_lt (upperPoint_step L hdim N hN g q).2 hbound
  · have hh := (upperPoint_step L hdim N hN (edgeVertex L N g q r) r).2
    rw [upperVertex_reverse,dist_comm] at hh
    exact lt_of_le_of_lt hh hbound


omit [LinearOrder V] in
/-- Six compatible generator pieces around a level triangle lie in one flat chart
once the three edge images are uniformly short. -/
theorem triangle_of_short (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (b c d u v w : TrianglePoint V) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : 4 * δ < 1 / (Fintype.card V + 1 : ℝ))
    (hb : CliquePoint L b) (hc : CliquePoint L c) (hd : CliquePoint L d)
    (hu : CliquePoint L u) (hv : CliquePoint L v) (hw : CliquePoint L w)
    (hbu : Compatible L b u) (huc : Compatible L u c)
    (hcv : Compatible L c v) (hvd : Compatible L v d)
    (hdw : Compatible L d w) (hwb : Compatible L w b)
    (dbu : dist b u ≤ δ) (duc : dist u c ≤ δ)
    (dcv : dist c v ≤ δ) (dvd : dist v d ≤ δ)
    (_ddw : dist d w ≤ δ) (dwb : dist w b ≤ δ) :
    edgeTransport h Q b u c * edgeTransport h Q c v d * edgeTransport h Q d w b = 1 := by
  have dbc : dist b c ≤ 2 * δ := by linarith [dist_triangle b u c]
  have dbv : dist b v ≤ 3 * δ := by linarith [dist_triangle b c v]
  have dbd : dist b d ≤ 4 * δ := by linarith [dist_triangle b v d]
  have dbw : dist b w ≤ δ := by simpa only [dist_comm] using dwb
  obtain ⟨a,ha⟩ := exists_large_coordinate b
  apply edgeTransport_triangle L h Q hf hQ b c d u v w hbu huc hcv hvd hdw hwb
  · exact nearby_star L ha hb (by simpa using lt_of_lt_of_le hδ (le_of_lt (by linarith : δ < 1 / (Fintype.card V + 1 : ℝ))))
  · exact nearby_star L ha hc (by linarith)
  · exact nearby_star L ha hd (lt_of_le_of_lt dbd hsmall)
  · exact nearby_star L ha hu (by linarith)
  · exact nearby_star L ha hv (by linarith)
  · exact nearby_star L ha hw (by linarith)

/-- Every oriented three-edge loop with these actual level endpoints is flat.
In particular both kinds of sections of a three-cube are covered. -/
theorem edgeLabel_triangle (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) (hsize : 8 / (N : ℝ) < 1 / (Fintype.card V + 1 : ℝ))
    (g₀ g₁ g₂ : NegativeLevel L N) (q₀ r₀ q₁ r₁ q₂ r₂ : V)
    (e₀ : edgeVertex L N g₀ q₀ r₀ = g₁)
    (e₁ : edgeVertex L N g₁ q₁ r₁ = g₂)
    (e₂ : edgeVertex L N g₂ q₂ r₂ = g₀) :
    edgeLabel L hdim h Q N hN g₀ q₀ r₀ *
      edgeLabel L hdim h Q N hN g₁ q₁ r₁ *
      edgeLabel L hdim h Q N hN g₂ q₂ r₂ = 1 := by
  have h₀ := upperPoint_step L hdim N hN g₀ q₀
  have h₁ := upperPoint_step L hdim N hN g₁ q₁
  have h₂ := upperPoint_step L hdim N hN g₂ q₂
  have j₀ := upperPoint_step L hdim N hN g₁ r₀
  have j₁ := upperPoint_step L hdim N hN g₂ r₁
  have j₂ := upperPoint_step L hdim N hN g₀ r₂
  rw [← e₀,upperVertex_reverse,e₀] at j₀
  rw [← e₁,upperVertex_reverse,e₁] at j₁
  rw [← e₂,upperVertex_reverse,e₂] at j₂
  unfold edgeLabel
  rw [e₀,e₁,e₂]
  apply triangle_of_short L h Q hf hQ _ _ _ _ _ _ (2/(N : ℝ))
  · positivity
  · convert hsize using 1; ring
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact point_clique L hdim _ _
  · exact h₀.1
  · exact compatible_symm L j₀.1
  · exact h₁.1
  · exact compatible_symm L j₁.1
  · exact h₂.1
  · exact compatible_symm L j₂.1
  · exact h₀.2
  · simpa only [dist_comm] using j₀.2
  · exact h₁.2
  · simpa only [dist_comm] using j₁.2
  · exact h₂.2
  · simpa only [dist_comm] using j₂.2


/-- A vertex of the simplex is also an honest point of its two-skeleton. -/
def vertexPoint (v : V) : TrianglePoint V :=
  ⟨fun w => if v = w then 1 else 0,by
    apply mem_triangleSet.mpr
    refine ⟨{v},by simp,⟨?_,?_⟩,?_⟩
    · intro w; dsimp only; split_ifs <;> norm_num
    · simp
    · intro w hw
      simp only [Finset.mem_singleton] at hw
      simp [Ne.symm hw]⟩

@[simp] theorem vertexPoint_val (v w : V) :
    (vertexPoint v : V → ℝ) w = if v = w then 1 else 0 := rfl

theorem star_vertex {a v : V} (hav : Related L a v) : Star L a (vertexPoint v) := by
  intro w hw
  have he : v = w := by by_contra hh; exact hw (by simp [vertexPoint,hh])
  simpa only [← he] using hav

omit [Fintype V] [LinearOrder V] in
theorem negative_powers_upper {q r : V} (hqr : L.Adj q r) (n m : ℕ) :
    (artinGenerator L q)⁻¹ ^ (n+1) * (artinGenerator L r)⁻¹ ^ m * artinGenerator L q =
      (artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m := by
  have hc := (adjacent_generators_commute L hqr).inv_right.pow_right m
  calc
    _ = (artinGenerator L q)⁻¹ ^ n *
        ((artinGenerator L q)⁻¹ * ((artinGenerator L r)⁻¹ ^ m * artinGenerator L q)) := by
      simp only [pow_succ]; group
    _ = (artinGenerator L q)⁻¹ ^ n *
        ((artinGenerator L q)⁻¹ * (artinGenerator L q * (artinGenerator L r)⁻¹ ^ m)) := by
      rw [← hc.eq]
    _ = _ := by group

/-- Negative commuting powers remain exactly in their two-coordinate face. -/
theorem powersPoint_star {q r : V} (hqr : L.Adj q r) (n m : ℕ)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m))) :
    Star L q (point L hdim ((artinGenerator L q)⁻¹ ^ n * (artinGenerator L r)⁻¹ ^ m) hg) := by
  intro v hv
  by_cases hqv : q = v
  · exact Or.inl hqv
  by_cases hrv : r = v
  · exact Or.inr (hrv ▸ hqr)
  exfalso
  apply hv
  rw [point_val,direction_negative_commuting_powers L hqr]
  simp [hqv,hrv]

/-- Constant endpoint in the q-direction, stated with a concrete positive height. -/
theorem powersPoint_first {q r : V} (hqr : L.Adj q r) (N : ℕ) (hN : 0 < N)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0))) :
    point L hdim ((artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0) hg =
      vertexPoint q := by
  apply Subtype.ext
  funext v
  rw [point_val,vertexPoint_val,direction_negative_commuting_powers L hqr]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  by_cases hv : q = v <;> simp [hv,hn]

theorem powersPoint_last {q r : V} (hqr : L.Adj q r) (N : ℕ) (hN : 0 < N)
    (hg : 0 < traceLength L (artinNormalTrace L
      ((artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N))) :
    point L hdim ((artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N) hg =
      vertexPoint r := by
  apply Subtype.ext
  funext v
  rw [point_val,vertexPoint_val,direction_negative_commuting_powers L hqr]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  by_cases hv : r = v <;> simp [hv,hn]

def powerVertex (N : ℕ) (q r : V) (j : ℕ) : NegativeLevel L N :=
  ⟨(artinGenerator L q)⁻¹ ^ (N - min j N) * (artinGenerator L r)⁻¹ ^ min j N,by
    simp only [map_mul,map_pow,map_inv,height_generator]
    change (N-min j N : ℕ) • (-1 : ℤ) + (min j N : ℕ) • (-1 : ℤ) = _
    simp only [nsmul_eq_mul,mul_neg,mul_one]
    have hh : min j N ≤ N := min_le_right _ _
    omega⟩

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_step (N : ℕ) {q r : V} (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    edgeVertex L N (powerVertex L N q r j) q r = powerVertex L N q r (j+1) := by
  apply Subtype.ext
  dsimp only [powerVertex,edgeVertex]
  rw [min_eq_left (by omega : j ≤ N),min_eq_left (by omega : j+1 ≤ N)]
  have he : N-j = (N-(j+1))+1 := by omega
  rw [he,negative_powers_upper L hqr,pow_succ]
  group

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_upper (N : ℕ) (hN : 1 < N) {q r : V}
    (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    (upperVertex L N hN (powerVertex L N q r j) q : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ (N-(j+1)) * (artinGenerator L r)⁻¹ ^ j := by
  dsimp only [powerVertex,upperVertex]
  rw [min_eq_left (by omega : j ≤ N)]
  have he : N-j = (N-(j+1))+1 := by omega
  rw [he,negative_powers_upper L hqr]

theorem powerVertex_star (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) (j : ℕ) :
    Star L q (levelPoint L hdim N hN (powerVertex L N q r j)) :=
  powersPoint_star L hdim hqr _ _ _

theorem powerVertex_upper_star (N : ℕ) (hN : 1 < N) {q r : V}
    (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    Star L q (levelPoint L hdim (N-1) (by omega)
      (upperVertex L N hN (powerVertex L N q r j) q)) := by
  unfold levelPoint
  generalize_proofs hpos
  simp only [powerVertex_upper L N hN hqr hj] at hpos ⊢
  exact powersPoint_star L hdim hqr _ _ _

theorem powerLabel_chart (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) {j : ℕ} (hj : j < N) :
    edgeLabel L hdim h Q N hN (powerVertex L N q r j) q r =
      chartTransport h Q q (levelPoint L hdim N (by omega) (powerVertex L N q r j))
        (levelPoint L hdim N (by omega) (powerVertex L N q r (j+1))) := by
  have hb := upperPoint_step L hdim N hN (powerVertex L N q r j) q
  have hc := upperPoint_step L hdim N hN (edgeVertex L N (powerVertex L N q r j) q r) r
  rw [upperVertex_reverse] at hc
  unfold edgeLabel
  rw [edgeTransport_chart L h Q hf hQ hb.1 (compatible_symm L hc.1)
    (powerVertex_star L hdim N (by omega) hqr j) (powerVertex_upper_star L hdim N hN hqr hj)]
  · rw [powerVertex_step L N hqr hj]
  · rw [powerVertex_step L N hqr hj]
    exact powerVertex_star L hdim N (by omega) hqr (j+1)


/-- Directed walks retain the chosen generator pair, including parallel edges. -/
inductive Walk (N : ℕ) : NegativeLevel L N → NegativeLevel L N → Type _
  | nil (g : NegativeLevel L N) : Walk N g g
  | cons {g k : NegativeLevel L N} (q r : V) (hqr : L.Adj q r)
      (p : Walk N (edgeVertex L N g q r) k) : Walk N g k

namespace Walk
variable {L} {N : ℕ}

def append {g k l : NegativeLevel L N} : Walk L N g k → Walk L N k l → Walk L N g l
  | .nil _, p => p
  | .cons q r hqr p, t => .cons q r hqr (append p t)

def cast {g k g' k' : NegativeLevel L N} (p : Walk L N g k)
    (hg : g = g') (hk : k = k') : Walk L N g' k' := hg ▸ hk ▸ p

end Walk

def walkProduct (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N} : Walk L N g k → SU2
  | .nil _ => 1
  | .cons (g := g) q r _ p => edgeLabel L hdim h Q N hN g q r * walkProduct N hN p

@[simp] theorem walkProduct_nil (N : ℕ) (hN : 1 < N) (g : NegativeLevel L N) :
    walkProduct L hdim h Q N hN (.nil g) = 1 := rfl

@[simp] theorem walkProduct_cons (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N}
    (q r : V) (hqr : L.Adj q r) (p : Walk L N (edgeVertex L N g q r) k) :
    walkProduct L hdim h Q N hN (.cons q r hqr p) =
      edgeLabel L hdim h Q N hN g q r * walkProduct L hdim h Q N hN p := rfl

@[simp] theorem walkProduct_append (N : ℕ) (hN : 1 < N) {g k l : NegativeLevel L N}
    (p : Walk L N g k) (t : Walk L N k l) :
    walkProduct L hdim h Q N hN (p.append t) =
      walkProduct L hdim h Q N hN p * walkProduct L hdim h Q N hN t := by
  induction p with
  | nil => simp [Walk.append]
  | cons q r hqr p ih => simp [Walk.append,ih,mul_assoc]

@[simp] theorem walkProduct_cast (N : ℕ) (hN : 1 < N) {g k g' k' : NegativeLevel L N}
    (p : Walk L N g k) (hg : g = g') (hk : k = k') :
    walkProduct L hdim h Q N hN (p.cast hg hk) = walkProduct L hdim h Q N hN p := by
  subst g'; subst k'; rfl

/-- The entire subdivided edge has the exact endpoint transport, not merely a limit. -/
theorem exists_powerWalk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) (k : ℕ) (hk : k ≤ N) :
    ∃ p : Walk L N (powerVertex L N q r 0) (powerVertex L N q r k),
      walkProduct L hdim h Q N hN p =
        chartTransport h Q q (levelPoint L hdim N (by omega) (powerVertex L N q r 0))
          (levelPoint L hdim N (by omega) (powerVertex L N q r k)) := by
  induction k with
  | zero => exact ⟨.nil _,by simp [chartTransport]⟩
  | succ k ih =>
      obtain ⟨p,hp⟩ := ih (by omega)
      let t : Walk L N (powerVertex L N q r k)
          (edgeVertex L N (powerVertex L N q r k) q r) := .cons q r hqr (.nil _)
      let t' := t.cast rfl (powerVertex_step L N hqr (by omega : k < N))
      refine ⟨p.append t',?_⟩
      rw [walkProduct_append,hp]
      simp only [t',walkProduct_cast,t,walkProduct_cons,walkProduct_nil,mul_one]
      rw [powerLabel_chart L hdim h Q hf hQ N hN hqr (by omega),chartTransport_trans]

def pureVertex (N : ℕ) (q : V) : NegativeLevel L N :=
  ⟨(artinGenerator L q)⁻¹ ^ N,by
    simp only [map_pow,map_inv,height_generator]
    change N • (-1 : ℤ) = -(N : ℤ)
    simp⟩

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_zero (N : ℕ) (q r : V) :
    powerVertex L N q r 0 = pureVertex L N q := by apply Subtype.ext; simp [powerVertex,pureVertex]

omit [Fintype V] [LinearOrder V] in
theorem powerVertex_last (N : ℕ) (q r : V) :
    powerVertex L N q r N = pureVertex L N r := by apply Subtype.ext; simp [powerVertex,pureVertex]

def vertexGauge (v : V) : SU2 := gauge h Q v (vertexPoint v)

theorem levelPoint_power_zero (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) :
    levelPoint L hdim N hN (powerVertex L N q r 0) = vertexPoint q := by
  unfold levelPoint
  have hh : (powerVertex L N q r 0 : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ N * (artinGenerator L r)⁻¹ ^ 0 := by simp [powerVertex]
  simp only [hh]
  exact powersPoint_first L hdim hqr N hN _

theorem levelPoint_power_last (N : ℕ) (hN : 0 < N) {q r : V} (hqr : L.Adj q r) :
    levelPoint L hdim N hN (powerVertex L N q r N) = vertexPoint r := by
  unfold levelPoint
  have hh : (powerVertex L N q r N : ArtinGroup L) =
      (artinGenerator L q)⁻¹ ^ 0 * (artinGenerator L r)⁻¹ ^ N := by simp [powerVertex]
  simp only [hh]
  exact powersPoint_last L hdim hqr N hN _

theorem exists_expanded_edge (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (hqr : L.Adj q r) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N r),
      walkProduct L hdim h Q N hN p =
        (vertexGauge h Q q)⁻¹ * h q r * vertexGauge h Q r := by
  obtain ⟨p,hp⟩ := exists_powerWalk L hdim h Q hf hQ N hN hqr N le_rfl
  refine ⟨p.cast (powerVertex_zero L N q r) (powerVertex_last L N q r),?_⟩
  rw [walkProduct_cast,hp,levelPoint_power_zero L hdim N (by omega) hqr,
    levelPoint_power_last L hdim N (by omega) hqr]
  unfold chartTransport vertexGauge
  rw [gauge_transition L h Q hf hQ (Or.inr hqr)
    (star_vertex L (Or.inr hqr)) (star_vertex L (Or.inl rfl))]
  group

omit [Fintype V] [LinearOrder V] in
def graphWalkProduct {a b : V} : L.Walk a b → SU2
  | .nil => 1
  | .cons (u := u) (v := v) _ p => h u v * graphWalkProduct p

theorem exists_expanded_walk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q r : V} (w : L.Walk q r) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N r),
      walkProduct L hdim h Q N hN p =
        (vertexGauge h Q q)⁻¹ * graphWalkProduct L h w * vertexGauge h Q r := by
  induction w with
  | nil => exact ⟨.nil _,by simp [graphWalkProduct]⟩
  | @cons q t r hqt w ih =>
      obtain ⟨p,hp⟩ := exists_expanded_edge L hdim h Q hf hQ N hN hqt
      obtain ⟨s,hs⟩ := ih
      refine ⟨p.append s,?_⟩
      rw [walkProduct_append,hp,hs]
      simp only [graphWalkProduct]
      group

omit [Fintype V] [LinearOrder V] in
theorem graphWalkProduct_eq_zipWith {a b : V} (w : L.Walk a b) :
    graphWalkProduct L h w = (List.zipWith h w.support w.support.tail).prod := by
  induction w with
  | nil => simp [graphWalkProduct]
  | @cons q t r hqt w ih =>
      cases w with
      | nil => simp [graphWalkProduct]
      | cons htl p => simpa only [graphWalkProduct,SimpleGraph.Walk.support_cons,
          List.tail_cons,List.zipWith_cons_cons,List.prod_cons] using congrArg (h q t * ·) ih

/-- A nontrivial seed holonomy survives every sufficiently translated level. -/
theorem exists_nontrivial_level_walk (hf : FlatConnection L h) (hQ : GeneralPosition h Q)
    (N : ℕ) (hN : 1 < N) {q : V} (w : L.Walk q q)
    (hw : graphWalkProduct L h w ≠ 1) :
    ∃ p : Walk L N (pureVertex L N q) (pureVertex L N q),
      walkProduct L hdim h Q N hN p ≠ 1 := by
  obtain ⟨p,hp⟩ := exists_expanded_walk L hdim h Q hf hQ N hN w
  refine ⟨p,?_⟩
  rw [hp]
  intro he
  apply hw
  calc
    graphWalkProduct L h w = vertexGauge h Q q *
      ((vertexGauge h Q q)⁻¹ * graphWalkProduct L h w * vertexGauge h Q q) *
        (vertexGauge h Q q)⁻¹ := by group
    _ = 1 := by rw [he]; group


namespace Walk
variable {L} {N : ℕ}
omit [Fintype V] [LinearOrder V] in
def eval (a : NegativeLevel L N → V → V → SU2)
    {g k : NegativeLevel L N} : Walk L N g k → SU2
  | .nil _ => 1
  | .cons (g := g) q r _ p => a g q r * eval a p
end Walk

theorem walkProduct_eq_eval (N : ℕ) (hN : 1 < N) {g k : NegativeLevel L N}
    (p : Walk L N g k) :
    walkProduct L hdim h Q N hN p = p.eval (edgeLabel L hdim h Q N hN) := by
  induction p with
  | nil => rfl
  | cons q r hqr p ih => simp only [walkProduct,Walk.eval,ih]

end LevelTransport

namespace SourceTransport
open LevelTransport AffineTransport

def seedWalk : seedGraph.Walk (.inl (.inl none)) (.inl (.inl none)) :=
  SimpleGraph.Walk.ofSupport SeedConnection.roseLoop
    (by simp [SeedConnection.roseLoop]) SeedConnection.roseLoop_edges

theorem seedWalk_support : seedWalk.support = SeedConnection.roseLoop :=
  SimpleGraph.Walk.support_ofSupport _ _

theorem seedWalk_product_ne : graphWalkProduct seedGraph SeedConnection.connection seedWalk ≠ 1 := by
  rw [graphWalkProduct_eq_zipWith,seedWalk_support]
  exact SeedConnection.roseLoop_nontrivial

/-- Actual small flat transport for the fixed source level graph. There are no
representation, direction-map, local-chart, or nontriviality hypotheses here. -/
theorem source_small_labels (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 < N ∧ ∃ a : NegativeLevel seedGraph N → SeedCell → SeedCell → SU2,
      (∀ g q r, a (edgeVertex seedGraph N g q r) r q = (a g q r)⁻¹) ∧
      (∀ g q r, dist (a g q r) 1 < ε) ∧
      (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
        edgeVertex seedGraph N g₀ q₀ r₀ = g₁ →
        edgeVertex seedGraph N g₁ q₁ r₁ = g₂ →
        edgeVertex seedGraph N g₂ q₂ r₂ = g₀ →
        a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1) ∧
      ∃ (g : NegativeLevel seedGraph N) (p : Walk seedGraph N g g), p.eval a ≠ 1 := by
  let : LinearOrder SeedCell := LinearOrder.lift' (Fintype.equivFin SeedCell)
    (Fintype.equivFin SeedCell).injective
  obtain ⟨Q,hQ⟩ := exists_generalPosition SeedConnection.connection
  have hf : FlatConnection seedGraph SeedConnection.connection :=
    fun _ _ _ hab hbc hac => SeedConnection.connection_flat hab hbc hac
  obtain ⟨M,hM⟩ := edgeLabel_uniform seedGraph SeedConnection.clique_card_le_three
    SeedConnection.connection Q hQ hε
  let D := Fintype.card SeedCell + 1
  let N := max M (8 * D + 2)
  have hMN : M ≤ N := le_max_left _ _
  have hNbound : 8 * D + 2 ≤ N := le_max_right _ _
  have hN : 1 < N := by omega
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsize : 8 / (N : ℝ) < 1 / (Fintype.card SeedCell + 1 : ℝ) := by
    have hBN : (8 : ℝ) * D + 2 ≤ N := by exact_mod_cast hNbound
    have hDcast : (D : ℝ) = (Fintype.card SeedCell : ℝ) + 1 := by simp [D]
    rw [← hDcast]
    apply (div_lt_div_iff₀ hNr hD).mpr
    nlinarith
  let a := edgeLabel seedGraph SeedConnection.clique_card_le_three
    SeedConnection.connection Q N hN
  refine ⟨N,hN,a,?_,?_,?_,?_⟩
  · exact edgeLabel_reverse seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN
  · exact hM N hMN hN
  · exact edgeLabel_triangle seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN hsize
  · obtain ⟨p,hp⟩ := exists_nontrivial_level_walk seedGraph SeedConnection.clique_card_le_three
      SeedConnection.connection Q hf hQ N hN seedWalk seedWalk_product_ne
    refine ⟨_,p,?_⟩
    rwa [walkProduct_eq_eval] at hp

end SourceTransport
end EilenbergGanea



end

end OAI

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import VerifiedAgora.tagger

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


/-%%
This files gathers definitions and basic properties about rectangles.
%%-/

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

lemma symm_re : Rectangle (w.re + z.im * I) (z.re + w.im * I) = Rectangle z w := by
  simp [Rectangle, uIcc_comm]

end Rectangle

/-%%
The border of a rectangle is the union of its four sides.
\begin{definition}[RectangleBorder]\label{RectangleBorder}\lean{RectangleBorder}\leanok
A Rectangle's border, given corners $z$ and $w$ is the union of the four sides.
\end{definition}
%%-/
/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

@[target]
lemma Square_apply (p : ℂ) (cpos : c > 0) :
    Square p c = Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by sorry
@[target, simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t := by sorry
@[target, simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm := by sorry
/-- The axis-parallel complex rectangle with opposite corners `z` and `w` is complex product
  of two intervals, which is also the convex hull of the four corners. Golfed from mathlib4\#9598.-/
@[target]
lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by sorry
/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
@[target]
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by sorry
@[target]
lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  simp only [Rectangle, mem_reProdIm, Set.uIcc_of_le zRe_lt_wRe, Set.uIcc_of_le zIm_lt_wIm,
    mem_Icc]
  tauto
  simp only [Rectangle, mem_reProdIm, Set.uIcc_of_le zRe_lt_wRe, Set.uIcc_of_le zIm_lt_wIm,
    mem_Icc]
  tauto
@[target]
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simp only [Square]
 
 
 
 
  rw [show -↑(-c) - ↑(-c) * I + p = ↑c + ↑c * I + p by push_cast; ring,
      show ↑(-c) + ↑(-c) * I + p = -↑c - ↑c *
  exact Rectangle.symm
@[target]
theorem Set.
@[target]
theorem Set.left_not_mem_uIoo {a b 
theorem 
theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact left_mem_Ioo
  · rw [uIoo_of_gt h]; exact right_mem_Ioo.mp
@[target]
theorem Set.right_not_mem_uIoo {a 
theore

theore
theorem Set.right_not_mem_uIoo {a b : ℝ} : b
  rcases le_or_lt a b with h | h
  · r
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact right_mem_Io

  · rw [uIoo_of_gt h]; exact left_mem_Ioo
@[target]
  · rw [uIoo_of_gt h]; exact left_mem_Ioo
@[target]
theorem Set.ne_left_of_mem_uIoo {a b c : ℝ
  fun h => Set.left_not_mem_uI
theorem Set.ne_left_of_mem_uIoo {a b c : ℝ
  fun h => Set.left_not_mem_uIoo (h ▸ hc)

@[target]
theorem Set.ne_right_of_mem_uIoo {a b c :
@[target]
theorem Set.ne_right_of_mem_uIoo {a 
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  f
  fun h => Set.right_not_mem_uIoo (h ▸ hc)
@[tar
  fun h => Set.right_not_mem_uIoo (h ▸ hc)
@[target]
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w :=
@[target]
lemma rect_subs
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w :=
@[target]
lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  constructor
  · intro h
    exact ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  · intro ⟨hz', hw'⟩ x hx

  · intro ⟨hz', hw'⟩ x hx
    simp only [Rectangle, mem_reProdIm] at hx hz' hw' ⊢
    exact ⟨Set.uIcc_subset_uIcc hz'.1 hw'.1 hx.1, Set.uIcc_subset_uIcc hz'.2 hw'.2 hx.2⟩
@[target]
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ 
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : 
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff]
  simp only [Rectangle, mem_reProdIm, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, sub_zero, Complex.ofReal_im, Complex.I_im, mul_one, Complex.add_im,
    Complex.mul_im, zero_mul]
  constructor
  · constructor
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
    · exact Set.mem_uIcc_of_le (by lina
  · constructor
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
@[target]
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [rect_subset_iff]
  simp only [Rectangle, mem_reProdIm]
  exact ⟨⟨Set.mem_uIcc_of_le (by linarith) (by linarith),

          Set.mem_uIcc_of_le (by linar
      
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩,
         ⟨Set.mem_uIcc_of_le (by linarith) (by linarith),
          Set.mem_uIcc_of_le (by linarith) (by linarith)⟩⟩
@[target]
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff]
  simp only [Rectangle, mem_reProdIm, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, sub_zero, C
    Complex.mul_im, zero_mul]
  constructor
  · constructor
   
    · exact Set.mem_uIc
    ·
    · exact Set.mem_uIc
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
  · constructor
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
    · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
@[target]
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ 
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangl
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [rect_subset_i
  simp only [Rectangle, mem_reProdIm]
  exact ⟨⟨Set.mem_uIcc_of_le (by linarith) (b
@[target]
lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  rw [Set.disjoint_singleton_right]
  intro hp

  intro hp
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  obtain ⟨hre_z, hre_w, him_z, him_w⟩ := h
  rcases hp with ((
 
  rcases hp with ((
  · exact him_z him
 
  · exact him_z him
  · exact hre_z hre
  · exact him_w him
  · exact hre_w hre
@[t
  · exact him_z him
  · exact hre_z hre
  · exact him_w him
  · exact hre_w hre
@[target]
lemma rectangle_subset_punctured_re
  · exact hre_w hre
@[target]
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ 
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {
  obt
  obtain ⟨h01, h12, h23, h01', h12', h23'⟩ := hz
  rw [Set.subset_diff]
  exact ⟨Rect
  obtain ⟨h01, h12, h23, h01', h12', h23'⟩ := hz
  rw [Set.subset_diff]
  exact ⟨RectSubRect' h01 h12 h23 h01' h12' h23',
         recta
         rectangle_disjoin
         recta
         rectangle_disjoint_singleton hp⟩
@[target]
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re 
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleB
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by
  obtain ⟨h01, h12, 
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by
  obtain ⟨h01, h12, h23, h01', h12', h23'⟩ := h
  rw [Set.subset_diff]
  exact ⟨(rectangleBorder_subset_rectangle z₁ z₂).trans
     
  exac
  exact ⟨(rectangleBorder_subset_rectangle z₁ z₂).trans
     
  exact ⟨(rectangleBorder_subset_rectangle z₁ z₂).trans
           (RectSubRect' h01 h12 h
           (RectSubRect' h01 h12 h23 h01' h12' h23'),
         r
         rectangleBorder_disjoint_singleton hp⟩
      (z.re < p.re ∧ w.re
         rectang
      (z.re < p.re ∧ w.re
         rectangleBorder_disjoint_singleton hp⟩
      (z.re < p.re ∧ w.re < p.re) ∨ (z.
    Disjoint (Rectangle z w) {p} := by
  rw [Set.disjoint_singleton_right]
  simp onl
  rw 
  rw [Set.disjoint_singleton_right]
  sim
  simp onl
  rw 
  rw [Set.disjoint_singleton_rig
  simp onl
  rw [Set.disjoint_singleton_right]
  simp only [Rectangle, mem_
  simp only [Rectangle, me
  simp only [Rectangle, mem_
  simp only [Rectangle, mem_reProdIm, not_and_or]
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1,
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact Set.not_mem_uIcc_of_lt h1 h2
  · right; exact Set
  · right; exact Set.not_mem_uIcc_of_lt h1 
  · r
  · right; exact Set.not_mem_uIcc_of_lt h1 
  · right; exact Se

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import VerifiedAgora.tagger

open Complex Set

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
def RectangleBorder (z w : ℂ) : Set ℂ := uIcc z.re w.re ×ℂ {z.im} ∪ {z.re} ×ℂ uIcc z.im w.im ∪ uIcc z.re w.re ×ℂ {w.im} ∪ {w.re} ×ℂ uIcc z.im w.im

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
    uIcc z.re w.re ×ℂ uIcc z.im w.im = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by sorry
/-- If the four corners of a rectangle are contained in a convex set `U`, then the whole
  rectangle is. Golfed from mathlib4\#9598.-/
@[target]
lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by sorry
@[target]
lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔ z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by sorry
@[target]
lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simp only [Square]
  rw [show -↑(-c) - ↑(-c) * I + p = ↑c + ↑c * I + p by push_cast; ring,
      show ↑(-c) + ↑(-c) * I + p = -↑c - ↑c * I + p by push_cast; ring]
  exact Rectangle.symm
@[target]
theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b := by
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact left_mem_Ioo.mp
  · rw [uIoo_of_gt h]; exact right_mem_Ioo.mp
@[target]
theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b := by
  rcases le_or_lt a b with h | h
  · rw [uIoo_of_le h]; exact right_mem_Ioo.mp
  · rw [uIoo_of_gt h]; exact left_mem_Ioo.mp
@[target]
theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h => Set.left_not_mem_uIoo (h ▸ hc)
@[target]
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h => Set.right_not_mem_uIoo (h ▸ hc)
@[target]
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩
@[target]
lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := by
  simp [Rectangle, mem_reProdIm, Set.right_mem_uIcc]
@[target]
lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by sorry
@[target]
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁) (x₁_le_x₂ : x₁ ≤ x₂)
    (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁) (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆ Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by sorry
@[target]
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re) (x₁_le_x₂ : z₁.re ≤ z₂.re)
    (x₂_le_x₃ : z₂.re ≤ z₃.re) (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by sorry
@[target]
lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro p hp
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  simp only [Rectangle, mem_reProdIm]
  rcases hp with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
  · exact ⟨h1, h2 ▸ Set.left_mem_uIcc⟩
  · exact ⟨h1 ▸ Set.left_mem_uIcc, h2⟩
  · exact ⟨h1, h2 ▸ Set.right_mem_uIcc⟩
  · exact ⟨h1 ▸ Set.right_mem_uIcc, h2⟩
/-- Note: try using `by simp` for `h`. -/
@[target]
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  rw [Set.disjoint_singleton_right]
  simp only [Rectangle, mem_reProdIm, not_and_or]
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · left; exact Set.not_mem_uIcc_of_lt h1 h2
  · right; exact Set.not_mem_uIcc_of_lt h1 h2
  · left; exact Set.not_mem_uIcc_of_gt h1 h2
  · right; exact Set.not_mem_uIcc_of_gt h1 h2
@[target]
lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  obtain ⟨hre_z, hre_w, him_z, him_w⟩ := h
  rw [Set.disjoint_singleton_right]
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff]
  push_neg
  refine ⟨⟨⟨fun _ => him_z, fun hre => absurd hre hre_z⟩, fun _ => him_w⟩, fun hre => absurd hre hre_w⟩
@[target]
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by sorry
@[target]
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} := by sorry
@[target]
lemma rectangle_mem_nhds_iff {z w p : ℂ} : Rectangle z w ∈ nhds p ↔
    p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by sorry
@[target]
lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w) := by
  intro y hy
  refine mem_reProdIm.mpr ?_
  constructor
  · simp [Rectangle]
  · simp; exact hy
@[target]
lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w) := by
  intro y hy
  refine mem_reProdIm.mpr ?_
  constructor
  · simp [Rectangle]
  · simp; exact hy
@[target]
lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (Rectangle z w) := by
  intro x hx
  refine mem_reProdIm.mpr ?_
  constructor
  · simp; exact hx
  · simp [Rectangle]
@[target]
lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (Rectangle z w) := by
  intro x hx
  refine mem_reProdIm.mpr ?_
  constructor
  · simp; exact hx
  · simp [Rectangle]
@[target]
lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (RectangleBorder z w) := by
  intro y hy
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; left; right; exact ⟨trivial, hy⟩
@[target]
lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (RectangleBorder z w) := by
  intro y hy
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  right; exact ⟨trivial, hy⟩
@[target]
lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (RectangleBorder z w) := by
  intro x hx
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; left; left; exact ⟨hx, trivial⟩
@[target]
lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (RectangleBorder z w) := by
  intro x hx
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
             Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
             Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im,
             mul_one, zero_add, Complex.I_im, add_zero]
  left; right; exact ⟨hx, trivial⟩
@[target]
lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w \ {p}) := by
  intro y hy
  refine ⟨mapsTo_rectangle_left_re z w hy, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_left_re z w hy)
@[target]
lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) (uIcc z.im w.im) (Rectangle z w \ {p}) := by
  intro y hy
  refine ⟨mapsTo_rectangle_right_re z w hy, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_right_re z w hy)
@[target]
lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) (uIcc z.re w.re) (Rectangle z w \ {p}) := by
  intro x hx
  refine ⟨mapsTo_rectangle_left_im z w hx, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_left_im z w hx)
@[target]
lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ} (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) (uIcc z.re w.re) (Rectangle z w \ {p}) := by
  intro x hx
  refine ⟨mapsTo_rectangle_right_im z w hx, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro h
  exact pNotOnBorder (h ▸ mapsTo_rectangleBorder_right_im z w hx)
@[target]
theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ} (hp : Rectangle z w ∈ nhds p) :
    p ∉ RectangleBorder z w := by sorry
@[target]
theorem Complex.nhds_hasBasis_square (p : ℂ) : (nhds p).HasBasis (0 < ·) (Square p ·) := by sorry
@[target]
lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ nhds p := by sorry
@[target]
lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by sorry
@[target]
lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in nhdsWithin 0 (Set.Ioi 0), Square p c ⊆ Rectangle z w := by sorry

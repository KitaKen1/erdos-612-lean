import Erdos612.Definitions
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Local four-layer inequalities for Erdős Problem 612

This file verifies the nonlinear algebra that was previously left outside the
Lean development.  The hypotheses are precisely the numerical output of the
finite-graph greedy covering lemma: after orienting a four-layer window so
that `a ≤ d`, `t` is the smaller closed non-neighbourhood bound, `e = d-a`,
and `k` is the number of greedily selected vertices in the left middle layer.
-/

namespace Erdos612

/-- The nonlinear local inequality used for the `K₅`-free bound. -/
theorem k5_local_four_layer
    (a b c d δ t e : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (had : a ≤ d)
    (hac : 0 < a + c) (hbd : 0 < b + d)
    (ht : t = a + b + c - δ) (he : e = d - a)
    (hk₁ : 1 ≤ k) (hk₄ : k ≤ 4)
    (hbkt : b ≤ (k : ℝ) * t)
    (hcover : 0 ≤ 4 * t + (4 - (k : ℝ)) * e - b - c) :
    k5Potential δ b c d - k5Potential δ a b c ≤ d - 2 * δ / 5 := by
  have he0 : 0 ≤ e := by rw [he]; linarith
  have ht0 : 0 ≤ t := by
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk₁
    nlinarith
  let L : ℝ := 4 * t + (4 - (k : ℝ)) * e - b - c
  let A : ℝ := b * (e + t - c) + c * t
  let B : ℝ := b * (4 * t - b - c) + (b + 2 * t) * e
  have hL : 0 ≤ L := by simpa [L] using hcover
  have hB : 0 ≤ B := by
    have hBid : B = b * L + ((k : ℝ) - 3) * b * e + 2 * t * e := by
      simp only [B, L]
      ring
    rw [hBid]
    interval_cases k <;> norm_num at hbkt ⊢
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ t)) he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ 2 * t)) he0,
        mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg hb he0, mul_nonneg ht0 he0]
  have hA : 0 ≤ A := by
    by_cases hbt : b ≤ t
    · have htc : 0 ≤ c * (t - b) := mul_nonneg hc (sub_nonneg.mpr hbt)
      have hbe : 0 ≤ b * e := mul_nonneg hb he0
      have hbt' : 0 ≤ b * t := mul_nonneg hb ht0
      simp only [A]
      nlinarith
    · have htb : t - b ≤ 0 := by linarith
      have hcBound : c ≤ 4 * t + (4 - (k : ℝ)) * e - b := by
        simpa [L] using hL
      have hmul := mul_le_mul_of_nonpos_left hcBound htb
      interval_cases k <;> norm_num at hbkt hmul ⊢
      · exfalso
        linarith
      · have hp : 0 ≤ (2 * t - b) * (2 * t + e - b) :=
          mul_nonneg (by linarith) (by linarith)
        simp only [A]
        nlinarith
      · have hs : 0 ≤ (b - 2 * t) ^ 2 := sq_nonneg _
        have het : 0 ≤ e * t := mul_nonneg he0 ht0
        simp only [A]
        nlinarith
      · have hs : 0 ≤ (b - 2 * t) ^ 2 := sq_nonneg _
        have heb : 0 ≤ b * e := mul_nonneg hb he0
        simp only [A]
        nlinarith
  have hden : 0 < 10 * (a + c) * (b + d) := by positivity
  have hid :
      10 * (a + c) * (b + d) *
          ((d - 2 * δ / 5) - (k5Potential δ b c d - k5Potential δ a b c)) =
        2 * (a * (2 * A) + c * B) := by
    simp only [k5Potential, A, B]
    rw [ht, he]
    field_simp
    ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hden).mp
  rw [hid]
  positivity

/-- The nonlinear local inequality used for the `K₄`-free bound. -/
theorem k4_local_four_layer
    (a b c d δ t e : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (had : a ≤ d)
    (hac : 0 < a + c) (hbd : 0 < b + d)
    (ht : t = a + b + c - δ) (he : e = d - a)
    (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (hbkt : b ≤ (k : ℝ) * t)
    (hcover : 0 ≤ 3 * t + (3 - (k : ℝ)) * e - b - c) :
    k4Potential δ b c d - k4Potential δ a b c ≤ d - 3 * δ / 7 := by
  have he0 : 0 ≤ e := by rw [he]; linarith
  have ht0 : 0 ≤ t := by
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk₁
    nlinarith
  let L : ℝ := 3 * t + (3 - (k : ℝ)) * e - b - c
  let A : ℝ := (3 * t - 4 * b) * c + 3 * b * (t + e)
  let B : ℝ := b * (6 * t - 2 * b - 2 * c) + (b + 3 * t) * e
  have hL : 0 ≤ L := by simpa [L] using hcover
  have hB : 0 ≤ B := by
    have hBid : B = 2 * b * L + (3 * t + (2 * (k : ℝ) - 5) * b) * e := by
      simp only [B, L]
      ring
    rw [hBid]
    interval_cases k <;> norm_num at hbkt ⊢
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ t)) he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ 2 * t)) he0,
        mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg hb he0, mul_nonneg ht0 he0]
  have hA : 0 ≤ A := by
    by_cases hcase : 4 * b ≤ 3 * t
    · have hfirst : 0 ≤ (3 * t - 4 * b) * c :=
        mul_nonneg (sub_nonneg.mpr hcase) hc
      have hsecond : 0 ≤ 3 * b * (t + e) := by positivity
      simp only [A]
      nlinarith
    · have hcoef : 0 ≤ 4 * b - 3 * t := by linarith
      have hsq : 0 ≤ (2 * b - 3 * t) ^ 2 := sq_nonneg _
      have hAL : 0 ≤ (4 * b - 3 * t) * L := mul_nonneg hcoef hL
      have hAid :
          A = (2 * b - 3 * t) ^ 2 +
              ((9 - 3 * (k : ℝ)) * t + (4 * (k : ℝ) - 9) * b) * e +
              (4 * b - 3 * t) * L := by
        simp only [A, L]
        ring
      rw [hAid]
      interval_cases k <;> norm_num at hbkt ⊢
      · have hmid : 0 ≤ (6 * t - 5 * b) * e :=
          mul_nonneg (by linarith) he0
        nlinarith
      · have hmid : 0 ≤ (3 * t - b) * e :=
          mul_nonneg (by linarith) he0
        nlinarith
      · have hmid : 0 ≤ 3 * b * e := by positivity
        nlinarith
  have hden : 0 < 14 * (a + c) * (b + d) := by positivity
  have hid :
      14 * (a + c) * (b + d) *
          ((d - 3 * δ / 7) - (k4Potential δ b c d - k4Potential δ a b c)) =
        2 * (a * A + c * B) := by
    simp only [k4Potential, A, B]
    rw [ht, he]
    field_simp
    ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hden).mp
  rw [hid]
  positivity

end Erdos612

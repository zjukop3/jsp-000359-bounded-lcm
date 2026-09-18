import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Bounded LCM for consecutive sequence elements (JSP-000359)

**Original problem.** Let `1 ≤ a₁ < a₂ < … < a_k ≤ n` be positive integers
with `lcm(a_{i-1}, a_i) ≤ n` for every `2 ≤ i ≤ k`. Prove `k = O(√n)`.

**Proof.** Set `r = ⌈√n⌉`. In layer `m ≥ 2` (width `r`), consecutive gaps
exceed `(m−1)²`, so the layer has at most `⌊r/(m−1)²⌋+1` elements. Summing
over layers and using `∑ 1/j² < 2` gives `k ≤ 4r ≤ 4√n + 4`.

Mathematical credit: Erdős–Graham (conjecture, 1980); van Doorn (proof).
-/

open Nat BigOperators Real

namespace BoundedLcm

noncomputable section

lemma gcd_dvd_sub {a b : ℕ} (hab : a ≤ b) : Nat.gcd a b ∣ b - a := by
  obtain ⟨p, hp⟩ := Nat.gcd_dvd_left a b
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a b
  refine ⟨q - p, ?_⟩
  have hkey : Nat.gcd a b * (q - p) = Nat.gcd a b * q - Nat.gcd a b * p :=
    mul_tsub _ _ _
  rw [hkey, ← hq, ← hp]

lemma gcd_le_diff {a b : ℕ} (hab : a < b) : Nat.gcd a b ≤ b - a :=
  Nat.le_of_dvd (by omega) (gcd_dvd_sub hab.le)

lemma lcm_mul_diff_ge_mul {a b : ℕ} (_ha : 0 < a) (hab : a < b) :
    Nat.lcm a b * (b - a) ≥ a * b := by
  have hle : Nat.gcd a b ≤ b - a := gcd_le_diff hab
  have heq : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  calc Nat.lcm a b * (b - a)
      ≥ Nat.lcm a b * Nat.gcd a b := Nat.mul_le_mul_left _ hle
    _ = a * b := by rw [mul_comm, heq]

lemma sq_le_mul_diff_of_lcm {a b n : ℕ} (ha : 0 < a) (hab : a < b)
    (hlcm : Nat.lcm a b ≤ n) :
    (a : ℝ) ^ 2 ≤ (n : ℝ) * ((b - a : ℕ) : ℝ) := by
  have hgcd_le : Nat.gcd a b ≤ b - a := gcd_le_diff hab
  have heq : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h1 : Nat.gcd a b * Nat.lcm a b ≤ (b - a) * Nat.lcm a b :=
    Nat.mul_le_mul_right (Nat.lcm a b) hgcd_le
  have h2 : (b - a) * Nat.lcm a b ≤ (b - a) * n := Nat.mul_le_mul_left _ hlcm
  have h_le : a * b ≤ (b - a) * n := by
    rw [← heq]; exact le_trans h1 h2
  have h3 : (a : ℝ) ^ 2 ≤ (a * b : ℝ) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hab.le)
      (by exact_mod_cast ha.le)
  have h4 : (a * b : ℝ) ≤ ((b - a : ℕ) * n : ℝ) := by exact_mod_cast h_le
  have h5 : ((b - a : ℕ) * n : ℝ) = (n : ℝ) * ((b - a : ℕ) : ℝ) := by
    push_cast; ring
  linarith [h3, h4, h5]

lemma gap_count {g B : ℕ} (hg : 0 < g) (l : List ℕ)
    (hl_pos : ∀ x ∈ l, 0 < x) (hl_le : ∀ x ∈ l, x ≤ B)
    (hl_sorted : l.SortedLT)
    (hl_gap : ∀ (i : ℕ) (hi : i + 1 < l.length),
      g ≤ l.get ⟨i + 1, hi⟩ - l.get ⟨i, Nat.lt_of_succ_lt hi⟩) :
    (l.length : ℝ) ≤ (B : ℝ) / g + 1 := by
  by_cases hl : l.length = 0
  · simp [hl]; positivity
  have hl' : 0 < l.length := by omega
  have h_lower : ∀ (i : ℕ) (hi : i < l.length),
      (1 + i * g : ℕ) ≤ l.get ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero => exact le_trans (by omega) (hl_pos _ (List.get_mem _ _))
    | succ i ih =>
      have hprev := ih (by omega)
      have hgap := hl_gap _ hi
      have hidx : i + 1 < l.length := hi
      have hi' : i < l.length := Nat.lt_of_succ_lt hidx
      have hle_idx : l.get ⟨i, hi'⟩ ≤ l.get ⟨i + 1, hidx⟩ := by
        apply hl_sorted.strictMono_get.monotone
        simp only [Fin.le_iff_val_le_val]
        omega
      have heq : l.get ⟨i + 1, hidx⟩ =
          l.get ⟨i, hi'⟩ + (l.get ⟨i + 1, hidx⟩ - l.get ⟨i, hi'⟩) :=
        (Nat.add_sub_of_le hle_idx).symm
      rw [heq, add_mul, one_mul]
      omega
  have h_last_idx : l.length - 1 < l.length := by omega
  have h_last : l.get ⟨l.length - 1, h_last_idx⟩ ≤ B :=
    hl_le _ (List.get_mem _ _)
  have h_lower_last : (1 + (l.length - 1) * g : ℕ) ≤
      l.get ⟨l.length - 1, h_last_idx⟩ := h_lower _ h_last_idx
  have h_bound : (1 + (l.length - 1) * g : ℕ) ≤ B :=
    le_trans h_lower_last h_last
  have h_mul : (l.length - 1) * g ≤ B - 1 := by omega
  have hg_pos : (0 : ℝ) < g := by exact_mod_cast hg
  by_cases hB : B = 0
  · exfalso
    match l with
    | [] => exact hl rfl
    | hd :: _ =>
      have hle := hl_le hd (List.get_mem _ 0)
      have hpos := hl_pos hd (List.get_mem _ 0)
      omega
  have h_sub : ((l.length - 1 : ℕ) : ℝ) * g ≤ ((B - 1 : ℕ) : ℝ) := by
    push_cast; exact_mod_cast h_mul
  have h_div : ((l.length - 1 : ℕ) : ℝ) ≤ ((B - 1 : ℕ) : ℝ) / g := by
    rw [le_div_iff₀ hg_pos]; exact h_sub
  have h_Bm1_div : ((B - 1 : ℕ) : ℝ) / g ≤ (B : ℝ) / g := by
    gcongr; exact_mod_cast (by omega : B - 1 ≤ B)
  have h_result : ((l.length - 1 : ℕ) : ℝ) + 1 ≤ (B : ℝ) / g + 1 := by
    linarith [add_le_add_right (le_trans h_div h_Bm1_div) 1]
  rw [show (l.length : ℝ) = ((l.length - 1 : ℕ) : ℝ) + 1 by
    push_cast; rw [Nat.cast_sub (by omega : 1 ≤ l.length)]; ring]
  exact h_result

lemma sum_inv_sq_telescope {N : ℕ} (hN : 2 ≤ N) :
    Finset.sum ((Finset.range N).filter (fun j => 1 ≤ j))
      (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2)
    ≤ 1 - 1 / (N : ℝ) := by
  have h := @sum_Ioc_inv_sq_le_sub ℝ _ _ _ 1 N (by omega) (by omega : 1 ≤ N)
  have heq : Finset.sum ((Finset.range N).filter (fun j => 1 ≤ j))
      (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) =
    Finset.sum (Finset.Ioc 1 N) (fun i => ((i : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_bij (fun j _ => j + 1)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_Ioc]
      exact ⟨by omega, by omega⟩
    · intro j1 _ j2 _ hjj
      omega
    · intro i hi
      simp only [Finset.mem_Ioc] at hi
      exact ⟨i - 1, by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega⟩, by omega⟩
    · intro j _
      simp [one_div, inv_pow]
  rw [heq]
  simpa using h

lemma sum_inv_sq_lt_two {r : ℕ} (hr : 1 ≤ r) :
    Finset.sum ((Finset.range r).filter (fun j => 1 ≤ j))
      (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2)
    < 2 := by
  by_cases hr2 : r ≤ 1
  · have hempty : (Finset.range r).filter (fun j => 1 ≤ j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        omega
      · intro h
        simp at h
    simp [hempty]
  · have hr' : 2 ≤ r := by omega
    have h := sum_inv_sq_telescope hr'
    have : (1 : ℝ) - 1 / (r : ℝ) < 1 := by
      have : 0 < (1 : ℝ) / (r : ℝ) := by positivity
      linarith
    linarith

theorem jsp_000359 (n : ℕ) (hn : 1 ≤ n)
    (a : List ℕ)
    (ha_sorted : a.SortedLT)
    (ha_pos : ∀ x ∈ a, 0 < x)
    (ha_le : ∀ x ∈ a, x ≤ n)
    (ha_lcm : ∀ (i : ℕ) (hi : i + 1 < a.length),
      Nat.lcm (a.get ⟨i, Nat.lt_of_succ_lt hi⟩) (a.get ⟨i + 1, hi⟩) ≤ n) :
    (a.length : ℝ) ≤ 4 * Real.sqrt n + 4 := by
  sorry

end
end BoundedLcm

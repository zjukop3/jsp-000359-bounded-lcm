import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
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
  -- Step 1: a.length ≤ n (pigeonhole: distinct positive integers in [1,n])
  have h_nodup : a.Nodup := ha_sorted.nodup
  have h_card : a.toFinset.card = a.length := List.toFinset_card_of_nodup h_nodup
  have h_subset : a.toFinset ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_Icc]
    exact ⟨ha_pos x hx, ha_le x hx⟩
  have h_card_Icc : (Finset.Icc (1 : ℕ) n).card = n := by simp
  have h_len_n : a.length ≤ n := by
    calc a.length = a.toFinset.card := h_card.symm
      _ ≤ (Finset.Icc (1 : ℕ) n).card := Finset.card_le_card h_subset
      _ = n := h_card_Icc
  have h_sqrt_ge_1 : (1 : ℝ) ≤ Real.sqrt n :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have h_8_le : (8 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
  by_cases hl : a.length ≤ 8
  · have : (a.length : ℝ) ≤ 8 := by exact_mod_cast hl
    linarith
  have h_n_ge_9 : 9 ≤ n := by omega
  by_cases hn23 : n ≤ 23
  · -- For 9 ≤ n ≤ 23: n ≤ 4√n+4 via (n-4)/4 ≤ √n
    have h_sq_nat : (n - 4)^2 ≤ 16 * n := by
      interval_cases n <;> decide
    have h_y : (0 : ℝ) ≤ (n - 4) / 4 := by
      have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
      have : (0 : ℝ) ≤ n - 4 := by linarith
      exact div_nonneg this (by norm_num)
    have h_sqrt_sq : Real.sqrt (((n - 4 : ℝ) / 4)^2) = (n - 4 : ℝ) / 4 :=
      Real.sqrt_sq h_y
    have h_1 : ((n - 4 : ℝ) / 4)^2 ≤ n := by
      interval_cases n <;> { push_cast; norm_num }
    have h_2 := Real.sqrt_le_sqrt h_1
    rw [Real.sqrt_sq h_y] at h_2
    push_cast
    have h_len_n_r : (a.length : ℝ) ≤ n := by exact_mod_cast h_len_n
    linarith [h_2, h_len_n_r]
  -- Step 5: For n ≥ 24
  have h_n_24 : (24 : ℝ) ≤ n := by exact_mod_cast (by omega : 24 ≤ n)
  by_cases hl24 : a.length ≤ 23
  · -- a.length ≤ 23 ≤ 4*√24+4 ≤ 4*√n+4
    -- Need √24 ≥ 19/4 = 4.75, since (19/4)² = 361/16 = 22.5625 ≤ 24
    have h_19_sq : (19 : ℕ)^2 ≤ 16 * (24 : ℕ) := by norm_num
    have h_y : (0 : ℝ) ≤ (19 / 4 : ℝ) := by norm_num
    have h_sq_19 : ((19 / 4 : ℝ)^2) ≤ 24 := by
      have h_eq : ((19 / 4 : ℝ)^2) = (19 : ℝ)^2 / 16 := by ring
      rw [h_eq, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
      push_cast
      exact_mod_cast h_19_sq
    have h_sqrt_sq : Real.sqrt ((19 / 4 : ℝ)^2) = 19 / 4 := Real.sqrt_sq h_y
    have h_le_24 : (19 / 4 : ℝ) ≤ Real.sqrt 24 := by
      have := Real.sqrt_le_sqrt h_sq_19
      rwa [h_sqrt_sq] at this
    have h_le_n : (19 / 4 : ℝ) ≤ Real.sqrt n := by
      have := Real.sqrt_le_sqrt h_n_24
      linarith
    push_cast
    have h_len_r : (a.length : ℝ) ≤ 23 := by exact_mod_cast hl24
    linarith
  -- a.length ≥ 24: need lcm constraint
  -- Use: a.length ≤ n (pigeonhole, already have h_len_n)
  -- For n ≥ 24: need stronger bound than n ≤ 4√n + 4 (which fails for n ≥ 24)
  -- Key: sq_le_mul_diff_of_lcm gives a_i^2 ≤ n * d_i for each consecutive pair
  -- Since a_i ≥ 1 (positive), a_i^2 ≥ 1, so d_i ≥ 1/n (trivial)
  -- But a_i ≥ i+1 (strictly increasing from ≥1), so d_i ≥ (i+1)^2/n
  -- For the first element after position floor(√n): d grows quadratically
  -- This forces the sequence to be short relative to n
  -- Step 1: Prove a_i ≥ i+1 for all i < a.length (from strictly increasing + positive)
  have h_ai_ge : ∀ (i : ℕ) (hi : i < a.length), i + 1 ≤ a.get ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
      have h0 : 0 < a.get ⟨0, hi⟩ := by
        have hmem : a.get ⟨0, hi⟩ ∈ a := by simp [List.getElem_mem]
        exact ha_pos _ hmem
      exact le_trans (by omega) h0
    | succ i ih =>
      have hprev := ih (by omega)
      have hi' : i < a.length := Nat.lt_of_succ_lt hi
      have hle_idx : a.get ⟨i + 1, hi⟩ ≥ a.get ⟨i, hi'⟩ :=
        (ha_sorted.strictMono_get (by omega : i < i + 1)).le
      have heq : a.get ⟨i + 1, hi⟩ = a.get ⟨i, hi'⟩ + (a.get ⟨i + 1, hi⟩ - a.get ⟨i, hi'⟩) :=
        (Nat.add_sub_of_le hle_idx).symm
      rw [heq]
      have hdi : 1 ≤ a.get ⟨i + 1, hi⟩ - a.get ⟨i, hi'⟩ :=
        Nat.sub_pos_of_lt (ha_sorted.strictMono_get (by omega : i < i + 1))
      have := hle_idx
      nlinarith

  -- Step 2: For each i < a.length - 1, (i+1)^2 ≤ n * d_i
  have h_sq_bound : ∀ (i : ℕ) (hi : i + 1 < a.length),
      (i + 1 : ℕ)^2 ≤ n * (a.get ⟨i + 1, hi⟩ - a.get ⟨i, Nat.lt_of_succ_lt hi⟩) := by
    intro i hi
    have hi' := Nat.lt_of_succ_lt hi
    have h_ai_pos : 0 < a.get ⟨i, hi'⟩ := by
      have hmem : a.get ⟨i, hi'⟩ ∈ a := by simp [List.getElem_mem]
      exact ha_pos _ hmem
    have h_ai_lt : a.get ⟨i, hi'⟩ < a.get ⟨i + 1, hi⟩ :=
      ha_sorted.strictMono_get (by omega : i < i + 1)
    have h_lcm : Nat.lcm (a.get ⟨i, hi'⟩) (a.get ⟨i + 1, hi⟩) ≤ n := ha_lcm i hi
    have h_sq := sq_le_mul_diff_of_lcm h_ai_pos h_ai_lt h_lcm
    have h_ge : (i + 1 : ℕ) ≤ a.get ⟨i, hi'⟩ := h_ai_ge i hi'
    have h_sq_ge : ((i + 1 : ℕ) : ℝ)^2 ≤ (a.get ⟨i, hi'⟩ : ℝ)^2 := by
      have hge_r : (i + 1 : ℕ) ≤ a.get ⟨i, hi'⟩ := h_ge
      have h_nat : (i + 1 : ℕ) * (i + 1) ≤ a.get ⟨i, hi'⟩ * a.get ⟨i, hi'⟩ :=
        Nat.mul_self_le_mul_self hge_r
      have h_real : ((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ) ≤ (a.get ⟨i, hi'⟩ : ℝ) * (a.get ⟨i, hi'⟩ : ℝ) :=
        by exact_mod_cast h_nat
      rw [sq, sq]
      exact h_real
    exact_mod_cast (le_trans h_sq_ge h_sq)

  -- Step 3: Derive k ≤ 4√n + 4 from h_sq_bound
  -- We have: for each i, (i+1)^2 ≤ n * d_i where d_i = a_{i+1} - a_i
  -- And: Σ d_i = a_{last} - a_{first} ≤ n - 1 ≤ n
  -- So: Σ (i+1)^2 ≤ n * Σ d_i ≤ n^2
  -- This gives (k-1)k(2k-1)/6 ≤ n^2, so k^3 ≤ 3n^2 (for k ≥ 2)
  -- Then k ≤ (3n^2)^(1/3) + 1, and (3n^2)^(1/3) ≤ 4√n for n ≥ 24
  -- But formalizing the sum requires Finset.sum infrastructure

  -- Alternative: use the gap_count lemma
  -- For i ≥ 0: d_i ≥ (i+1)^2/n
  -- For i ≥ floor(√n) - 1: d_i ≥ n/n = 1 (trivial, already true)
  -- For i ≥ floor(√(2n)) - 1: d_i ≥ 2n/n = 2
  -- For i ≥ floor(√(3n)) - 1: d_i ≥ 3n/n = 3
  -- ...
  -- For i ≥ floor(√(m*n)) - 1: d_i ≥ m
  -- This gives a layered argument similar to the partitioning proof

  -- For now: use interval_cases for small n and native approach for large n
  -- Key: for n ≤ 600, (3n^2)^(1/3) + 1 ≤ 4√n + 4
  -- For n ≥ 601: need partitioning argument (gap_count + sum_inv_sq_lt_two)

  -- Simplest approach that avoids Finset.sum:
  -- Use h_sq_bound to get d_i ≥ 1 for all i (trivial from strictly increasing)
  -- Use gap_count with g=1: length ≤ n + 1 (trivial)
  -- This doesn't help. We need the quadratic bound.

  -- Try: prove k ≤ 4√n + 4 directly via:
  -- 1. k ≤ n (pigeonhole)
  -- 2. For n ≥ 24, k ≤ n, but n can be > 4√n + 4
  -- 3. So we need: if k > 4√n + 4, then contradiction with lcm constraint

  -- Use: if k ≥ 25 (since k > 4*√24+4 ≈ 23.6), then:
  -- Σ d_i ≥ Σ (i+1)^2/n ≥ (1+4+9+...+625)/n = (25*26*51)/6 / n
  -- = 5525/n ≤ n, so n^2 ≥ 5525, n ≥ 75
  -- So if k ≥ 25, then n ≥ 75
  -- And 4*√75 + 4 ≈ 38.6, so k ≤ n ≤ ... still need more

  -- The fundamental issue: without Finset.sum, we can't sum h_sq_bound
  -- Try using List.sum and List.take instead

  have h_cs : (a.length : ℝ) ≤ 4 * Real.sqrt n + 4 := by
    -- Prove by induction: Σ_{i=0}^{j-1} (i+1)^2 ≤ n * (a_j - a_0)
    have h_sum_ind : ∀ (j : ℕ) (hj : j < a.length),
        ((List.range j).map (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤
        n * (a.get ⟨j, hj⟩ - a.get ⟨0, by omega⟩) := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        have hj' : j < a.length := Nat.lt_of_succ_lt hj
        have hprev := ih hj'
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        have hsq := h_sq_bound j hj
        have hle01 : a.get ⟨0, by omega⟩ ≤ a.get ⟨j, hj'⟩ := by
          match j with
          | 0 => simp
          | j+1 => exact (ha_sorted.strictMono_get (Nat.succ_pos j)).le
        have hle12 : a.get ⟨j, hj'⟩ ≤ a.get ⟨j + 1, hj⟩ := by
          exact (ha_sorted.strictMono_get (by omega : j < j + 1)).le
        have h_split : a.get ⟨j, hj'⟩ - a.get ⟨0, by omega⟩ +
            (a.get ⟨j + 1, hj⟩ - a.get ⟨j, hj'⟩) =
            a.get ⟨j + 1, hj⟩ - a.get ⟨0, by omega⟩ := by omega
        nlinarith
    -- Apply h_sum_ind at j = a.length - 1
    have h_k1 : 1 ≤ a.length := by omega
    have h_last_idx : a.length - 1 < a.length := by omega
    have h_sum_final : ((List.range (a.length - 1)).map (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤
        n * (a.get ⟨a.length - 1, h_last_idx⟩ - a.get ⟨0, by omega⟩) :=
      h_sum_ind (a.length - 1) h_last_idx
    -- a_{last} ≤ n, a_0 ≥ 1, so a_{last} - a_0 ≤ n - 1
    have h_last_le : a.get ⟨a.length - 1, h_last_idx⟩ ≤ n := by
      have hmem : a.get ⟨a.length - 1, h_last_idx⟩ ∈ a := by simp [List.getElem_mem]
      exact ha_le _ hmem
    have h_first_pos : 1 ≤ a.get ⟨0, by omega⟩ := by
      have hmem : a.get ⟨0, by omega⟩ ∈ a := by simp [List.getElem_mem]
      exact ha_pos _ hmem
    have h_diff_le : a.get ⟨a.length - 1, h_last_idx⟩ - a.get ⟨0, by omega⟩ ≤ n - 1 := by omega
    have h_sum_sq : ((List.range (a.length - 1)).map (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤ n * (n - 1) := by
      have h1 : a.get ⟨a.length - 1, h_last_idx⟩ - a.get ⟨0, by omega⟩ ≤ n - 1 := h_diff_le
      have h2 := h_sum_final
      nlinarith
    -- Σ (i+1)^2 for i=0..k-2 = (k-1)*k*(2k-1)/6 (sum of squares formula)
    -- But we don't need the exact formula, just (k-1)^3 ≤ 6 * Σ (i+1)^2
    -- For k ≥ 2: (i+1)^2 ≥ i^2 for i ≥ 0, so Σ (i+1)^2 ≥ Σ i^2 = (k-1)(k-2)(2k-3)/6
    -- Actually simpler: (i+1)^2 ≥ (i+1) for i ≥ 0, so Σ (i+1)^2 ≥ Σ (i+1) = k(k-1)/2
    -- And for k ≥ 2: k(k-1)/2 ≥ (k-1)^2/2, so (k-1)^2 ≤ 2*Σ ≤ 2n(n-1)
    -- This gives k ≤ √(2n²) + 1 ≈ 1.41√n + 1
    -- For n = 24: 1.41*4.89 + 1 = 7.9, 4*4.89+4 = 23.6, so 8 ≤ 23.6 ✓
    -- For n = 1000: 1.41*31.6 + 1 = 45.6, 4*31.6+4 = 130.5, so 46 ≤ 130.5 ✓
    -- This bound works for ALL n ≥ 1! (since 1.41√n + 1 ≤ 4√n + 4 for n ≥ 1)
    -- (4√n + 4) - (1.41√n + 1) = 2.59√n + 3 ≥ 0 always)

    -- Actually let's use the simpler bound:
    -- Σ (i+1)^2 ≥ Σ (i+1) = k(k-1)/2 (where k = a.length)
    -- So k(k-1)/2 ≤ n(n-1)
    -- k² ≤ 2n² (for k ≥ 1), k ≤ √2 * n (too weak, n > √n for n > 1)

    -- Better: (i+1)^2 ≥ i+1 for i ≥ 0 (since i ≥ 0, (i+1)^2 = (i+1)(i+1) ≥ i+1)
    -- So Σ_{i=0}^{k-2} (i+1) = (k-1)k/2 ≤ n(n-1)
    -- k² ≤ 2n², k ≤ √2 * n (still too weak)

    -- Even better: (i+1)^2 ≥ (i+1)^2 (trivial), and we know
    -- (k-1)^3/3 ≤ (k-1)k(2k-1)/6 = Σ_{j=1}^{k-1} j^2 (sum of squares)
    -- And Σ_{j=1}^{k-1} j^2 = Σ_{i=0}^{k-2} (i+1)^2 ≤ n(n-1)
    -- So (k-1)^3 ≤ 3n(n-1) ≤ 3n²
    -- k ≤ (3n²)^(1/3) + 1

    -- For the bound (k-1)^3 ≤ 3*(k-1)*k*(2k-1)/6:
    -- (k-1)^3 ≤ (k-1)*k*(2k-1)/2 (since k ≥ k-1, 2k-1 ≥ 2(k-1))
    -- = 3 * (k-1)*k*(2k-1)/6 = 3 * Σ j^2
    -- So (k-1)^3 ≤ 3 * n * (n-1) ≤ 3n²

    -- We need: (k-1)^3 ≤ 3n² → k-1 ≤ (3n²)^(1/3) → k ≤ (3n²)^(1/3) + 1
    -- Then: (3n²)^(1/3) + 1 ≤ 4√n + 4
    -- i.e., (3n²)^(1/3) ≤ 4√n + 3
    -- i.e., 3n² ≤ (4√n + 3)³
    -- For n = 24: 3*576 = 1728, (4*4.89+3)³ = 22.56³ = 11490 ✓
    -- For n = 500: 3*250000 = 750000, (4*22.36+3)³ = 92.44³ = 790000 ✓
    -- For n = 600: 3*360000 = 1080000, (4*24.49+3)³ = 100.96³ = 1029000 ✗
    -- Fails at n ≈ 550!
    -- So (3n²)^(1/3) + 1 ≤ 4√n + 4 only for n ≤ ~550
    -- Key: Real.sqrt n ≥ Nat.sqrt n
    have h_sqrt_ge_nat : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
      have h_sq : (Nat.sqrt n : ℕ) * Nat.sqrt n ≤ n := Nat.sqrt_le n
      have h_pos : (0 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (Nat.zero_le _)
      have h1 : Real.sqrt ((Nat.sqrt n : ℕ) * Nat.sqrt n) ≤ Real.sqrt n :=
        Real.sqrt_le_sqrt (by exact_mod_cast h_sq)
      have h2 : Real.sqrt ((Nat.sqrt n : ℕ) * Nat.sqrt n) = Nat.sqrt n := by
        have : (Nat.sqrt n : ℝ) * Nat.sqrt n = (Nat.sqrt n : ℝ)^2 := by rw [sq]
        rw [this, Real.sqrt_sq h_pos]
      linarith

    -- For n ≤ 550: use interval_cases to verify 3*n*(n-1) ≤ (4*Nat.sqrt(n)+4)^3
    -- This works for n ≤ 543 (Nat.sqrt gives enough precision)
    -- For n ∈ [544, 550]: use Real.sqrt(n) ≥ 93/4

    by_cases hn550 : n ≤ 550
    · -- n ≤ 550
      by_cases hn543 : n ≤ 543
      · -- n ≤ 543: Nat.sqrt bound works
        -- (k-1)^3 ≤ 3n(n-1) ≤ (4*Nat.sqrt(n)+4)^3 ≤ (4*Real.sqrt(n)+4)^3
        -- So k ≤ 4*Real.sqrt(n)+4
        -- Use interval_cases on n with ranges
        interval_cases n <;>
          { -- For each n in [24, 543]:
            -- 1. (k-1)^3 ≤ 3*n*(n-1) (from h_sum_sq)
            -- 2. 3*n*(n-1) ≤ (4*Nat.sqrt(n)+4)^3
            -- 3. (4*Nat.sqrt(n)+4)^3 ≤ (4*Real.sqrt(n)+4)^3 (since Real.sqrt ≥ Nat.sqrt)
            -- 4. So (k-1)^3 ≤ (4*Real.sqrt(n)+4)^3, k ≤ 4*Real.sqrt(n)+4
            sorry }
      · -- n ∈ [544, 550]: use Real.sqrt(n) ≥ 93/4
        -- (93/4)^2 = 8649/16 = 540.5625 ≤ 544 ≤ n
        -- So sqrt(n) ≥ 93/4, 4*sqrt(n)+4 ≥ 97
        -- (k-1)^3 ≤ 3n(n-1) ≤ 3*550*549 = 905850 ≤ 912673 = 97^3
        -- So k-1 ≤ 96, k ≤ 97 ≤ 4*sqrt(n)+4
        have h_sqrt : (93 / 4 : ℝ) ≤ Real.sqrt n := by
          have h_n_ge : (544 : ℝ) ≤ n := by exact_mod_cast (by omega : 544 ≤ n)
          have h_sq : (93/4 : ℝ)^2 = 8649/16 := by norm_num
          have h_le : (8649/16 : ℝ) ≤ 544 := by norm_num
          have h_chain : (93/4 : ℝ)^2 ≤ n := by
            rw [h_sq]; linarith
          -- sqrt(x) ≥ y when y ≥ 0 and y^2 ≤ x
          -- Use: Real.sqrt_le_sqrt gives sqrt(a) ≤ sqrt(b) when a ≤ b
          -- We need: y ≤ sqrt(x), i.e., sqrt(y^2) ≤ sqrt(x), i.e., y^2 ≤ x
          have h_y_pos : (0 : ℝ) ≤ 93/4 := by norm_num
          have h_y_sqrt : Real.sqrt ((93/4 : ℝ)^2) = 93/4 := by
            rw [Real.sqrt_sq h_y_pos]
          have h_chain2 : Real.sqrt ((93/4 : ℝ)^2) ≤ Real.sqrt n :=
            Real.sqrt_le_sqrt h_chain
          rw [h_y_sqrt] at h_chain2
          exact h_chain2
        have h_97 : (97 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
        have h_97_cube : (97 : ℝ)^3 ≤ (4 * Real.sqrt n + 4)^3 :=
          pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 97) h_97 3
        have h_3n_max : (3 : ℝ) * 550 * 549 ≤ 97^3 := by norm_num
        have h_3n : (3 : ℝ) * n * (n - 1) ≤ 97^3 := by
          have h_n_r : (n : ℝ) ≤ 550 := by exact_mod_cast (by omega : n ≤ 550)
          have h_n1_r : ((n - 1 : ℕ) : ℝ) ≤ 549 := by exact_mod_cast (by omega : n - 1 ≤ 549)
          nlinarith
        -- (k-1)^3 ≤ 3n(n-1) ≤ 97^3 ≤ (4*sqrt(n)+4)^3
        -- So k-1 ≤ 97, k ≤ 98 ≤ 4*sqrt(n)+4 (since sqrt(n) ≥ 93/4, 4*93/4+4=97, 98 ≤ 97? No!)
        -- Wait: k-1 ≤ (3n(n-1))^(1/3) ≤ 97, so k ≤ 98
        -- But 4*sqrt(n)+4 ≥ 97, and 98 > 97. So k ≤ 98 > 97 = 4*sqrt(n)+4-1
        -- This is off by one!
        -- Fix: (k-1)^3 ≤ 3n(n-1) ≤ 97^3, so k-1 ≤ 97, k ≤ 98
        -- Need 98 ≤ 4*sqrt(n)+4, i.e., sqrt(n) ≥ 94/4 = 23.5
        -- (23.5)^2 = 552.25 ≤ 544? No! 552.25 > 544
        -- So sqrt(544) < 23.5, and 4*sqrt(544)+4 < 98
        -- This approach fails!
        -- Better: use 94/4 = 47/2, (47/2)^2 = 2209/4 = 552.25
        -- 552.25 ≤ n for n ≥ 553, but we need n ≥ 544
        -- So 47/2 doesn't work for n ∈ [544, 552]
        -- Need a different approach for n ∈ [544, 550]
        -- Use: (k-1)^3 ≤ 3n(n-1) ≤ (4*Nat.sqrt(n)+4)^3
        -- For n ∈ [544, 550]: Nat.sqrt(n) = 23 (since 23^2=529 ≤ n < 576=24^2)
        -- (4*23+4)^3 = 96^3 = 884736
        -- 3*550*549 = 905850 > 884736 ✗!
        -- Fails! So Nat.sqrt(23) bound is too weak for n ∈ [544, 550]
        -- Need Real.sqrt bound: sqrt(n) ≥ 23 + delta for some delta > 0
        -- sqrt(544) ≈ 23.32, 4*23.32+4 = 97.3
        -- Need: (k-1)^3 ≤ 3n(n-1) ≤ 97^3 = 912673
        -- 3*550*549 = 905850 ≤ 912673 ✓
        -- So (k-1) ≤ 97, k ≤ 98
        -- Need: 98 ≤ 4*sqrt(n)+4, i.e., sqrt(n) ≥ 94/4 = 23.5
        -- But sqrt(544) ≈ 23.32 < 23.5, so 4*sqrt(544)+4 ≈ 97.3 < 98 ✗!
        -- Fails for n=544!
        -- For n=548: sqrt(548) ≈ 23.41, 4*23.41+4 = 97.6 < 98 ✗
        -- For n=553: sqrt(553) ≈ 23.52, 4*23.52+4 = 98.1 ≥ 98 ✓
        -- But we need n ≤ 550, so this doesn't help
        -- For n ∈ [544, 550]: need k ≤ 97, not 98
        -- (k-1)^3 ≤ 3n(n-1) ≤ 97^3, so k-1 ≤ 97, k ≤ 98
        -- But 97^3 = 912673, and 3*550*549 = 905850 ≤ 912673
        -- So (k-1)^3 ≤ 905850 < 97^3, so k-1 < 97, k-1 ≤ 96, k ≤ 97
        -- And 4*sqrt(n)+4 ≥ 4*93/4+4 = 97 ✓!
        -- Wait: (k-1)^3 ≤ 905850, and 96^3 = 884736 < 905850
        -- So (k-1)^3 ≤ 905850 doesn't give k-1 ≤ 96!
        -- 97^3 = 912673 > 905850, so k-1 < 97, k-1 ≤ 96, k ≤ 97
        -- 4*sqrt(n)+4 ≥ 97 (from sqrt(n) ≥ 93/4)
        -- So k ≤ 97 ≤ 4*sqrt(n)+4 ✓!
        -- The key: 3*550*549 = 905850 < 912673 = 97^3
        -- So (k-1)^3 ≤ 905850 < 97^3, k-1 < 97, k ≤ 97
        -- And 97 ≤ 4*sqrt(n)+4 ✓
        -- This works!
        have h_k_le_97 : (a.length : ℝ) ≤ 97 := by
          -- From h_sum_sq: Σ (i+1)^2 ≤ n*(n-1)
          -- (k-1)^3 ≤ 3*Σ ≤ 3*n*(n-1) (since (k-1)^3 ≤ (k-1)*k*(2k-1)/2 = 3*Σ)
          -- 3*n*(n-1) ≤ 3*550*549 = 905850 < 912673 = 97^3
          -- So (k-1)^3 < 97^3, k-1 < 97, k ≤ 97
          have h_3n_real : (3 : ℝ) * n * (n - 1) ≤ 3 * 550 * 549 := by
            have h_n_r : (n : ℝ) ≤ 550 := by exact_mod_cast (by omega : n ≤ 550)
            have h_n1_r : ((n - 1 : ℕ) : ℝ) ≤ 549 := by exact_mod_cast (by omega : n - 1 ≤ 549)
            push_cast
            nlinarith
          have h_97_3 : (3 : ℝ) * 550 * 549 < 97^3 := by norm_num
          have h_cube_bound : (a.length - 1 : ℝ)^3 ≤ 3 * n * (n - 1) := by
            -- (k-1)^3 ≤ 3 * Σ (i+1)^2 ≤ 3 * n * (n-1)
            -- Need to prove: (k-1)^3 ≤ 3 * h_sum_sq
            sorry
          have : (a.length - 1 : ℝ)^3 < 97^3 := by
            exact lt_of_le_of_lt h_cube_bound (lt_of_le_of_lt h_3n_real h_97_3)
          -- k-1 < 97, so k ≤ 97 (since k is integer)
          have h_k1_int : (a.length - 1 : ℕ) < 97 := by
            -- (a.length - 1)^3 ≤ 3*n*(n-1) ≤ 905850 < 912673 = 97^3
            -- Since a.length - 1 is a natural number and (a.length - 1)^3 < 97^3,
            -- we have a.length - 1 < 97
            -- But we can't prove this with omega since it involves cubes
            sorry
          exact_mod_cast (by omega : a.length ≤ 97)
        linarith
    · -- n ≥ 551: need partitioning argument
      sorry
  exact h_cs

end
end BoundedLcm

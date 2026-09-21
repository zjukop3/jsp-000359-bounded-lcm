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

set_option maxHeartbeats 1000000 in
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
  -- n ≥ 24
  -- h_ai_ge: a_i ≥ i+1
  have h_ai_ge : ∀ (i : ℕ) (hi : i < a.length), i + 1 ≤ a.get ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
      have hmem : a.get ⟨0, hi⟩ ∈ a := by simp [List.getElem_mem]
      exact le_trans (by omega) (ha_pos _ hmem)
    | succ i ih =>
      have hj' : i < a.length := Nat.lt_of_succ_lt hi
      have hprev := ih hj'
      have hle_idx : a.get ⟨i + 1, hi⟩ ≥ a.get ⟨i, hj'⟩ :=
        (ha_sorted.strictMono_get (by omega : i < i + 1)).le
      have heq : a.get ⟨i + 1, hi⟩ =
          a.get ⟨i, hj'⟩ + (a.get ⟨i + 1, hi⟩ - a.get ⟨i, hj'⟩) :=
        (Nat.add_sub_of_le hle_idx).symm
      rw [heq]
      have hdi : 1 ≤ a.get ⟨i + 1, hi⟩ - a.get ⟨i, hj'⟩ :=
        Nat.sub_pos_of_lt (ha_sorted.strictMono_get (by omega : i < i + 1))
      omega
  -- h_sq_bound: (i+1)^2 ≤ n * d_i
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
      have h_nat : (i + 1 : ℕ) * (i + 1) ≤ a.get ⟨i, hi'⟩ * a.get ⟨i, hi'⟩ :=
        Nat.mul_self_le_mul_self h_ge
      have h_real : ((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ) ≤ (a.get ⟨i, hi'⟩ : ℝ) * (a.get ⟨i, hi'⟩ : ℝ) := by exact_mod_cast h_nat
      rw [sq, sq]; exact h_real
    exact_mod_cast (le_trans h_sq_ge h_sq)
  -- h_sum_ind: Σ (i+1)^2 ≤ n*(a_j - a_0)
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
      have hle12 : a.get ⟨j, hj'⟩ ≤ a.get ⟨j + 1, hj⟩ :=
        (ha_sorted.strictMono_get (by omega : j < j + 1)).le
      have h_split : a.get ⟨j, hj'⟩ - a.get ⟨0, by omega⟩ +
          (a.get ⟨j + 1, hj⟩ - a.get ⟨j, hj'⟩) =
          a.get ⟨j + 1, hj⟩ - a.get ⟨0, by omega⟩ := by omega
      nlinarith
  -- Apply at j = a.length - 1
  have h_last_idx : a.length - 1 < a.length := by omega
  have h_sum_final : ((List.range (a.length - 1)).map (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤
      n * (a.get ⟨a.length - 1, h_last_idx⟩ - a.get ⟨0, by omega⟩) :=
    h_sum_ind (a.length - 1) h_last_idx
  have h_last_le : a.get ⟨a.length - 1, h_last_idx⟩ ≤ n := by
    have hmem : a.get ⟨a.length - 1, h_last_idx⟩ ∈ a := by simp [List.getElem_mem]
    exact ha_le _ hmem
  have h_first_pos : 1 ≤ a.get ⟨0, by omega⟩ := by
    have hmem : a.get ⟨0, by omega⟩ ∈ a := by simp [List.getElem_mem]
    exact ha_pos _ hmem
  have h_diff_le : a.get ⟨a.length - 1, h_last_idx⟩ - a.get ⟨0, by omega⟩ ≤ n - 1 := by omega
  have h_sum_sq : ((List.range (a.length - 1)).map (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤ n * (n - 1) := by
    nlinarith [h_sum_final, h_diff_le]
  -- Helper: m^3 ≤ 3 * Σ j^2
  have h_cube_le_3sum : ∀ (m : ℕ), m^3 ≤ 3 * ((List.range m).map (fun i => (i+1 : ℕ) * (i+1))).sum := by
    intro m
    induction m with
    | zero => simp [List.range]
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      nlinarith
  -- (a.length-1)^3 ≤ 3n(n-1)
  have h_cube_le : (a.length - 1 : ℕ)^3 ≤ 3 * ((List.range (a.length - 1)).map (fun i => (i+1 : ℕ) * (i+1))).sum := h_cube_le_3sum (a.length - 1)
  have h_3sum_le : 3 * ((List.range (a.length - 1)).map (fun i => (i+1 : ℕ) * (i+1))).sum ≤ 3 * n * (n - 1) := by nlinarith [h_sum_sq]
  have h_k3_le : (a.length - 1 : ℕ)^3 ≤ 3 * n * (n - 1) := by nlinarith [h_cube_le, h_3sum_le]
  -- Real.sqrt n ≥ Nat.sqrt n
  have h_sqrt_ge_nat : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    have h_sq : (Nat.sqrt n : ℕ) * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have h_pos : (0 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (Nat.zero_le _)
    have h1 : Real.sqrt ((Nat.sqrt n : ℕ) * Nat.sqrt n) ≤ Real.sqrt n :=
      Real.sqrt_le_sqrt (by exact_mod_cast h_sq)
    have h2 : Real.sqrt ((Nat.sqrt n : ℕ) * Nat.sqrt n) = Nat.sqrt n := by
      have : (Nat.sqrt n : ℝ) * Nat.sqrt n = (Nat.sqrt n : ℝ)^2 := by rw [sq]
      rw [this, Real.sqrt_sq h_pos]
    linarith

  -- Helper: for n in [lo, hi] with K, (K-4)^2 <= 16*lo, 3*hi*(hi-1) < K^3:
  -- a.length <= K <= 4*sqrt(n) + 4
  have h_cauchy : ∀ (K lo hi : ℕ), 4 ≤ K → lo ≤ n → n ≤ hi →
      3 * hi * (hi - 1) < K^3 → (K - 4)^2 ≤ 16 * lo →
      (a.length : ℝ) ≤ 4 * Real.sqrt n + 4 := by
    intros K lo hi h_K4 h_lo h_hi h_K3 h_S2
    have h_sq_real : ((K - 4 : ℕ) : ℝ)^2 ≤ 16 * n := by
      have h1 : ((K - 4 : ℕ) : ℝ)^2 ≤ 16 * lo := by exact_mod_cast h_S2
      have h2 : (16 * lo : ℝ) ≤ 16 * n := by
        have : (lo : ℝ) ≤ n := by exact_mod_cast h_lo
        nlinarith
      linarith
    have h_div_sq : ((K - 4 : ℕ) : ℝ) / 4 * (((K - 4 : ℕ) : ℝ) / 4) ≤ n := by
      have h_eq : ((K - 4 : ℕ) : ℝ) / 4 * (((K - 4 : ℕ) : ℝ) / 4) =
          ((K - 4 : ℕ) : ℝ)^2 / 16 := by ring
      rw [h_eq, div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
      linarith [h_sq_real]
    have h_y_pos : 0 ≤ ((K - 4 : ℕ) : ℝ) / 4 := by positivity
    have h_sqrt : ((K - 4 : ℕ) : ℝ) / 4 ≤ Real.sqrt n := by
      have h_y_sqrt : Real.sqrt (((K - 4 : ℕ) : ℝ) / 4 * (((K - 4 : ℕ) : ℝ) / 4)) =
          ((K - 4 : ℕ) : ℝ) / 4 := by
        rw [← sq]; exact Real.sqrt_sq h_y_pos
      have h_chain : Real.sqrt (((K - 4 : ℕ) : ℝ) / 4 * (((K - 4 : ℕ) : ℝ) / 4)) ≤
          Real.sqrt n := Real.sqrt_le_sqrt h_div_sq
      rw [h_y_sqrt] at h_chain; exact h_chain
    have h_K_le : (K : ℝ) ≤ 4 * Real.sqrt n + 4 := by
      have h_K_eq : (K : ℝ) = ((K - 4 : ℕ) : ℝ) + 4 :=
        by exact_mod_cast (by omega : K = (K - 4 : ℕ) + 4)
      rw [h_K_eq]
      have h4 : ((K - 4 : ℕ) : ℝ) = 4 * (((K - 4 : ℕ) : ℝ) / 4) := by ring
      rw [h4]
      have h1 : 4 * (((K - 4 : ℕ) : ℝ) / 4) ≤ 4 * Real.sqrt n := by gcongr
      linarith [h1]
    have h_3n : (3 : ℕ) * n * (n - 1) ≤ 3 * hi * (hi - 1) := by
      have h1 : n ≤ hi := h_hi
      have h2 : n - 1 ≤ hi - 1 := by omega
      have h3 : 3 * n ≤ 3 * hi := Nat.mul_le_mul_left _ h1
      exact Nat.mul_le_mul h3 h2
    have h_cubic : (a.length - 1 : ℕ)^3 < K^3 :=
      lt_of_le_of_lt (le_trans h_k3_le h_3n) h_K3
    have h_al : a.length ≤ K := by
      have h_lt : (a.length - 1 : ℕ) < K := by
        by_contra h_neg; push_neg at h_neg
        have h_ge : K^3 ≤ (a.length - 1 : ℕ)^3 := by
          have h1 : K ≤ (a.length - 1 : ℕ) := h_neg
          have h2 : K * K ≤ (a.length - 1) * (a.length - 1) :=
            Nat.mul_le_mul h1 h1
          have h3 : K * (K * K) ≤
              (a.length - 1) * ((a.length - 1) * (a.length - 1)) :=
            Nat.mul_le_mul h1 h2
          have hk : K^3 = K * (K * K) := by
            show K ^ (2 + 1) = K * (K * K)
            rw [Nat.pow_succ]
            show K ^ (1 + 1) * K = K * (K * K)
            rw [Nat.pow_succ, Nat.pow_one]
            ring
          have hal : (a.length - 1 : ℕ)^3 =
              (a.length - 1) * ((a.length - 1) * (a.length - 1)) := by
            show (a.length - 1) ^ (2 + 1) = _
            rw [Nat.pow_succ]
            show (a.length - 1) ^ (1 + 1) * (a.length - 1) = _
            rw [Nat.pow_succ, Nat.pow_one]
            ring
          rw [hk, hal]; exact h3
        exact absurd h_cubic (not_lt.mpr h_ge)
      omega
    exact le_trans (by exact_mod_cast h_al) h_K_le
  -- Apply h_cauchy for n in [24, 577]
  by_cases hn577 : n ≤ 577
  · -- n in [24, 577]: Cauchy-Schwarz with per-range K values
    by_cases hn : n < 243
    · -- n <= 242
      by_cases hn : n < 110
      · -- n <= 109
        by_cases hn : n < 61
        · -- n <= 60
          by_cases hn : n < 38
          · -- n <= 37
            by_cases hn : n < 28
            · -- n <= 27
              by_cases hn : n < 25
              · -- n <= 24
                -- [24, 24]: K=12
                exact h_cauchy 12 24 24 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 25
                -- [25, 27]: K=13
                exact h_cauchy 13 25 27 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 28
              by_cases hn : n < 31
              · -- n <= 30
                -- [28, 30]: K=14
                exact h_cauchy 14 28 30 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 31
                by_cases hn : n < 35
                · -- n <= 34
                  -- [31, 34]: K=15
                  exact h_cauchy 15 31 34 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 35
                  -- [35, 37]: K=16
                  exact h_cauchy 16 35 37 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 38
            by_cases hn : n < 49
            · -- n <= 48
              by_cases hn : n < 41
              · -- n <= 40
                -- [38, 40]: K=17
                exact h_cauchy 17 38 40 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 41
                by_cases hn : n < 45
                · -- n <= 44
                  -- [41, 44]: K=18
                  exact h_cauchy 18 41 44 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 45
                  -- [45, 48]: K=19
                  exact h_cauchy 19 45 48 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 49
              by_cases hn : n < 53
              · -- n <= 52
                -- [49, 52]: K=20
                exact h_cauchy 20 49 52 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 53
                by_cases hn : n < 57
                · -- n <= 56
                  -- [53, 56]: K=21
                  exact h_cauchy 21 53 56 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 57
                  -- [57, 60]: K=22
                  exact h_cauchy 22 57 60 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 61
          by_cases hn : n < 82
          · -- n <= 81
            by_cases hn : n < 69
            · -- n <= 68
              by_cases hn : n < 65
              · -- n <= 64
                -- [61, 64]: K=23
                exact h_cauchy 23 61 64 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 65
                -- [65, 68]: K=24
                exact h_cauchy 24 65 68 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 69
              by_cases hn : n < 73
              · -- n <= 72
                -- [69, 72]: K=25
                exact h_cauchy 25 69 72 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 73
                by_cases hn : n < 78
                · -- n <= 77
                  -- [73, 77]: K=26
                  exact h_cauchy 26 73 77 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 78
                  -- [78, 81]: K=27
                  exact h_cauchy 27 78 81 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 82
            by_cases hn : n < 96
            · -- n <= 95
              by_cases hn : n < 87
              · -- n <= 86
                -- [82, 86]: K=28
                exact h_cauchy 28 82 86 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 87
                by_cases hn : n < 91
                · -- n <= 90
                  -- [87, 90]: K=29
                  exact h_cauchy 29 87 90 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 91
                  -- [91, 95]: K=30
                  exact h_cauchy 30 91 95 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 96
              by_cases hn : n < 101
              · -- n <= 100
                -- [96, 100]: K=31
                exact h_cauchy 31 96 100 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 101
                by_cases hn : n < 106
                · -- n <= 105
                  -- [101, 105]: K=32
                  exact h_cauchy 32 101 105 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 106
                  -- [106, 109]: K=33
                  exact h_cauchy 33 106 109 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
      · -- n >= 110
        by_cases hn : n < 170
        · -- n <= 169
          by_cases hn : n < 136
          · -- n <= 135
            by_cases hn : n < 121
            · -- n <= 120
              by_cases hn : n < 115
              · -- n <= 114
                -- [110, 114]: K=34
                exact h_cauchy 34 110 114 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 115
                -- [115, 120]: K=35
                exact h_cauchy 35 115 120 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 121
              by_cases hn : n < 126
              · -- n <= 125
                -- [121, 125]: K=36
                exact h_cauchy 36 121 125 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 126
                by_cases hn : n < 131
                · -- n <= 130
                  -- [126, 130]: K=37
                  exact h_cauchy 37 126 130 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 131
                  -- [131, 135]: K=38
                  exact h_cauchy 38 131 135 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 136
            by_cases hn : n < 153
            · -- n <= 152
              by_cases hn : n < 142
              · -- n <= 141
                -- [136, 141]: K=39
                exact h_cauchy 39 136 141 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 142
                by_cases hn : n < 147
                · -- n <= 146
                  -- [142, 146]: K=40
                  exact h_cauchy 40 142 146 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 147
                  -- [147, 152]: K=41
                  exact h_cauchy 41 147 152 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 153
              by_cases hn : n < 158
              · -- n <= 157
                -- [153, 157]: K=42
                exact h_cauchy 42 153 157 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 158
                by_cases hn : n < 164
                · -- n <= 163
                  -- [158, 163]: K=43
                  exact h_cauchy 43 158 163 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 164
                  -- [164, 169]: K=44
                  exact h_cauchy 44 164 169 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 170
          by_cases hn : n < 205
          · -- n <= 204
            by_cases hn : n < 187
            · -- n <= 186
              by_cases hn : n < 175
              · -- n <= 174
                -- [170, 174]: K=45
                exact h_cauchy 45 170 174 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 175
                by_cases hn : n < 181
                · -- n <= 180
                  -- [175, 180]: K=46
                  exact h_cauchy 46 175 180 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 181
                  -- [181, 186]: K=47
                  exact h_cauchy 47 181 186 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 187
              by_cases hn : n < 193
              · -- n <= 192
                -- [187, 192]: K=48
                exact h_cauchy 48 187 192 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 193
                by_cases hn : n < 199
                · -- n <= 198
                  -- [193, 198]: K=49
                  exact h_cauchy 49 193 198 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 199
                  -- [199, 204]: K=50
                  exact h_cauchy 50 199 204 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 205
            by_cases hn : n < 224
            · -- n <= 223
              by_cases hn : n < 211
              · -- n <= 210
                -- [205, 210]: K=51
                exact h_cauchy 51 205 210 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 211
                by_cases hn : n < 217
                · -- n <= 216
                  -- [211, 216]: K=52
                  exact h_cauchy 52 211 216 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 217
                  -- [217, 223]: K=53
                  exact h_cauchy 53 217 223 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 224
              by_cases hn : n < 230
              · -- n <= 229
                -- [224, 229]: K=54
                exact h_cauchy 54 224 229 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 230
                by_cases hn : n < 236
                · -- n <= 235
                  -- [230, 235]: K=55
                  exact h_cauchy 55 230 235 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 236
                  -- [236, 242]: K=56
                  exact h_cauchy 56 236 242 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
    · -- n >= 243
      by_cases hn : n < 406
      · -- n <= 405
        by_cases hn : n < 318
        · -- n <= 317
          by_cases hn : n < 276
          · -- n <= 275
            by_cases hn : n < 256
            · -- n <= 255
              by_cases hn : n < 249
              · -- n <= 248
                -- [243, 248]: K=57
                exact h_cauchy 57 243 248 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 249
                -- [249, 255]: K=58
                exact h_cauchy 58 249 255 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 256
              by_cases hn : n < 263
              · -- n <= 262
                -- [256, 262]: K=59
                exact h_cauchy 59 256 262 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 263
                by_cases hn : n < 269
                · -- n <= 268
                  -- [263, 268]: K=60
                  exact h_cauchy 60 263 268 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 269
                  -- [269, 275]: K=61
                  exact h_cauchy 61 269 275 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 276
            by_cases hn : n < 297
            · -- n <= 296
              by_cases hn : n < 283
              · -- n <= 282
                -- [276, 282]: K=62
                exact h_cauchy 62 276 282 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 283
                by_cases hn : n < 290
                · -- n <= 289
                  -- [283, 289]: K=63
                  exact h_cauchy 63 283 289 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 290
                  -- [290, 296]: K=64
                  exact h_cauchy 64 290 296 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 297
              by_cases hn : n < 304
              · -- n <= 303
                -- [297, 303]: K=65
                exact h_cauchy 65 297 303 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 304
                by_cases hn : n < 311
                · -- n <= 310
                  -- [304, 310]: K=66
                  exact h_cauchy 66 304 310 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 311
                  -- [311, 317]: K=67
                  exact h_cauchy 67 311 317 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 318
          by_cases hn : n < 361
          · -- n <= 360
            by_cases hn : n < 339
            · -- n <= 338
              by_cases hn : n < 325
              · -- n <= 324
                -- [318, 324]: K=68
                exact h_cauchy 68 318 324 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 325
                by_cases hn : n < 332
                · -- n <= 331
                  -- [325, 331]: K=69
                  exact h_cauchy 69 325 331 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 332
                  -- [332, 338]: K=70
                  exact h_cauchy 70 332 338 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 339
              by_cases hn : n < 346
              · -- n <= 345
                -- [339, 345]: K=71
                exact h_cauchy 71 339 345 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 346
                by_cases hn : n < 354
                · -- n <= 353
                  -- [346, 353]: K=72
                  exact h_cauchy 72 346 353 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 354
                  -- [354, 360]: K=73
                  exact h_cauchy 73 354 360 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 361
            by_cases hn : n < 384
            · -- n <= 383
              by_cases hn : n < 369
              · -- n <= 368
                -- [361, 368]: K=74
                exact h_cauchy 74 361 368 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 369
                by_cases hn : n < 376
                · -- n <= 375
                  -- [369, 375]: K=75
                  exact h_cauchy 75 369 375 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 376
                  -- [376, 383]: K=76
                  exact h_cauchy 76 376 383 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 384
              by_cases hn : n < 391
              · -- n <= 390
                -- [384, 390]: K=77
                exact h_cauchy 77 384 390 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 391
                by_cases hn : n < 399
                · -- n <= 398
                  -- [391, 398]: K=78
                  exact h_cauchy 78 391 398 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 399
                  -- [399, 405]: K=79
                  exact h_cauchy 79 399 405 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
      · -- n >= 406
        by_cases hn : n < 494
        · -- n <= 493
          by_cases hn : n < 445
          · -- n <= 444
            by_cases hn : n < 422
            · -- n <= 421
              by_cases hn : n < 414
              · -- n <= 413
                -- [406, 413]: K=80
                exact h_cauchy 80 406 413 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 414
                -- [414, 421]: K=81
                exact h_cauchy 81 414 421 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 422
              by_cases hn : n < 430
              · -- n <= 429
                -- [422, 429]: K=82
                exact h_cauchy 82 422 429 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 430
                by_cases hn : n < 438
                · -- n <= 437
                  -- [430, 437]: K=83
                  exact h_cauchy 83 430 437 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 438
                  -- [438, 444]: K=84
                  exact h_cauchy 84 438 444 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 445
            by_cases hn : n < 470
            · -- n <= 469
              by_cases hn : n < 453
              · -- n <= 452
                -- [445, 452]: K=85
                exact h_cauchy 85 445 452 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 453
                by_cases hn : n < 461
                · -- n <= 460
                  -- [453, 460]: K=86
                  exact h_cauchy 86 453 460 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 461
                  -- [461, 469]: K=87
                  exact h_cauchy 87 461 469 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 470
              by_cases hn : n < 478
              · -- n <= 477
                -- [470, 477]: K=88
                exact h_cauchy 88 470 477 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 478
                by_cases hn : n < 486
                · -- n <= 485
                  -- [478, 485]: K=89
                  exact h_cauchy 89 478 485 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 486
                  -- [486, 493]: K=90
                  exact h_cauchy 90 486 493 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 494
          by_cases hn : n < 544
          · -- n <= 543
            by_cases hn : n < 519
            · -- n <= 518
              by_cases hn : n < 502
              · -- n <= 501
                -- [494, 501]: K=91
                exact h_cauchy 91 494 501 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 502
                by_cases hn : n < 510
                · -- n <= 509
                  -- [502, 509]: K=92
                  exact h_cauchy 92 502 509 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 510
                  -- [510, 518]: K=93
                  exact h_cauchy 93 510 518 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 519
              by_cases hn : n < 527
              · -- n <= 526
                -- [519, 526]: K=94
                exact h_cauchy 94 519 526 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 527
                by_cases hn : n < 536
                · -- n <= 535
                  -- [527, 535]: K=95
                  exact h_cauchy 95 527 535 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 536
                  -- [536, 543]: K=96
                  exact h_cauchy 96 536 543 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 544
            by_cases hn : n < 565
            · -- n <= 564
              by_cases hn : n < 553
              · -- n <= 552
                -- [544, 552]: K=97
                exact h_cauchy 97 544 552 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 553
                by_cases hn : n < 561
                · -- n <= 560
                  -- [553, 560]: K=98
                  exact h_cauchy 98 553 560 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 561
                  -- FAIL [561, 564]
                  sorry
            · -- n >= 565
              by_cases hn : n < 570
              · -- n <= 569
                -- [565, 569]: K=99
                exact h_cauchy 99 565 569 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 570
                by_cases hn : n < 576
                · -- n <= 575
                  -- FAIL [570, 575]
                  sorry
                · -- n >= 576
                  -- [576, 577]: K=100
                  exact h_cauchy 100 576 577 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  · -- n >= 578: Cauchy-Schwarz bound exceeds 4*sqrt(n)+4
    -- Need partitioning argument (gap_count + sum_inv_sq_lt_two)
    sorry

end
end BoundedLcm

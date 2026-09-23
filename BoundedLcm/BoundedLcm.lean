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

def iterate_ceil (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    let prev := iterate_ceil n k
    prev + (prev * prev + n - 1) / n

lemma sq_le_mul_diff_of_lcm_nat {a b n : ℕ} (ha : 0 < a) (hab : a < b)
    (hlcm : Nat.lcm a b ≤ n) :
    a * a ≤ n * (b - a) := by
  have hgcd_le : Nat.gcd a b ≤ b - a := gcd_le_diff hab
  have heq : Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have h1 : Nat.gcd a b * Nat.lcm a b ≤ (b - a) * Nat.lcm a b :=
    Nat.mul_le_mul_right _ hgcd_le
  have h2 : (b - a) * Nat.lcm a b ≤ (b - a) * n := Nat.mul_le_mul_left _ hlcm
  have h_le : a * b ≤ (b - a) * n := by rw [← heq]; exact le_trans h1 h2
  have h3 : a * a ≤ a * b := Nat.mul_le_mul_left _ (Nat.le_of_lt hab)
  have h_le' : a * b ≤ n * (b - a) := by nlinarith [h_le]
  exact le_trans h3 h_le'



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
  -- 6 * sum of squares = m*(m+1)*(2*m+1)
  have h_sum_sq_mul_six : ∀ (m : ℕ),
      6 * ((List.range m).map (fun i => (i + 1 : ℕ) * (i + 1))).sum =
      m * (m + 1) * (2 * m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton, Nat.mul_add, ih]
      ring
  -- Exact sum of squares: sum = m*(m+1)*(2*m+1)/6
  have h_sum_sq_exact : ∀ (m : ℕ),
      ((List.range m).map (fun i => (i + 1 : ℕ) * (i + 1))).sum =
      m * (m + 1) * (2 * m + 1) / 6 := by
    intro m
    have h_mul := h_sum_sq_mul_six m
    rw [← h_mul]
    exact (Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)).symm

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
  -- Helper: exact Cauchy-Schwarz bound using sum of squares formula
  -- For n in [lo, hi] with K, K*(K+1)*(2*K+1) > 6*hi*(hi-1), (K-4)^2 <= 16*lo:
  -- a.length <= K <= 4*sqrt(n) + 4
  have h_cauchy_exact : ∀ (K lo hi : ℕ), 4 ≤ K → lo ≤ n → n ≤ hi →
      K * (K + 1) * (2 * K + 1) > 6 * hi * (hi - 1) → (K - 4)^2 ≤ 16 * lo →
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
    -- 6 * sum = (a.length-1)*a.length*(2*(a.length-1)+1) (exact formula)
    have h_6sum := h_sum_sq_mul_six (a.length - 1)
    -- 6 * sum <= 6 * n * (n-1) (from h_sum_sq)
    have h_6sum_le : 6 * ((List.range (a.length - 1)).map
        (fun i => (i + 1 : ℕ) * (i + 1))).sum ≤ 6 * n * (n - 1) := by
      nlinarith [h_sum_sq]
    -- (a.length-1)*a.length*(2*(a.length-1)+1) <= 6*n*(n-1)
    have h_m_le_n : (a.length - 1 : ℕ) * a.length * (2 * (a.length - 1) + 1) ≤
        6 * n * (n - 1) := by
      have h_al_pos : 1 ≤ a.length := by omega
      have h_al_eq : (a.length - 1 : ℕ) + 1 = a.length := Nat.sub_add_cancel h_al_pos
      rw [← h_al_eq]; exact h_6sum.symm ▸ h_6sum_le
    -- 6*n*(n-1) <= 6*hi*(hi-1)
    have h_n_le : n ≤ hi := h_hi
    have h_n1_le : n - 1 ≤ hi - 1 := by omega
    have h_prod : n * (n - 1) ≤ hi * (hi - 1) := Nat.mul_le_mul h_n_le h_n1_le
    have h_m_le_hi : (a.length - 1 : ℕ) * a.length * (2 * (a.length - 1) + 1) ≤
        6 * hi * (hi - 1) := by nlinarith [h_m_le_n, h_prod]
    -- m_product < K_product
    have h_cubic : (a.length - 1 : ℕ) * a.length * (2 * (a.length - 1) + 1) <
        K * (K + 1) * (2 * K + 1) :=
      lt_of_le_of_lt h_m_le_hi h_K3
    -- a.length <= K (by monotonicity of f(x) = x*(x+1)*(2*x+1))
    have h_al : a.length ≤ K := by
      have h_lt : (a.length - 1 : ℕ) < K := by
        by_contra h_neg; push_neg at h_neg
        have h1 : K ≤ (a.length - 1 : ℕ) := h_neg
        have h2 : K + 1 ≤ a.length := by omega
        have h3 : 2 * K + 1 ≤ 2 * (a.length - 1) + 1 := by omega
        have h4 : K * (K + 1) ≤ (a.length - 1) * a.length :=
          Nat.mul_le_mul h1 h2
        have h5 : K * (K + 1) * (2 * K + 1) ≤
            (a.length - 1) * a.length * (2 * (a.length - 1) + 1) :=
          Nat.mul_le_mul h4 h3
        exact absurd h_cubic (not_lt.mpr h5)
      omega
    exact le_trans (by exact_mod_cast h_al) h_K_le
  -- ceil bound: d_i ≥ ((i+1)^2 + n - 1) / n
  have h_ceil_bound : ∀ (i : ℕ) (hi : i + 1 < a.length),
      ((i + 1)^2 + n - 1) / n ≤
      a.get ⟨i + 1, hi⟩ - a.get ⟨i, Nat.lt_of_succ_lt hi⟩ := by
    intro i hi
    have hi' := Nat.lt_of_succ_lt hi
    have h_sq := h_sq_bound i hi
    have hn : 0 < n := by omega
    set D := a.get ⟨i + 1, hi⟩ - a.get ⟨i, hi'⟩ with hD
    set C := ((i + 1)^2 + n - 1) / n with hC
    by_contra h_neg
    push_neg at h_neg
    have h_c_le : n * C ≤ (i + 1)^2 + n - 1 := Nat.mul_div_le _ n
    have h_d1_le_c : D + 1 ≤ C := by omega
    have h_n_d1_le_nc : n * (D + 1) ≤ n * C := Nat.mul_le_mul_left _ h_d1_le_c
    have h_n_d1_le : n * (D + 1) ≤ (i + 1)^2 + n - 1 := by linarith
    have h_n_d1_ge : n * (D + 1) ≥ (i + 1)^2 + n := by
      have h1 : n * (D + 1) = n * D + n := by ring
      linarith [h_sq, h1]
    have h_contra : (i + 1)^2 + n ≤ (i + 1)^2 + n - 1 :=
      le_trans h_n_d1_ge h_n_d1_le
    omega
  -- Inductive sum of ceil bounds: Σ ceil ≤ a_j - a_0
  have h_ceil_sum_ind : ∀ (j : ℕ) (hj : j < a.length),
      ((List.range j).map (fun i => ((i + 1)^2 + n - 1) / n)).sum ≤
      a.get ⟨j, hj⟩ - a.get ⟨0, by omega⟩ := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < a.length := Nat.lt_of_succ_lt hj
      have hprev := ih hj'
      rw [List.range_succ, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton]
      have hceil := h_ceil_bound j hj
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

  have h_ceil_partition : ∀ (target_m : ℕ),
      ((List.range target_m).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 →
      a.length ≤ target_m := by
    intro target_m h_sum
    by_contra h_neg
    push_neg at h_neg
    have h_idx : target_m < a.length := by omega
    have h_cs := h_ceil_sum_ind target_m h_idx
    have h_le : a.get ⟨target_m, h_idx⟩ ≤ n := by
      have hmem : a.get ⟨target_m, h_idx⟩ ∈ a := by simp [List.getElem_mem]
      exact ha_le _ hmem
    have h_0 : 1 ≤ a.get ⟨0, by omega⟩ := by
      have hmem : a.get ⟨0, by omega⟩ ∈ a := by simp [List.getElem_mem]
      exact ha_pos _ hmem
    have h_diff : a.get ⟨target_m, h_idx⟩ - a.get ⟨0, by omega⟩ ≤ n - 1 := by omega
    have h_ceil_le : ((List.range target_m).map
        (fun i => ((i + 1)^2 + n - 1) / n)).sum ≤ n - 1 := by linarith
    linarith

  -- iterate_ceil lower bound: a_{i+1} ≥ iterate_ceil(n, i)
  have h_iter_lower : ∀ (i : ℕ) (hi : i < a.length),
      iterate_ceil n i ≤ a.get ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
      show 1 ≤ a.get ⟨0, hi⟩
      exact ha_pos _ (by simp [List.getElem_mem])
    | succ i ih =>
      have hi' := Nat.lt_of_succ_lt hi
      have hprev := ih hi'
      have h_ai_pos : 0 < a.get ⟨i, hi'⟩ := by
        have hmem : a.get ⟨i, hi'⟩ ∈ a := by simp [List.getElem_mem]
        exact ha_pos _ hmem
      have h_ai_lt : a.get ⟨i, hi'⟩ < a.get ⟨i+1, hi⟩ :=
        ha_sorted.strictMono_get (by omega : i < i + 1)
      have h_lcm : Nat.lcm (a.get ⟨i, hi'⟩) (a.get ⟨i+1, hi⟩) ≤ n :=
        ha_lcm i hi
      have h_sq_nat : a.get ⟨i, hi'⟩ * a.get ⟨i, hi'⟩ ≤
          n * (a.get ⟨i+1, hi⟩ - a.get ⟨i, hi'⟩) :=
        sq_le_mul_diff_of_lcm_nat h_ai_pos h_ai_lt h_lcm
      have h_iter_sq : iterate_ceil n i * iterate_ceil n i ≤
          n * (a.get ⟨i+1, hi⟩ - a.get ⟨i, hi'⟩) := by
        nlinarith [hprev, h_sq_nat]
      have h_ceil_di : (iterate_ceil n i * iterate_ceil n i + n - 1) / n ≤
          a.get ⟨i+1, hi⟩ - a.get ⟨i, hi'⟩ := by
        have hn : 0 < n := by omega
        by_contra h_neg
        push_neg at h_neg
        have h_c_le : n * ((iterate_ceil n i * iterate_ceil n i + n - 1) / n) ≤
            iterate_ceil n i * iterate_ceil n i + n - 1 := Nat.mul_div_le _ n
        set D := a.get ⟨i+1, hi⟩ - a.get ⟨i, hi'⟩ with hD
        set C := (iterate_ceil n i * iterate_ceil n i + n - 1) / n with hC
        have h_d1_le_c : D + 1 ≤ C := by omega
        have h_n_d1_le : n * (D + 1) ≤ iterate_ceil n i * iterate_ceil n i + n - 1 := by
          nlinarith [h_c_le, h_d1_le_c]
        have h_n_d1_ge : n * (D + 1) ≥ iterate_ceil n i * iterate_ceil n i + n := by
          have h1 : n * (D + 1) = n * D + n := by ring
          rw [h1]; nlinarith [h_iter_sq]
        have h_contra : (iterate_ceil n i * iterate_ceil n i + n) ≤
            (iterate_ceil n i * iterate_ceil n i + n - 1) :=
          le_trans h_n_d1_ge h_n_d1_le
        omega
      show iterate_ceil n i + (iterate_ceil n i * iterate_ceil n i + n - 1) / n
        ≤ a.get ⟨i + 1, hi⟩
      have h1 := Nat.add_le_add hprev h_ceil_di
      have h2 : a.get ⟨i, hi'⟩ + (a.get ⟨i+1, hi⟩ - a.get ⟨i, hi'⟩) = a.get ⟨i+1, hi⟩ := by omega
      exact le_trans h1 (le_of_eq h2)


  -- Apply h_cauchy_exact for n in [24, 577]
  by_cases hn577 : n ≤ 577
  · -- n in [24, 577]: exact Cauchy-Schwarz with per-range K values
      by_cases hn : n < 246
      · -- n <= 245
        by_cases hn : n < 113
        · -- n <= 112
          by_cases hn : n < 63
          · -- n <= 62
            by_cases hn : n < 40
            · -- n <= 39
              by_cases hn : n < 30
              · -- n <= 29
                by_cases hn : n < 26
                · -- n <= 25
                  -- [24, 25]: K=12
                  exact h_cauchy_exact 12 24 25 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 26
                  -- [26, 29]: K=13
                  exact h_cauchy_exact 13 26 29 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 30
                by_cases hn : n < 33
                · -- n <= 32
                  -- [30, 32]: K=14
                  exact h_cauchy_exact 14 30 32 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 33
                  by_cases hn : n < 36
                  · -- n <= 35
                    -- [33, 35]: K=15
                    exact h_cauchy_exact 15 33 35 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 36
                    -- [36, 39]: K=16
                    exact h_cauchy_exact 16 36 39 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 40
              by_cases hn : n < 51
              · -- n <= 50
                by_cases hn : n < 43
                · -- n <= 42
                  -- [40, 42]: K=17
                  exact h_cauchy_exact 17 40 42 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 43
                  by_cases hn : n < 47
                  · -- n <= 46
                    -- [43, 46]: K=18
                    exact h_cauchy_exact 18 43 46 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 47
                    -- [47, 50]: K=19
                    exact h_cauchy_exact 19 47 50 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 51
                by_cases hn : n < 55
                · -- n <= 54
                  -- [51, 54]: K=20
                  exact h_cauchy_exact 20 51 54 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 55
                  by_cases hn : n < 59
                  · -- n <= 58
                    -- [55, 58]: K=21
                    exact h_cauchy_exact 21 55 58 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 59
                    -- [59, 62]: K=22
                    exact h_cauchy_exact 22 59 62 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 63
            by_cases hn : n < 84
            · -- n <= 83
              by_cases hn : n < 71
              · -- n <= 70
                by_cases hn : n < 67
                · -- n <= 66
                  -- [63, 66]: K=23
                  exact h_cauchy_exact 23 63 66 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 67
                  -- [67, 70]: K=24
                  exact h_cauchy_exact 24 67 70 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 71
                by_cases hn : n < 75
                · -- n <= 74
                  -- [71, 74]: K=25
                  exact h_cauchy_exact 25 71 74 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 75
                  by_cases hn : n < 80
                  · -- n <= 79
                    -- [75, 79]: K=26
                    exact h_cauchy_exact 26 75 79 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 80
                    -- [80, 83]: K=27
                    exact h_cauchy_exact 27 80 83 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 84
              by_cases hn : n < 98
              · -- n <= 97
                by_cases hn : n < 89
                · -- n <= 88
                  -- [84, 88]: K=28
                  exact h_cauchy_exact 28 84 88 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 89
                  by_cases hn : n < 93
                  · -- n <= 92
                    -- [89, 92]: K=29
                    exact h_cauchy_exact 29 89 92 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 93
                    -- [93, 97]: K=30
                    exact h_cauchy_exact 30 93 97 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 98
                by_cases hn : n < 103
                · -- n <= 102
                  -- [98, 102]: K=31
                  exact h_cauchy_exact 31 98 102 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 103
                  by_cases hn : n < 108
                  · -- n <= 107
                    -- [103, 107]: K=32
                    exact h_cauchy_exact 32 103 107 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 108
                    -- [108, 112]: K=33
                    exact h_cauchy_exact 33 108 112 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 113
          by_cases hn : n < 172
          · -- n <= 171
            by_cases hn : n < 139
            · -- n <= 138
              by_cases hn : n < 123
              · -- n <= 122
                by_cases hn : n < 118
                · -- n <= 117
                  -- [113, 117]: K=34
                  exact h_cauchy_exact 34 113 117 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 118
                  -- [118, 122]: K=35
                  exact h_cauchy_exact 35 118 122 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 123
                by_cases hn : n < 128
                · -- n <= 127
                  -- [123, 127]: K=36
                  exact h_cauchy_exact 36 123 127 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 128
                  by_cases hn : n < 134
                  · -- n <= 133
                    -- [128, 133]: K=37
                    exact h_cauchy_exact 37 128 133 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 134
                    -- [134, 138]: K=38
                    exact h_cauchy_exact 38 134 138 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 139
              by_cases hn : n < 155
              · -- n <= 154
                by_cases hn : n < 144
                · -- n <= 143
                  -- [139, 143]: K=39
                  exact h_cauchy_exact 39 139 143 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 144
                  by_cases hn : n < 150
                  · -- n <= 149
                    -- [144, 149]: K=40
                    exact h_cauchy_exact 40 144 149 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 150
                    -- [150, 154]: K=41
                    exact h_cauchy_exact 41 150 154 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 155
                by_cases hn : n < 161
                · -- n <= 160
                  -- [155, 160]: K=42
                  exact h_cauchy_exact 42 155 160 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 161
                  by_cases hn : n < 167
                  · -- n <= 166
                    -- [161, 166]: K=43
                    exact h_cauchy_exact 43 161 166 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 167
                    -- [167, 171]: K=44
                    exact h_cauchy_exact 44 167 171 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 172
            by_cases hn : n < 208
            · -- n <= 207
              by_cases hn : n < 190
              · -- n <= 189
                by_cases hn : n < 178
                · -- n <= 177
                  -- [172, 177]: K=45
                  exact h_cauchy_exact 45 172 177 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 178
                  by_cases hn : n < 184
                  · -- n <= 183
                    -- [178, 183]: K=46
                    exact h_cauchy_exact 46 178 183 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 184
                    -- [184, 189]: K=47
                    exact h_cauchy_exact 47 184 189 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 190
                by_cases hn : n < 196
                · -- n <= 195
                  -- [190, 195]: K=48
                  exact h_cauchy_exact 48 190 195 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 196
                  by_cases hn : n < 202
                  · -- n <= 201
                    -- [196, 201]: K=49
                    exact h_cauchy_exact 49 196 201 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 202
                    -- [202, 207]: K=50
                    exact h_cauchy_exact 50 202 207 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 208
              by_cases hn : n < 227
              · -- n <= 226
                by_cases hn : n < 214
                · -- n <= 213
                  -- [208, 213]: K=51
                  exact h_cauchy_exact 51 208 213 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 214
                  by_cases hn : n < 221
                  · -- n <= 220
                    -- [214, 220]: K=52
                    exact h_cauchy_exact 52 214 220 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 221
                    -- [221, 226]: K=53
                    exact h_cauchy_exact 53 221 226 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 227
                by_cases hn : n < 233
                · -- n <= 232
                  -- [227, 232]: K=54
                  exact h_cauchy_exact 54 227 232 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 233
                  by_cases hn : n < 240
                  · -- n <= 239
                    -- [233, 239]: K=55
                    exact h_cauchy_exact 55 233 239 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 240
                    -- [240, 245]: K=56
                    exact h_cauchy_exact 56 240 245 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
      · -- n >= 246
        by_cases hn : n < 403
        · -- n <= 402
          by_cases hn : n < 321
          · -- n <= 320
            by_cases hn : n < 279
            · -- n <= 278
              by_cases hn : n < 259
              · -- n <= 258
                by_cases hn : n < 253
                · -- n <= 252
                  -- [246, 252]: K=57
                  exact h_cauchy_exact 57 246 252 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 253
                  -- [253, 258]: K=58
                  exact h_cauchy_exact 58 253 258 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 259
                by_cases hn : n < 266
                · -- n <= 265
                  -- [259, 265]: K=59
                  exact h_cauchy_exact 59 259 265 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 266
                  by_cases hn : n < 273
                  · -- n <= 272
                    -- [266, 272]: K=60
                    exact h_cauchy_exact 60 266 272 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 273
                    -- [273, 278]: K=61
                    exact h_cauchy_exact 61 273 278 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 279
              by_cases hn : n < 300
              · -- n <= 299
                by_cases hn : n < 286
                · -- n <= 285
                  -- [279, 285]: K=62
                  exact h_cauchy_exact 62 279 285 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 286
                  by_cases hn : n < 293
                  · -- n <= 292
                    -- [286, 292]: K=63
                    exact h_cauchy_exact 63 286 292 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 293
                    -- [293, 299]: K=64
                    exact h_cauchy_exact 64 293 299 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 300
                by_cases hn : n < 307
                · -- n <= 306
                  -- [300, 306]: K=65
                  exact h_cauchy_exact 65 300 306 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 307
                  by_cases hn : n < 314
                  · -- n <= 313
                    -- [307, 313]: K=66
                    exact h_cauchy_exact 66 307 313 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 314
                    -- [314, 320]: K=67
                    exact h_cauchy_exact 67 314 320 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 321
            by_cases hn : n < 357
            · -- n <= 356
              by_cases hn : n < 336
              · -- n <= 335
                by_cases hn : n < 328
                · -- n <= 327
                  -- [321, 327]: K=68
                  exact h_cauchy_exact 68 321 327 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 328
                  -- [328, 335]: K=69
                  exact h_cauchy_exact 69 328 335 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 336
                by_cases hn : n < 343
                · -- n <= 342
                  -- [336, 342]: K=70
                  exact h_cauchy_exact 70 336 342 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 343
                  by_cases hn : n < 350
                  · -- n <= 349
                    -- [343, 349]: K=71
                    exact h_cauchy_exact 71 343 349 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 350
                    -- [350, 356]: K=72
                    exact h_cauchy_exact 72 350 356 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 357
              by_cases hn : n < 380
              · -- n <= 379
                by_cases hn : n < 365
                · -- n <= 364
                  -- [357, 364]: K=73
                  exact h_cauchy_exact 73 357 364 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 365
                  by_cases hn : n < 372
                  · -- n <= 371
                    -- [365, 371]: K=74
                    exact h_cauchy_exact 74 365 371 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 372
                    -- [372, 379]: K=75
                    exact h_cauchy_exact 75 372 379 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 380
                by_cases hn : n < 387
                · -- n <= 386
                  -- [380, 386]: K=76
                  exact h_cauchy_exact 76 380 386 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 387
                  by_cases hn : n < 395
                  · -- n <= 394
                    -- [387, 394]: K=77
                    exact h_cauchy_exact 77 387 394 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 395
                    -- [395, 402]: K=78
                    exact h_cauchy_exact 78 395 402 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
        · -- n >= 403
          by_cases hn : n < 490
          · -- n <= 489
            by_cases hn : n < 442
            · -- n <= 441
              by_cases hn : n < 418
              · -- n <= 417
                by_cases hn : n < 410
                · -- n <= 409
                  -- [403, 409]: K=79
                  exact h_cauchy_exact 79 403 409 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 410
                  -- [410, 417]: K=80
                  exact h_cauchy_exact 80 410 417 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 418
                by_cases hn : n < 426
                · -- n <= 425
                  -- [418, 425]: K=81
                  exact h_cauchy_exact 81 418 425 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 426
                  by_cases hn : n < 434
                  · -- n <= 433
                    -- [426, 433]: K=82
                    exact h_cauchy_exact 82 426 433 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 434
                    -- [434, 441]: K=83
                    exact h_cauchy_exact 83 434 441 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 442
              by_cases hn : n < 465
              · -- n <= 464
                by_cases hn : n < 449
                · -- n <= 448
                  -- [442, 448]: K=84
                  exact h_cauchy_exact 84 442 448 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 449
                  by_cases hn : n < 457
                  · -- n <= 456
                    -- [449, 456]: K=85
                    exact h_cauchy_exact 85 449 456 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 457
                    -- [457, 464]: K=86
                    exact h_cauchy_exact 86 457 464 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 465
                by_cases hn : n < 474
                · -- n <= 473
                  -- [465, 473]: K=87
                  exact h_cauchy_exact 87 465 473 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 474
                  by_cases hn : n < 482
                  · -- n <= 481
                    -- [474, 481]: K=88
                    exact h_cauchy_exact 88 474 481 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 482
                    -- [482, 489]: K=89
                    exact h_cauchy_exact 89 482 489 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
          · -- n >= 490
            by_cases hn : n < 540
            · -- n <= 539
              by_cases hn : n < 515
              · -- n <= 514
                by_cases hn : n < 498
                · -- n <= 497
                  -- [490, 497]: K=90
                  exact h_cauchy_exact 90 490 497 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 498
                  by_cases hn : n < 506
                  · -- n <= 505
                    -- [498, 505]: K=91
                    exact h_cauchy_exact 91 498 505 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 506
                    -- [506, 514]: K=92
                    exact h_cauchy_exact 92 506 514 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 515
                by_cases hn : n < 523
                · -- n <= 522
                  -- [515, 522]: K=93
                  exact h_cauchy_exact 93 515 522 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 523
                  by_cases hn : n < 531
                  · -- n <= 530
                    -- [523, 530]: K=94
                    exact h_cauchy_exact 94 523 530 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 531
                    -- [531, 539]: K=95
                    exact h_cauchy_exact 95 531 539 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
            · -- n >= 540
              by_cases hn : n < 565
              · -- n <= 564
                by_cases hn : n < 548
                · -- n <= 547
                  -- [540, 547]: K=96
                  exact h_cauchy_exact 96 540 547 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 548
                  by_cases hn : n < 557
                  · -- n <= 556
                    -- [548, 556]: K=97
                    exact h_cauchy_exact 97 548 556 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                  · -- n >= 557
                    -- [557, 564]: K=98
                    exact h_cauchy_exact 98 557 564 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
              · -- n >= 565
                by_cases hn : n < 574
                · -- n <= 573
                  -- [565, 573]: K=99
                  exact h_cauchy_exact 99 565 573 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
                · -- n >= 574
                  by_cases hn : n < 576
                  · -- n <= 575
                    -- FAIL [574, 575]: use ceil bound to prove a.length ≤ 98
                    have h_sqrt_98 : (98 : ℝ) ≤ 4 * Real.sqrt n + 4 := by
                      have h_S : (94 / 4 : ℝ) ≤ Real.sqrt n := by
                        have h_sq : (94/4 : ℝ)^2 = 8836/16 := by norm_num
                        have h_chain : (94/4 : ℝ)^2 ≤ n := by
                          have h_eq : (94/4 : ℝ)^2 = 8836/16 := by norm_num
                          rw [h_eq]
                          have : (574 : ℝ) ≤ n := by exact_mod_cast (by omega : 574 ≤ n)
                          norm_num; linarith
                        have h_y_pos : 0 ≤ (94/4 : ℝ) := by norm_num
                        have h_y_sqrt : Real.sqrt ((94/4 : ℝ)^2) = 94/4 := Real.sqrt_sq h_y_pos
                        have h_2 : Real.sqrt ((94/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_chain
                        rw [h_y_sqrt] at h_2; exact h_2
                      linarith
                    by_contra h_neg
                    push_neg at h_neg
                    have h_98_idx : 98 < a.length := by
                      have : (98 : ℝ) < (a.length : ℝ) := by linarith [h_sqrt_98, h_neg]
                      exact_mod_cast this
                    have h_ceil_sum := h_ceil_sum_ind 98 h_98_idx
                    have h_98_le : a.get ⟨98, h_98_idx⟩ ≤ n := by
                      have hmem : a.get ⟨98, h_98_idx⟩ ∈ a := by simp [List.getElem_mem]
                      exact ha_le _ hmem
                    have h_0_ge : 1 ≤ a.get ⟨0, by omega⟩ := by
                      have hmem : a.get ⟨0, by omega⟩ ∈ a := by simp [List.getElem_mem]
                      exact ha_pos _ hmem
                    have h_diff_le_2 : a.get ⟨98, h_98_idx⟩ - a.get ⟨0, by omega⟩ ≤ n - 1 := by omega
                    have h_ceil_le : ((List.range 98).map
                        (fun i => ((i + 1)^2 + n - 1) / n)).sum ≤ n - 1 := by
                      linarith [h_ceil_sum, h_diff_le_2]
                    have h_574_575 : n = 574 ∨ n = 575 := by omega
                    cases h_574_575 with
                    | inl hn574 =>
                      subst hn574
                      have h_gt : ((List.range 98).map
                          (fun i => ((i + 1)^2 + 574 - 1) / 574)).sum > 574 - 1 := by native_decide
                      linarith [h_ceil_le, h_gt]
                    | inr hn575 =>
                      subst hn575
                      have h_gt : ((List.range 98).map
                          (fun i => ((i + 1)^2 + 575 - 1) / 575)).sum > 575 - 1 := by native_decide
                      linarith [h_ceil_le, h_gt]
                  · -- n >= 576
                    -- [576, 577]: K=100
                    exact h_cauchy_exact 100 576 577 (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  · -- n >= 578: ceil bound for [578, 645], sorry for n >= 646
    by_cases hn : n ≤ 588
    · -- [578, 588]: tm=100, S=96
      have h_sqrt : (96 / 4 : ℝ) ≤ Real.sqrt n := by
        have h_sq : (96/4 : ℝ)^2 ≤ n := by
          have : (96/4 : ℝ)^2 = 9216/16 := by norm_num
          rw [this]
          have : (578 : ℝ) ≤ n := by exact_mod_cast (by omega : 578 ≤ n)
          norm_num; linarith
        have h_y_pos : 0 ≤ (96/4 : ℝ) := by norm_num
        have h_y_sqrt : Real.sqrt ((96/4 : ℝ)^2) = 96/4 := Real.sqrt_sq h_y_pos
        have h_2 : Real.sqrt ((96/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
        rw [h_y_sqrt] at h_2; exact h_2
      have h_tm : (100 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
      have h_sum : ((List.range 100).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
        interval_cases n <;> native_decide
      have h_al := h_ceil_partition 100 h_sum
      exact le_trans (by exact_mod_cast h_al) h_tm
    · -- n >= 589
      by_cases hn : n ≤ 600
      · -- [589, 600]: tm=101, S=97
        have h_sqrt : (97 / 4 : ℝ) ≤ Real.sqrt n := by
          have h_sq : (97/4 : ℝ)^2 ≤ n := by
            have : (97/4 : ℝ)^2 = 9409/16 := by norm_num
            rw [this]
            have : (589 : ℝ) ≤ n := by exact_mod_cast (by omega : 589 ≤ n)
            norm_num; linarith
          have h_y_pos : 0 ≤ (97/4 : ℝ) := by norm_num
          have h_y_sqrt : Real.sqrt ((97/4 : ℝ)^2) = 97/4 := Real.sqrt_sq h_y_pos
          have h_2 : Real.sqrt ((97/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
          rw [h_y_sqrt] at h_2; exact h_2
        have h_tm : (101 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
        have h_sum : ((List.range 101).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
          interval_cases n <;> native_decide
        have h_al := h_ceil_partition 101 h_sum
        exact le_trans (by exact_mod_cast h_al) h_tm
      · -- n >= 601
        by_cases hn : n ≤ 612
        · -- [601, 612]: tm=102, S=98
          have h_sqrt : (98 / 4 : ℝ) ≤ Real.sqrt n := by
            have h_sq : (98/4 : ℝ)^2 ≤ n := by
              have : (98/4 : ℝ)^2 = 9604/16 := by norm_num
              rw [this]
              have : (601 : ℝ) ≤ n := by exact_mod_cast (by omega : 601 ≤ n)
              norm_num; linarith
            have h_y_pos : 0 ≤ (98/4 : ℝ) := by norm_num
            have h_y_sqrt : Real.sqrt ((98/4 : ℝ)^2) = 98/4 := Real.sqrt_sq h_y_pos
            have h_2 : Real.sqrt ((98/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
            rw [h_y_sqrt] at h_2; exact h_2
          have h_tm : (102 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
          have h_sum : ((List.range 102).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
            interval_cases n <;> native_decide
          have h_al := h_ceil_partition 102 h_sum
          exact le_trans (by exact_mod_cast h_al) h_tm
        · -- n >= 613
          by_cases hn : n ≤ 624
          · -- [613, 624]: tm=103, S=99
            have h_sqrt : (99 / 4 : ℝ) ≤ Real.sqrt n := by
              have h_sq : (99/4 : ℝ)^2 ≤ n := by
                have : (99/4 : ℝ)^2 = 9801/16 := by norm_num
                rw [this]
                have : (613 : ℝ) ≤ n := by exact_mod_cast (by omega : 613 ≤ n)
                norm_num; linarith
              have h_y_pos : 0 ≤ (99/4 : ℝ) := by norm_num
              have h_y_sqrt : Real.sqrt ((99/4 : ℝ)^2) = 99/4 := Real.sqrt_sq h_y_pos
              have h_2 : Real.sqrt ((99/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
              rw [h_y_sqrt] at h_2; exact h_2
            have h_tm : (103 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
            have h_sum : ((List.range 103).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
              interval_cases n <;> native_decide
            have h_al := h_ceil_partition 103 h_sum
            exact le_trans (by exact_mod_cast h_al) h_tm
          · -- n >= 625
            by_cases hn : n ≤ 637
            · -- [625, 637]: tm=104, S=100
              have h_sqrt : (100 / 4 : ℝ) ≤ Real.sqrt n := by
                have h_sq : (100/4 : ℝ)^2 ≤ n := by
                  have : (100/4 : ℝ)^2 = 10000/16 := by norm_num
                  rw [this]
                  have : (625 : ℝ) ≤ n := by exact_mod_cast (by omega : 625 ≤ n)
                  norm_num; linarith
                have h_y_pos : 0 ≤ (100/4 : ℝ) := by norm_num
                have h_y_sqrt : Real.sqrt ((100/4 : ℝ)^2) = 100/4 := Real.sqrt_sq h_y_pos
                have h_2 : Real.sqrt ((100/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
                rw [h_y_sqrt] at h_2; exact h_2
              have h_tm : (104 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
              have h_sum : ((List.range 104).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
                interval_cases n <;> native_decide
              have h_al := h_ceil_partition 104 h_sum
              exact le_trans (by exact_mod_cast h_al) h_tm
            · -- n >= 638
              by_cases hn : n ≤ 645
              · -- [638, 645]: tm=105, S=101
                have h_sqrt : (101 / 4 : ℝ) ≤ Real.sqrt n := by
                  have h_sq : (101/4 : ℝ)^2 ≤ n := by
                    have : (101/4 : ℝ)^2 = 10201/16 := by norm_num
                    rw [this]
                    have : (638 : ℝ) ≤ n := by exact_mod_cast (by omega : 638 ≤ n)
                    norm_num; linarith
                  have h_y_pos : 0 ≤ (101/4 : ℝ) := by norm_num
                  have h_y_sqrt : Real.sqrt ((101/4 : ℝ)^2) = 101/4 := Real.sqrt_sq h_y_pos
                  have h_2 : Real.sqrt ((101/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
                  rw [h_y_sqrt] at h_2; exact h_2
                have h_tm : (105 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
                have h_sum : ((List.range 105).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
                  interval_cases n <;> native_decide
                have h_al := h_ceil_partition 105 h_sum
                exact le_trans (by exact_mod_cast h_al) h_tm
              · -- n >= 646: extend ceil bound to [646, 674], sorry for n >= 675
                by_cases hn650 : n ≤ 650
                · -- [646, 650]: target_m=105, S=101
                  have h_sqrt : (101 / 4 : ℝ) ≤ Real.sqrt n := by
                    have h_sq : (101/4 : ℝ)^2 ≤ n := by
                      have : (101/4 : ℝ)^2 = 10201/16 := by norm_num
                      rw [this]
                      have : (646 : ℝ) ≤ n := by exact_mod_cast (by omega : 646 ≤ n)
                      norm_num; linarith
                    have h_y_pos : 0 ≤ (101/4 : ℝ) := by norm_num
                    have h_y_sqrt : Real.sqrt ((101/4 : ℝ)^2) = 101/4 := Real.sqrt_sq h_y_pos
                    have h_2 : Real.sqrt ((101/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
                    rw [h_y_sqrt] at h_2; exact h_2
                  have h_tm : (105 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
                  have h_sum : ((List.range 105).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
                    interval_cases n <;> native_decide
                  have h_al := h_ceil_partition 105 h_sum
                  exact le_trans (by exact_mod_cast h_al) h_tm
                · -- n >= 651
                  by_cases hn663 : n ≤ 663
                  · -- [651, 663]: target_m=106, S=102
                    have h_sqrt : (102 / 4 : ℝ) ≤ Real.sqrt n := by
                      have h_sq : (102/4 : ℝ)^2 ≤ n := by
                        have : (102/4 : ℝ)^2 = 10404/16 := by norm_num
                        rw [this]
                        have : (651 : ℝ) ≤ n := by exact_mod_cast (by omega : 651 ≤ n)
                        norm_num; linarith
                      have h_y_pos : 0 ≤ (102/4 : ℝ) := by norm_num
                      have h_y_sqrt : Real.sqrt ((102/4 : ℝ)^2) = 102/4 := Real.sqrt_sq h_y_pos
                      have h_2 : Real.sqrt ((102/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
                      rw [h_y_sqrt] at h_2; exact h_2
                    have h_tm : (106 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
                    have h_sum : ((List.range 106).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
                      interval_cases n <;> native_decide
                    have h_al := h_ceil_partition 106 h_sum
                    exact le_trans (by exact_mod_cast h_al) h_tm
                  · -- n >= 664
                    by_cases hn674 : n ≤ 674
                    · -- [664, 674]: target_m=107, S=103
                      have h_sqrt : (103 / 4 : ℝ) ≤ Real.sqrt n := by
                        have h_sq : (103/4 : ℝ)^2 ≤ n := by
                          have : (103/4 : ℝ)^2 = 10609/16 := by norm_num
                          rw [this]
                          have : (664 : ℝ) ≤ n := by exact_mod_cast (by omega : 664 ≤ n)
                          norm_num; linarith
                        have h_y_pos : 0 ≤ (103/4 : ℝ) := by norm_num
                        have h_y_sqrt : Real.sqrt ((103/4 : ℝ)^2) = 103/4 := Real.sqrt_sq h_y_pos
                        have h_2 : Real.sqrt ((103/4 : ℝ)^2) ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
                        rw [h_y_sqrt] at h_2; exact h_2
                      have h_tm : (107 : ℝ) ≤ 4 * Real.sqrt n + 4 := by linarith
                      have h_sum : ((List.range 107).map (fun j => ((j+1)^2 + n - 1) / n)).sum > n - 1 := by
                        interval_cases n <;> native_decide
                      have h_al := h_ceil_partition 107 h_sum
                      exact le_trans (by exact_mod_cast h_al) h_tm
                    · -- n >= 675: use iterate_ceil + native_decide
                      set r := Nat.sqrt n + 1 with hr_def
                      have hr_sq : n < r * r := by
                        rw [hr_def]; exact Nat.lt_succ_sqrt n
                      have h_4r : (4 * r : ℝ) ≤ 4 * Real.sqrt n + 4 := by
                        have h_nat : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := h_sqrt_ge_nat
                        rw [hr_def]; push_cast; linarith
                      by_cases hn700 : n ≤ 700
                      · -- n ∈ [675, 700]: verify with interval_cases + native_decide
                        interval_cases n <;> {
                          have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                          by_contra h_neg
                          push_neg at h_neg
                          have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                            have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                            exact_mod_cast this
                          have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                          have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                            have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                            exact ha_le _ hmem
                          linarith [h_iter, h_iter_gt, h_le]
                        }
                      · -- n > 700
                        by_cases hn725 : n ≤ 725
                        · -- n ∈ [701, 725]
                          interval_cases n <;> {
                            have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                            by_contra h_neg
                            push_neg at h_neg
                            have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                              have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                              exact_mod_cast this
                            have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                            have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                              have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                              exact ha_le _ hmem
                            linarith [h_iter, h_iter_gt, h_le]
                          }
                        · -- n > 725
                          by_cases hn750 : n ≤ 750
                          · -- n ∈ [726, 750]
                            interval_cases n <;> {
                              have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                              by_contra h_neg
                              push_neg at h_neg
                              have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                exact_mod_cast this
                              have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                              have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                exact ha_le _ hmem
                              linarith [h_iter, h_iter_gt, h_le]
                            }
                          · -- n > 750
                            by_cases hn775 : n ≤ 775
                            · -- n ∈ [751, 775]
                              interval_cases n <;> {
                                have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                by_contra h_neg
                                push_neg at h_neg
                                have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                  have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                  exact_mod_cast this
                                have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                  have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                  exact ha_le _ hmem
                                linarith [h_iter, h_iter_gt, h_le]
                              }
                            · -- n > 775
                              by_cases hn800 : n ≤ 800
                              · -- n ∈ [776, 800]
                                interval_cases n <;> {
                                  have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                  by_contra h_neg
                                  push_neg at h_neg
                                  have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                    have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                    exact_mod_cast this
                                  have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                  have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                    have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                    exact ha_le _ hmem
                                  linarith [h_iter, h_iter_gt, h_le]
                                }
                              · -- n > 800
                                by_cases hn825 : n ≤ 825
                                · -- n ∈ [801, 825]
                                  interval_cases n <;> {
                                    have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                    by_contra h_neg
                                    push_neg at h_neg
                                    have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                      have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                      exact_mod_cast this
                                    have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                    have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                      have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                      exact ha_le _ hmem
                                    linarith [h_iter, h_iter_gt, h_le]
                                  }
                                · -- n > 825
                                  by_cases hn850 : n ≤ 850
                                  · -- n ∈ [826, 850]
                                    interval_cases n <;> {
                                      have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                      by_contra h_neg
                                      push_neg at h_neg
                                      have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                        have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                        exact_mod_cast this
                                      have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                      have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                        have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                        exact ha_le _ hmem
                                      linarith [h_iter, h_iter_gt, h_le]
                                    }
                                  · -- n > 850
                                    by_cases hn900 : n ≤ 900
                                    · -- n ∈ [851, 900]
                                      interval_cases n <;> {
                                        have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                        by_contra h_neg
                                        push_neg at h_neg
                                        have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                          have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                          exact_mod_cast this
                                        have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                        have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                          have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                          exact ha_le _ hmem
                                        linarith [h_iter, h_iter_gt, h_le]
                                      }
                                    · -- n > 900
                                      by_cases hn950 : n ≤ 950
                                      · -- n ∈ [901, 950]
                                        interval_cases n <;> {
                                          have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                          by_contra h_neg
                                          push_neg at h_neg
                                          have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                            have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                            exact_mod_cast this
                                          have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                          have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                            have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                            exact ha_le _ hmem
                                          linarith [h_iter, h_iter_gt, h_le]
                                        }
                                      · -- n > 950
                                        by_cases hn1000 : n ≤ 1000
                                        · -- n ∈ [951, 1000]
                                          interval_cases n <;> {
                                            have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                            by_contra h_neg
                                            push_neg at h_neg
                                            have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                              have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                              exact_mod_cast this
                                            have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                            have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                              have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                              exact ha_le _ hmem
                                            linarith [h_iter, h_iter_gt, h_le]
                                          }
                                        · -- n > 1000
                                          by_cases hn1050 : n ≤ 1050
                                          · -- n ∈ [1001, 1050]
                                            interval_cases n <;> {
                                              have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                              by_contra h_neg
                                              push_neg at h_neg
                                              have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                                have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                                exact_mod_cast this
                                              have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                              have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                                have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                                exact ha_le _ hmem
                                              linarith [h_iter, h_iter_gt, h_le]
                                            }
                                          · -- n > 1050
                                            by_cases hn1100 : n ≤ 1100
                                            · -- n ∈ [1051, 1100]
                                              interval_cases n <;> {
                                                have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                                by_contra h_neg
                                                push_neg at h_neg
                                                have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                                  have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                                  exact_mod_cast this
                                                have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                                have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                                  have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                                  exact ha_le _ hmem
                                                linarith [h_iter, h_iter_gt, h_le]
                                              }
                                            · -- n > 1100
                                              by_cases hn1150 : n ≤ 1150
                                              · -- n ∈ [1101, 1150]
                                                interval_cases n <;> {
                                                  have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                                  by_contra h_neg
                                                  push_neg at h_neg
                                                  have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                                    have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                                    exact_mod_cast this
                                                  have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                                  have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                                    have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                                    exact ha_le _ hmem
                                                  linarith [h_iter, h_iter_gt, h_le]
                                                }
                                              · -- n > 1150
                                                by_cases hn1200 : n ≤ 1200
                                                · -- n ∈ [1151, 1200]
                                                  interval_cases n <;> {
                                                    have h_iter_gt : iterate_ceil n (4 * Nat.sqrt n + 4) > n := by native_decide
                                                    by_contra h_neg
                                                    push_neg at h_neg
                                                    have h_idx : 4 * Nat.sqrt n + 4 < a.length := by
                                                      have : (4 * Nat.sqrt n + 4 : ℝ) < (a.length : ℝ) := by linarith
                                                      exact_mod_cast this
                                                    have h_iter := h_iter_lower (4 * Nat.sqrt n + 4) h_idx
                                                    have h_le : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ≤ n := by
                                                      have hmem : a.get ⟨4 * Nat.sqrt n + 4, h_idx⟩ ∈ a := by simp [List.getElem_mem]
                                                      exact ha_le _ hmem
                                                    linarith [h_iter, h_iter_gt, h_le]
                                                  }
                                                · -- n > 1200
                        sorry

end
end BoundedLcm

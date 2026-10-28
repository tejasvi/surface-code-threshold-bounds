import Mathlib

/-!
# Clopper–Pearson arithmetic, checked by the kernel

`binomCDF n k p = ∑_{j ≤ k} C(n,j) p^j (1-p)^(n-j)` is the binomial lower tail. For `p = a/b` and `α = c/d`
(natural numbers), `cpCheck n k a b c d` compares the two integers `d ∑_{j ≤ k} C(n,j) a^j (b-a)^(n-j)` and
`c b^n`; `cpCheck_sound` turns a successful check into `binomCDF n k (a/b) ≤ c/d`. The check is a closed Boolean
term, so `decide +kernel` evaluates it in the kernel (GMP arithmetic on literals). Binomial coefficients are computed
as `descFactorial n j / j!`, which unfolds in `j` steps instead of the recursion of `Nat.choose`.
-/

open Finset

namespace QECML

/-- The binomial lower tail `F(k; n, p) = ∑_{j ≤ k} C(n,j) p^j (1-p)^(n-j)`. -/
noncomputable def binomCDF (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- Binomial coefficient through the falling factorial (`j` kernel steps). -/
def chooseF (n j : ℕ) : ℕ := n.descFactorial j / j.factorial

theorem chooseF_eq (n j : ℕ) : chooseF n j = n.choose j :=
  (Nat.choose_eq_descFactorial_div_factorial n j).symm

/-- `cpNum n a b k = ∑_{j ≤ k} C(n,j) a^j (b-a)^(n-j)`, by recursion on `k`. -/
def cpNum (n a b : ℕ) : ℕ → ℕ
  | 0 => chooseF n 0 * a ^ 0 * (b - a) ^ (n - 0)
  | k + 1 => cpNum n a b k + chooseF n (k + 1) * a ^ (k + 1) * (b - a) ^ (n - (k + 1))

theorem cpNum_eq (n a b k : ℕ) :
    cpNum n a b k = ∑ j ∈ range (k + 1), n.choose j * a ^ j * (b - a) ^ (n - j) := by
  induction k with
  | zero => simp [cpNum, chooseF_eq]
  | succ k ih => rw [cpNum, ih, Finset.sum_range_succ _ (k + 1), chooseF_eq]

/-- The integer check for `F(k; n, a/b) ≤ c/d`. -/
def cpCheck (n k a b c d : ℕ) : Bool := Nat.ble (d * cpNum n a b k) (c * b ^ n)

theorem cpCheck_sound {n k a b c d : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : cpCheck n k a b c d = true) : binomCDF n k ((a : ℝ) / b) ≤ (c : ℝ) / d := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hterm : ∀ j ∈ range (k + 1), (n.choose j : ℝ) * ((a : ℝ) / b) ^ j * (1 - (a : ℝ) / b) ^ (n - j) =
      ((n.choose j * a ^ j * (b - a) ^ (n - j) : ℕ) : ℝ) / (b : ℝ) ^ n := by
    intro j hj
    have hjn : j ≤ n := by
      simp only [Finset.mem_range] at hj
      omega
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hab, one_sub_div hbR.ne',
      div_pow, div_pow, show (b : ℝ) ^ n = (b : ℝ) ^ j * (b : ℝ) ^ (n - j) by
        rw [← pow_add, Nat.add_sub_cancel' hjn]]
    field_simp
  rw [binomCDF, Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, ← cpNum_eq,
    div_le_div_iff₀ (by positivity) hdR]
  have h' : ((d * cpNum n a b k : ℕ) : ℝ) ≤ ((c * b ^ n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_ble_eq_true h
  push_cast at h'
  linarith

/-- `binomCDF n k (a/b)` as an integer over `b^n` (for `k ≤ n`, `a ≤ b`, `b > 0`). -/
theorem binomCDF_eq_cpNum {n k a b : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) :
    binomCDF n k ((a : ℝ) / b) = (cpNum n a b k : ℝ) / (b : ℝ) ^ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [binomCDF, cpNum_eq, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by
    simp only [Finset.mem_range] at hj
    omega
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hab, one_sub_div hbR.ne',
    div_pow, div_pow, show (b : ℝ) ^ n = (b : ℝ) ^ j * (b : ℝ) ^ (n - j) by
      rw [← pow_add, Nat.add_sub_cancel' hjn]]
  field_simp

/-- The reverse integer check, for `c/d < F(k; n, a/b)`. -/
def cpCheckGt (n k a b c d : ℕ) : Bool := Nat.ble (c * b ^ n + 1) (d * cpNum n a b k)

theorem cpCheckGt_sound {n k a b c d : ℕ} (hk : k ≤ n) (hab : a ≤ b) (hb : 0 < b) (hd : 0 < d)
    (h : cpCheckGt n k a b c d = true) : (c : ℝ) / d < binomCDF n k ((a : ℝ) / b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [binomCDF_eq_cpNum hk hab hb, div_lt_div_iff₀ hdR (by positivity)]
  have h' : ((c * b ^ n : ℕ) : ℝ) < ((d * cpNum n a b k : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h)
  push_cast at h'
  linarith

end QECML

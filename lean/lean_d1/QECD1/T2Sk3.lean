import QECD1.T2Ends3
import QECD1.TransferEx

/-!
# The 3D T2 skeleton

The 3D analogue of the 2D `S3Geom.T2Sk` (TwoD/T2Count), shaped for the 3D transfer (`transfer3_ex_top`).

* `T2Sk3`: a bottom part (a start block `b0` in the bottom strip, not counted, and a route word `ms0` from `A`), the
  intermediate families (landing root and family skeleton `Skel3`), and a top part `(et, mst, tf)` (`Top3`).
* `exitSk`: the exit cover of a family skeleton, the end of its route.
* `t2TD`: the tail data of the transfer: jumps `jw3`/`jok3`, families `skelEncoding` with exit `exitSk`, tops
  `tw3`/`tok3`.
* `T2Sk3.counted`: the counted blocks (bottom route, family key blocks, top root and top route if the top is a family).
* `jsum3`, `ssum3`, `rlen`: the `ℓ1` lengths of the jumps, of the family spans, and of a route word.
* `T2Sk3.OK ny cE`: the validity used by the count: the bottom part, the tail in the transfer's sense (`TailOKex`,
  boundary plane `y = n_y - 1`), the height of the top part, the metric constraint (X) in block units with per-family
  constant `30` and end constant `cE`, and the counted blocks undeclared and pairwise `D`-separated.
-/

open Finset Classical

namespace QECD1

/-! ### `ℓ1` -/

theorem l1_sub_comm (a b : V3) : l1 (a - b) = l1 (b - a) := by
  simp only [l1, Prod.fst_sub, Prod.snd_sub]
  omega

theorem l1_sub_le (a b c : V3) : l1 (a - c) ≤ l1 (a - b) + l1 (b - c) := by
  simp only [l1, Prod.fst_sub, Prod.snd_sub]
  omega

theorem l1_le_linf (v : V3) : l1 v ≤ 3 * linf v := by
  simp only [l1, linf]
  omega

/-- A block within `D - 1` of another (in `ℓ∞`) is within `3 (D - 1) = 12` in `ℓ1`. -/
theorem l1_le_of_dist3 {a b : V3} (h : dist3 a b ≤ Const.D - 1) : l1 (a - b) ≤ 12 := by
  have h1 := l1_le_linf (a - b)
  have hD : Const.D - 1 = 4 := by decide
  unfold dist3 at h
  omega

/-! ### Route words -/

/-- The `ℓ1` length of a route word: the offsets of its steps and links (a leaf does not move the route). -/
def rlen : List Tok → ℕ
  | [] => 0
  | .step v :: ws => l1 v + rlen ws
  | .link v :: ws => l1 v + rlen ws
  | .leaf _ :: ws => rlen ws
  | .mark :: ws => rlen ws

/-- The end of a route word rises at most its `ℓ1` length. -/
theorem endOf_row_le : ∀ (cur : V3) (ws : List Tok), (endOf cur ws).2.2 ≤ cur.2.2 + rlen ws
  | _, [] => by simp [endOf, rlen]
  | cur, .step v :: ws => by
    have ih := endOf_row_le (cur + v) ws
    have hv : v.2.2 ≤ l1 v := by
      simp only [l1]
      omega
    simp only [endOf, rlen, Prod.snd_add] at ih ⊢
    push_cast
    omega
  | cur, .link v :: ws => by
    have ih := endOf_row_le (cur + v) ws
    have hv : v.2.2 ≤ l1 v := by
      simp only [l1]
      omega
    simp only [endOf, rlen, Prod.snd_add] at ih ⊢
    push_cast
    omega
  | cur, .leaf _ :: ws => by
    have ih := endOf_row_le cur ws
    simpa [endOf, rlen] using ih
  | cur, .mark :: ws => by
    have ih := endOf_row_le cur ws
    simpa [endOf, rlen] using ih

/-! ### Skeletons -/

/-- The exit cover of a family skeleton: the end of its route. -/
def exitSk (k : Skel3) : V3 := endOf k.1 (k.2.2.1 ++ k.2.2.2.2)

/-- The tail data of the 3D T2 count, with the boundary plane `y = Y`. -/
noncomputable def t2TD (Y : ℤ) : TData V3 Skel3 Top3 :=
  TData.mk jw3 jok3 skelEncoding.root exitSk skelEncoding.fok skelEncoding.w tw3 (tok3 Y)

/-- The `ℓ1` lengths of the jumps of a tail after the cover `c`: to each landing root, then to the top root. -/
def jsum3 : V3 → List (V3 × Skel3) → V3 → ℕ
  | c, [], et => l1 (et - c)
  | c, f :: fs, et => l1 (f.1 - c) + jsum3 (exitSk f.2) fs et

/-- The `ℓ1` spans of the families of a tail: from each landing root to the family's exit cover. -/
def ssum3 : List (V3 × Skel3) → ℕ
  | [] => 0
  | f :: fs => l1 (exitSk f.2 - f.1) + ssum3 fs

/-- The cover before family `i` (`0`: the start cover `c0`). -/
def covAt (c0 : V3) (K : ℕ → Skel3) (i : ℕ) : V3 := if i = 0 then c0 else exitSk (K i)

/-- The jumps of a tail of families indexed `1, …, m`, as a sum over the stations. -/
theorem jsum3_range (et : V3) : ∀ (m : ℕ) (R : ℕ → V3) (K : ℕ → Skel3) (c0 : V3),
    jsum3 c0 ((List.range m).map (fun i => (R (i + 1), K (i + 1)))) et =
      ∑ i ∈ range m, l1 (R (i + 1) - covAt c0 K i) + l1 (et - covAt c0 K m)
  | 0, R, K, c0 => by simp [jsum3, covAt]
  | m + 1, R, K, c0 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := jsum3_range et m (fun j => R (j + 1)) (fun j => K (j + 1)) (exitSk (K 1))
    have hc : ∀ i, covAt (exitSk (K 1)) (fun j => K (j + 1)) i = covAt c0 K (i + 1) := by
      intro i
      unfold covAt
      rw [if_neg (by omega : i + 1 ≠ 0)]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl]
      · rw [if_neg hi]
    simp only [hc] at ih
    show l1 (R (0 + 1) - c0) + jsum3 (exitSk (K (0 + 1)))
      ((List.range m).map ((fun i => (R (i + 1), K (i + 1))) ∘ Nat.succ)) et = _
    have he : ((List.range m).map ((fun i => (R (i + 1), K (i + 1))) ∘ Nat.succ)) =
        (List.range m).map (fun i => (R (i + 1 + 1), K (i + 1 + 1))) := rfl
    have h0 : covAt c0 K 0 = c0 := if_pos rfl
    rw [he, ih, Finset.sum_range_succ', h0]
    ring

/-- The spans of a tail of families indexed `1, …, m`, as a sum. -/
theorem ssum3_range : ∀ (m : ℕ) (R : ℕ → V3) (K : ℕ → Skel3),
    ssum3 ((List.range m).map (fun i => (R (i + 1), K (i + 1)))) =
      ∑ i ∈ range m, l1 (exitSk (K (i + 1)) - R (i + 1))
  | 0, R, K => by simp [ssum3]
  | m + 1, R, K => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := ssum3_range m (fun j => R (j + 1)) (fun j => K (j + 1))
    show l1 (exitSk (K (0 + 1)) - R (0 + 1)) +
      ssum3 ((List.range m).map ((fun i => (R (i + 1), K (i + 1))) ∘ Nat.succ)) = _
    have he : ((List.range m).map ((fun i => (R (i + 1), K (i + 1))) ∘ Nat.succ)) =
        (List.range m).map (fun i => (R (i + 1 + 1), K (i + 1 + 1))) := rfl
    rw [he, ih, Finset.sum_range_succ']
    ring

/-- A 3D T2 skeleton. -/
structure T2Sk3 where
  b0 : V3
  ms0 : List Tok
  fams : List (V3 × Skel3)
  top : Top3

namespace T2Sk3

/-- The counted blocks: the bottom route, the families' key blocks, and the top root and top route if the top part
is a family. -/
def counted (sk : T2Sk3) : List V3 :=
  blocksOf sk.b0 sk.ms0 ++ (sk.fams.flatMap (fun f => keyBlocks f.1 f.2.2.2) ++
    (if sk.top.2.2 then sk.top.1 :: blocksOf sk.top.1 sk.top.2.1 else []))

/-- **A valid 3D T2 skeleton** (`n_y` block rows, end constant `cE`). -/
def OK (ny : ℕ) (cE : ℝ) (sk : T2Sk3) : Prop :=
  sk.b0.2.2 ≤ hs3 ∧ route3.Gram 1 sk.ms0 ∧
    (t2TD ((ny : ℤ) - 1)).TailOKex (tok3ex ((ny : ℤ) - 1)) (endOf sk.b0 sk.ms0) sk.fams sk.top ∧
    (ny : ℤ) ≤ (endOf sk.top.1 sk.top.2.1).2.2 + 1 + hs3 + Const.A1 ∧
    (jsum3 (endOf sk.b0 sk.ms0) sk.fams sk.top.1 : ℝ) ≤
      ssum3 sk.fams + rlen sk.ms0 + rlen sk.top.2.1 + 30 * sk.fams.length + cE ∧
    (∀ b ∈ sk.counted, ¬ declared3 ny b) ∧ sk.counted.Pairwise (fun a b => Const.D ≤ dist3 a b)

end T2Sk3

/-! ### Families -/

/-- **Blocks of different families are `D`-separated**: families are unions of clusters. -/
theorem sep_of_families {F L : Finset V3} {Fm Fm' : Finset V3} (hFm : Fm ∈ families3 F L)
    (hFm' : Fm' ∈ families3 F L) (hne : Fm ≠ Fm') {c d : V3} (hc : c ∈ Fm) (hd : d ∈ Fm') :
    Const.D ≤ dist3 c d := by
  by_contra hlt
  obtain ⟨c0, -, hc0⟩ := mem_families3.1 hFm
  obtain ⟨c0', -, hc0'⟩ := mem_families3.1 hFm'
  have hcF : c ∈ F := by
    rw [← hc0] at hc
    exact famF_sub _ _ _ hc
  have hdF : d ∈ F := by
    rw [← hc0'] at hd
    exact famF_sub _ _ _ hd
  have hlink : Linked3 F L c d :=
    ⟨hcF, hdF, Or.inl (Relation.ReflTransGen.single ⟨hcF, hdF, by rw [← a0_succ_eq_D] at hlt; omega⟩)⟩
  have hdc : d ∈ Fm := by
    rw [← famF_eq_of_mem_families3 hFm hc]
    exact mem_famF.2 ⟨hdF, Relation.ReflTransGen.single hlink⟩
  exact hne (families3_eq_of_mem hFm hFm' hdc hd)

end QECD1

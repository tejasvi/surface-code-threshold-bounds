import QEC.Count.ChunksK4
import Mathlib.Tactic.IntervalCases
import QEC.KChecks.A6K2.E0
import QEC.KChecks.A6K2.E1
import QEC.KChecks.A6K2.E2
import QEC.KChecks.A6K2.E3
import QEC.KChecks.A6K2.E4
import QEC.KChecks.A6K2.E5
import QEC.KChecks.A6K2.E6
import QEC.KChecks.A6K2.E7

namespace QECKChecks.A6K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfsp_0 : dfsPreK PA6K2 tA6K2 [0] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_0_0, dfs_0_1, dfs_0_2, dfs_0_3, dfs_0_4, dfs_0_5, dfs_0_6, dfs_0_7]

theorem dfsp_1 : dfsPreK PA6K2 tA6K2 [1] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_1_0, dfs_1_1, dfs_1_2, dfs_1_3, dfs_1_4, dfs_1_5, dfs_1_6, dfs_1_7]

theorem dfsp_2 : dfsPreK PA6K2 tA6K2 [2] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_2_0, dfs_2_1, dfs_2_2, dfs_2_3, dfs_2_4, dfs_2_5, dfs_2_6, dfs_2_7]

theorem dfsp_3 : dfsPreK PA6K2 tA6K2 [3] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_3_0, dfs_3_1, dfs_3_2, dfs_3_3, dfs_3_4, dfs_3_5, dfs_3_6, dfs_3_7]

theorem dfsp_4 : dfsPreK PA6K2 tA6K2 [4] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_4_0, dfs_4_1, dfs_4_2, dfs_4_3, dfs_4_4, dfs_4_5, dfs_4_6, dfs_4_7]

theorem dfsp_5 : dfsPreK PA6K2 tA6K2 [5] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_5_0, dfs_5_1, dfs_5_2, dfs_5_3, dfs_5_4, dfs_5_5, dfs_5_6, dfs_5_7]

theorem dfsp_6 : dfsPreK PA6K2 tA6K2 [6] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_6_0, dfs_6_1, dfs_6_2, dfs_6_3, dfs_6_4, dfs_6_5, dfs_6_6, dfs_6_7]

theorem dfsp_7 : dfsPreK PA6K2 tA6K2 [7] [] = true := by
  apply dfsPreK_split1 (by decide)
  intro j hj
  have hl : (candList PA6K2.n).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_7_0, dfs_7_1, dfs_7_2, dfs_7_3, dfs_7_4, dfs_7_5, dfs_7_6, dfs_7_7]

end QECKChecks.A6K2

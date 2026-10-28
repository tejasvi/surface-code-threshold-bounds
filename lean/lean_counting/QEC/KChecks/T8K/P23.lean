import QEC.Count.ChunksTK
import Mathlib.Tactic.IntervalCases
import QEC.KChecks.T8K.E23_0
import QEC.KChecks.T8K.E23_1
import QEC.KChecks.T8K.E23_2
import QEC.KChecks.T8K.E23_3
import QEC.KChecks.T8K.E23_4
import QEC.KChecks.T8K.E23_5
import QEC.KChecks.T8K.E23_6
import QEC.KChecks.T8K.E23_7
import QEC.KChecks.T8K.E23_8
import QEC.KChecks.T8K.E23_9
import QEC.KChecks.T8K.E23_10
import QEC.KChecks.T8K.E23_11
import QEC.KChecks.T8K.E23_12
import QEC.KChecks.T8K.E23_13
import QEC.KChecks.T8K.E23_14
import QEC.KChecks.T8K.E23_15
import QEC.KChecks.T8K.E23_16
import QEC.KChecks.T8K.E23_17
import QEC.KChecks.T8K.E23_18
import QEC.KChecks.T8K.E23_19
import QEC.KChecks.T8K.E23_20
import QEC.KChecks.T8K.E23_21
import QEC.KChecks.T8K.E23_22
import QEC.KChecks.T8K.E23_23
import QEC.KChecks.T8K.E23_24
import QEC.KChecks.T8K.E23_25
import QEC.KChecks.T8K.E23_26
import QEC.KChecks.T8K.E23_27
import QEC.KChecks.T8K.E23_28
import QEC.KChecks.T8K.E23_29
import QEC.KChecks.T8K.E23_30
import QEC.KChecks.T8K.E23_31
import QEC.KChecks.T8K.E23_32
import QEC.KChecks.T8K.E23_33
import QEC.KChecks.T8K.E23_34
import QEC.KChecks.T8K.E23_35
import QEC.KChecks.T8K.E23_36
import QEC.KChecks.T8K.E23_37
import QEC.KChecks.T8K.E23_38
import QEC.KChecks.T8K.E23_39
import QEC.KChecks.T8K.E23_40
import QEC.KChecks.T8K.E23_41
import QEC.KChecks.T8K.E23_42
import QEC.KChecks.T8K.E23_43
import QEC.KChecks.T8K.E23_44
import QEC.KChecks.T8K.E23_45
import QEC.KChecks.T8K.E23_46
import QEC.KChecks.T8K.E23_47
import QEC.KChecks.T8K.E23_48
import QEC.KChecks.T8K.E23_49
import QEC.KChecks.T8K.E23_50
import QEC.KChecks.T8K.E23_51
import QEC.KChecks.T8K.E23_52
import QEC.KChecks.T8K.E23_53
import QEC.KChecks.T8K.E23_54
import QEC.KChecks.T8K.E23_55
import QEC.KChecks.T8K.E23_56
import QEC.KChecks.T8K.E23_57
import QEC.KChecks.T8K.E23_58
import QEC.KChecks.T8K.E23_59
import QEC.KChecks.T8K.E23_60
import QEC.KChecks.T8K.E23_61
import QEC.KChecks.T8K.E23_62
import QEC.KChecks.T8K.E23_63

namespace QECKChecks.T8K

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfsp_23_0_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_0_0, dfs_23_0_0_1, dfs_23_0_0_2, dfs_23_0_0_3, dfs_23_0_0_4, dfs_23_0_0_5, dfs_23_0_0_6, dfs_23_0_0_7]

theorem dfsp_23_0_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_1_0, dfs_23_0_1_1, dfs_23_0_1_2, dfs_23_0_1_3, dfs_23_0_1_4, dfs_23_0_1_5, dfs_23_0_1_6, dfs_23_0_1_7]

theorem dfsp_23_0_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_2_0, dfs_23_0_2_1, dfs_23_0_2_2, dfs_23_0_2_3, dfs_23_0_2_4, dfs_23_0_2_5, dfs_23_0_2_6, dfs_23_0_2_7]

theorem dfsp_23_0_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_3_0, dfs_23_0_3_1, dfs_23_0_3_2, dfs_23_0_3_3, dfs_23_0_3_4, dfs_23_0_3_5, dfs_23_0_3_6, dfs_23_0_3_7]

theorem dfsp_23_0_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_4_0, dfs_23_0_4_1, dfs_23_0_4_2, dfs_23_0_4_3, dfs_23_0_4_4, dfs_23_0_4_5, dfs_23_0_4_6, dfs_23_0_4_7]

theorem dfsp_23_0_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_5_0, dfs_23_0_5_1, dfs_23_0_5_2, dfs_23_0_5_3, dfs_23_0_5_4, dfs_23_0_5_5, dfs_23_0_5_6, dfs_23_0_5_7]

theorem dfsp_23_0_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_6_0, dfs_23_0_6_1, dfs_23_0_6_2, dfs_23_0_6_3, dfs_23_0_6_4, dfs_23_0_6_5, dfs_23_0_6_6, dfs_23_0_6_7]

theorem dfsp_23_0_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [0, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_0_7_0, dfs_23_0_7_1, dfs_23_0_7_2, dfs_23_0_7_3, dfs_23_0_7_4, dfs_23_0_7_5, dfs_23_0_7_6, dfs_23_0_7_7]

theorem dfsp_23_1_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_0_0, dfs_23_1_0_1, dfs_23_1_0_2, dfs_23_1_0_3, dfs_23_1_0_4, dfs_23_1_0_5, dfs_23_1_0_6, dfs_23_1_0_7]

theorem dfsp_23_1_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_1_0, dfs_23_1_1_1, dfs_23_1_1_2, dfs_23_1_1_3, dfs_23_1_1_4, dfs_23_1_1_5, dfs_23_1_1_6, dfs_23_1_1_7]

theorem dfsp_23_1_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_2_0, dfs_23_1_2_1, dfs_23_1_2_2, dfs_23_1_2_3, dfs_23_1_2_4, dfs_23_1_2_5, dfs_23_1_2_6, dfs_23_1_2_7]

theorem dfsp_23_1_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_3_0, dfs_23_1_3_1, dfs_23_1_3_2, dfs_23_1_3_3, dfs_23_1_3_4, dfs_23_1_3_5, dfs_23_1_3_6, dfs_23_1_3_7]

theorem dfsp_23_1_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_4_0, dfs_23_1_4_1, dfs_23_1_4_2, dfs_23_1_4_3, dfs_23_1_4_4, dfs_23_1_4_5, dfs_23_1_4_6, dfs_23_1_4_7]

theorem dfsp_23_1_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_5_0, dfs_23_1_5_1, dfs_23_1_5_2, dfs_23_1_5_3, dfs_23_1_5_4, dfs_23_1_5_5, dfs_23_1_5_6, dfs_23_1_5_7]

theorem dfsp_23_1_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_6_0, dfs_23_1_6_1, dfs_23_1_6_2, dfs_23_1_6_3, dfs_23_1_6_4, dfs_23_1_6_5, dfs_23_1_6_6, dfs_23_1_6_7]

theorem dfsp_23_1_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [1, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_1_7_0, dfs_23_1_7_1, dfs_23_1_7_2, dfs_23_1_7_3, dfs_23_1_7_4, dfs_23_1_7_5, dfs_23_1_7_6, dfs_23_1_7_7]

theorem dfsp_23_2_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_0_0, dfs_23_2_0_1, dfs_23_2_0_2, dfs_23_2_0_3, dfs_23_2_0_4, dfs_23_2_0_5, dfs_23_2_0_6, dfs_23_2_0_7]

theorem dfsp_23_2_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_1_0, dfs_23_2_1_1, dfs_23_2_1_2, dfs_23_2_1_3, dfs_23_2_1_4, dfs_23_2_1_5, dfs_23_2_1_6, dfs_23_2_1_7]

theorem dfsp_23_2_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_2_0, dfs_23_2_2_1, dfs_23_2_2_2, dfs_23_2_2_3, dfs_23_2_2_4, dfs_23_2_2_5, dfs_23_2_2_6, dfs_23_2_2_7]

theorem dfsp_23_2_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_3_0, dfs_23_2_3_1, dfs_23_2_3_2, dfs_23_2_3_3, dfs_23_2_3_4, dfs_23_2_3_5, dfs_23_2_3_6, dfs_23_2_3_7]

theorem dfsp_23_2_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_4_0, dfs_23_2_4_1, dfs_23_2_4_2, dfs_23_2_4_3, dfs_23_2_4_4, dfs_23_2_4_5, dfs_23_2_4_6, dfs_23_2_4_7]

theorem dfsp_23_2_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_5_0, dfs_23_2_5_1, dfs_23_2_5_2, dfs_23_2_5_3, dfs_23_2_5_4, dfs_23_2_5_5, dfs_23_2_5_6, dfs_23_2_5_7]

theorem dfsp_23_2_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_6_0, dfs_23_2_6_1, dfs_23_2_6_2, dfs_23_2_6_3, dfs_23_2_6_4, dfs_23_2_6_5, dfs_23_2_6_6, dfs_23_2_6_7]

theorem dfsp_23_2_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [2, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_2_7_0, dfs_23_2_7_1, dfs_23_2_7_2, dfs_23_2_7_3, dfs_23_2_7_4, dfs_23_2_7_5, dfs_23_2_7_6, dfs_23_2_7_7]

theorem dfsp_23_3_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_0_0, dfs_23_3_0_1, dfs_23_3_0_2, dfs_23_3_0_3, dfs_23_3_0_4, dfs_23_3_0_5, dfs_23_3_0_6, dfs_23_3_0_7]

theorem dfsp_23_3_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_1_0, dfs_23_3_1_1, dfs_23_3_1_2, dfs_23_3_1_3, dfs_23_3_1_4, dfs_23_3_1_5, dfs_23_3_1_6, dfs_23_3_1_7]

theorem dfsp_23_3_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_2_0, dfs_23_3_2_1, dfs_23_3_2_2, dfs_23_3_2_3, dfs_23_3_2_4, dfs_23_3_2_5, dfs_23_3_2_6, dfs_23_3_2_7]

theorem dfsp_23_3_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_3_0, dfs_23_3_3_1, dfs_23_3_3_2, dfs_23_3_3_3, dfs_23_3_3_4, dfs_23_3_3_5, dfs_23_3_3_6, dfs_23_3_3_7]

theorem dfsp_23_3_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_4_0, dfs_23_3_4_1, dfs_23_3_4_2, dfs_23_3_4_3, dfs_23_3_4_4, dfs_23_3_4_5, dfs_23_3_4_6, dfs_23_3_4_7]

theorem dfsp_23_3_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_5_0, dfs_23_3_5_1, dfs_23_3_5_2, dfs_23_3_5_3, dfs_23_3_5_4, dfs_23_3_5_5, dfs_23_3_5_6, dfs_23_3_5_7]

theorem dfsp_23_3_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_6_0, dfs_23_3_6_1, dfs_23_3_6_2, dfs_23_3_6_3, dfs_23_3_6_4, dfs_23_3_6_5, dfs_23_3_6_6, dfs_23_3_6_7]

theorem dfsp_23_3_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [3, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_3_7_0, dfs_23_3_7_1, dfs_23_3_7_2, dfs_23_3_7_3, dfs_23_3_7_4, dfs_23_3_7_5, dfs_23_3_7_6, dfs_23_3_7_7]

theorem dfsp_23_4_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_0_0, dfs_23_4_0_1, dfs_23_4_0_2, dfs_23_4_0_3, dfs_23_4_0_4, dfs_23_4_0_5, dfs_23_4_0_6, dfs_23_4_0_7]

theorem dfsp_23_4_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_1_0, dfs_23_4_1_1, dfs_23_4_1_2, dfs_23_4_1_3, dfs_23_4_1_4, dfs_23_4_1_5, dfs_23_4_1_6, dfs_23_4_1_7]

theorem dfsp_23_4_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_2_0, dfs_23_4_2_1, dfs_23_4_2_2, dfs_23_4_2_3, dfs_23_4_2_4, dfs_23_4_2_5, dfs_23_4_2_6, dfs_23_4_2_7]

theorem dfsp_23_4_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_3_0, dfs_23_4_3_1, dfs_23_4_3_2, dfs_23_4_3_3, dfs_23_4_3_4, dfs_23_4_3_5, dfs_23_4_3_6, dfs_23_4_3_7]

theorem dfsp_23_4_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_4_0, dfs_23_4_4_1, dfs_23_4_4_2, dfs_23_4_4_3, dfs_23_4_4_4, dfs_23_4_4_5, dfs_23_4_4_6, dfs_23_4_4_7]

theorem dfsp_23_4_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_5_0, dfs_23_4_5_1, dfs_23_4_5_2, dfs_23_4_5_3, dfs_23_4_5_4, dfs_23_4_5_5, dfs_23_4_5_6, dfs_23_4_5_7]

theorem dfsp_23_4_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_6_0, dfs_23_4_6_1, dfs_23_4_6_2, dfs_23_4_6_3, dfs_23_4_6_4, dfs_23_4_6_5, dfs_23_4_6_6, dfs_23_4_6_7]

theorem dfsp_23_4_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [4, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_4_7_0, dfs_23_4_7_1, dfs_23_4_7_2, dfs_23_4_7_3, dfs_23_4_7_4, dfs_23_4_7_5, dfs_23_4_7_6, dfs_23_4_7_7]

theorem dfsp_23_5_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_0_0, dfs_23_5_0_1, dfs_23_5_0_2, dfs_23_5_0_3, dfs_23_5_0_4, dfs_23_5_0_5, dfs_23_5_0_6, dfs_23_5_0_7]

theorem dfsp_23_5_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_1_0, dfs_23_5_1_1, dfs_23_5_1_2, dfs_23_5_1_3, dfs_23_5_1_4, dfs_23_5_1_5, dfs_23_5_1_6, dfs_23_5_1_7]

theorem dfsp_23_5_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_2_0, dfs_23_5_2_1, dfs_23_5_2_2, dfs_23_5_2_3, dfs_23_5_2_4, dfs_23_5_2_5, dfs_23_5_2_6, dfs_23_5_2_7]

theorem dfsp_23_5_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_3_0, dfs_23_5_3_1, dfs_23_5_3_2, dfs_23_5_3_3, dfs_23_5_3_4, dfs_23_5_3_5, dfs_23_5_3_6, dfs_23_5_3_7]

theorem dfsp_23_5_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_4_0, dfs_23_5_4_1, dfs_23_5_4_2, dfs_23_5_4_3, dfs_23_5_4_4, dfs_23_5_4_5, dfs_23_5_4_6, dfs_23_5_4_7]

theorem dfsp_23_5_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_5_0, dfs_23_5_5_1, dfs_23_5_5_2, dfs_23_5_5_3, dfs_23_5_5_4, dfs_23_5_5_5, dfs_23_5_5_6, dfs_23_5_5_7]

theorem dfsp_23_5_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_6_0, dfs_23_5_6_1, dfs_23_5_6_2, dfs_23_5_6_3, dfs_23_5_6_4, dfs_23_5_6_5, dfs_23_5_6_6, dfs_23_5_6_7]

theorem dfsp_23_5_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [5, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_5_7_0, dfs_23_5_7_1, dfs_23_5_7_2, dfs_23_5_7_3, dfs_23_5_7_4, dfs_23_5_7_5, dfs_23_5_7_6, dfs_23_5_7_7]

theorem dfsp_23_6_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_0_0, dfs_23_6_0_1, dfs_23_6_0_2, dfs_23_6_0_3, dfs_23_6_0_4, dfs_23_6_0_5, dfs_23_6_0_6, dfs_23_6_0_7]

theorem dfsp_23_6_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_1_0, dfs_23_6_1_1, dfs_23_6_1_2, dfs_23_6_1_3, dfs_23_6_1_4, dfs_23_6_1_5, dfs_23_6_1_6, dfs_23_6_1_7]

theorem dfsp_23_6_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_2_0, dfs_23_6_2_1, dfs_23_6_2_2, dfs_23_6_2_3, dfs_23_6_2_4, dfs_23_6_2_5, dfs_23_6_2_6, dfs_23_6_2_7]

theorem dfsp_23_6_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_3_0, dfs_23_6_3_1, dfs_23_6_3_2, dfs_23_6_3_3, dfs_23_6_3_4, dfs_23_6_3_5, dfs_23_6_3_6, dfs_23_6_3_7]

theorem dfsp_23_6_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_4_0, dfs_23_6_4_1, dfs_23_6_4_2, dfs_23_6_4_3, dfs_23_6_4_4, dfs_23_6_4_5, dfs_23_6_4_6, dfs_23_6_4_7]

theorem dfsp_23_6_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_5_0, dfs_23_6_5_1, dfs_23_6_5_2, dfs_23_6_5_3, dfs_23_6_5_4, dfs_23_6_5_5, dfs_23_6_5_6, dfs_23_6_5_7]

theorem dfsp_23_6_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_6_0, dfs_23_6_6_1, dfs_23_6_6_2, dfs_23_6_6_3, dfs_23_6_6_4, dfs_23_6_6_5, dfs_23_6_6_6, dfs_23_6_6_7]

theorem dfsp_23_6_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [6, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_6_7_0, dfs_23_6_7_1, dfs_23_6_7_2, dfs_23_6_7_3, dfs_23_6_7_4, dfs_23_6_7_5, dfs_23_6_7_6, dfs_23_6_7_7]

theorem dfsp_23_7_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 0] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_0_0, dfs_23_7_0_1, dfs_23_7_0_2, dfs_23_7_0_3, dfs_23_7_0_4, dfs_23_7_0_5, dfs_23_7_0_6, dfs_23_7_0_7]

theorem dfsp_23_7_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 1] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_1_0, dfs_23_7_1_1, dfs_23_7_1_2, dfs_23_7_1_3, dfs_23_7_1_4, dfs_23_7_1_5, dfs_23_7_1_6, dfs_23_7_1_7]

theorem dfsp_23_7_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 2] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_2_0, dfs_23_7_2_1, dfs_23_7_2_2, dfs_23_7_2_3, dfs_23_7_2_4, dfs_23_7_2_5, dfs_23_7_2_6, dfs_23_7_2_7]

theorem dfsp_23_7_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 3] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_3_0, dfs_23_7_3_1, dfs_23_7_3_2, dfs_23_7_3_3, dfs_23_7_3_4, dfs_23_7_3_5, dfs_23_7_3_6, dfs_23_7_3_7]

theorem dfsp_23_7_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 4] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_4_0, dfs_23_7_4_1, dfs_23_7_4_2, dfs_23_7_4_3, dfs_23_7_4_4, dfs_23_7_4_5, dfs_23_7_4_6, dfs_23_7_4_7]

theorem dfsp_23_7_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 5] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_5_0, dfs_23_7_5_1, dfs_23_7_5_2, dfs_23_7_5_3, dfs_23_7_5_4, dfs_23_7_5_5, dfs_23_7_5_6, dfs_23_7_5_7]

theorem dfsp_23_7_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 6] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_6_0, dfs_23_7_6_1, dfs_23_7_6_2, dfs_23_7_6_3, dfs_23_7_6_4, dfs_23_7_6_5, dfs_23_7_6_6, dfs_23_7_6_7]

theorem dfsp_23_7_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) [7, 7] [] = true := by
  apply dfsPreTK_split1 (by decide)
  intro j hj
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hj
  interval_cases j
  exacts [dfs_23_7_7_0, dfs_23_7_7_1, dfs_23_7_7_2, dfs_23_7_7_3, dfs_23_7_7_4, dfs_23_7_7_5, dfs_23_7_7_6, dfs_23_7_7_7]

theorem dfsoff_23 : dfsTK PT8K tNT8K.find tBT8K.find (offT PT8K 23) PT8K.K [] = true := by
  apply dfsTK_of_prefixes (D := 2) (by decide)
  intro js hlen hjs
  have hl : (candList 2).length = 8 := by decide
  rw [hl] at hjs
  match js, hlen with
  | [j1, j2], _ =>
    have hj1 : j1 < 8 := hjs j1 (by simp)
    have hj2 : j2 < 8 := hjs j2 (by simp)
    interval_cases j1 <;> interval_cases j2
    exacts [dfsp_23_0_0, dfsp_23_0_1, dfsp_23_0_2, dfsp_23_0_3, dfsp_23_0_4, dfsp_23_0_5, dfsp_23_0_6, dfsp_23_0_7, dfsp_23_1_0, dfsp_23_1_1, dfsp_23_1_2, dfsp_23_1_3, dfsp_23_1_4, dfsp_23_1_5, dfsp_23_1_6, dfsp_23_1_7, dfsp_23_2_0, dfsp_23_2_1, dfsp_23_2_2, dfsp_23_2_3, dfsp_23_2_4, dfsp_23_2_5, dfsp_23_2_6, dfsp_23_2_7, dfsp_23_3_0, dfsp_23_3_1, dfsp_23_3_2, dfsp_23_3_3, dfsp_23_3_4, dfsp_23_3_5, dfsp_23_3_6, dfsp_23_3_7, dfsp_23_4_0, dfsp_23_4_1, dfsp_23_4_2, dfsp_23_4_3, dfsp_23_4_4, dfsp_23_4_5, dfsp_23_4_6, dfsp_23_4_7, dfsp_23_5_0, dfsp_23_5_1, dfsp_23_5_2, dfsp_23_5_3, dfsp_23_5_4, dfsp_23_5_5, dfsp_23_5_6, dfsp_23_5_7, dfsp_23_6_0, dfsp_23_6_1, dfsp_23_6_2, dfsp_23_6_3, dfsp_23_6_4, dfsp_23_6_5, dfsp_23_6_6, dfsp_23_6_7, dfsp_23_7_0, dfsp_23_7_1, dfsp_23_7_2, dfsp_23_7_3, dfsp_23_7_4, dfsp_23_7_5, dfsp_23_7_6, dfsp_23_7_7]

end QECKChecks.T8K

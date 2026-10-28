import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6208 = true := by
  decide +kernel

theorem tot6208 : totK PA10K2 A10K2.t6208 = [0, 0, 112574319960, 1249414440998, 2291457692530, 913103296909, 77820506896, 0, 0, 0] := by
  decide +kernel

theorem rows6209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6209 = true := by
  decide +kernel

theorem tot6209 : totK PA10K2 A10K2.t6209 = [0, 0, 314979364907, 1249116253426, 1835406566879, 1067233609728, 213638840706, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6210 = true := by
  decide +kernel

theorem tot6210 : totK PA10K2 A10K2.t6210 = [0, 0, 523813060156, 1901066942411, 1946260968480, 466434881406, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows6211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6211 = true := by
  decide +kernel

theorem tot6211 : totK PA10K2 A10K2.t6211 = [0, 0, 0, 647967257171, 2025309265518, 1583243882440, 382211736569, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15356 = true := by
  decide +kernel

theorem tot15356 : totK PD2M8K2 D2M8K2.t15356 = [0, 0, 170801653863, 463943362256, 240372894610, 11957301992, 0, 0] := by
  decide +kernel

theorem rows15357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15357 = true := by
  decide +kernel

theorem tot15357 : totK PD2M8K2 D2M8K2.t15357 = [0, 0, 0, 297124090116, 497631136061, 104963179480, 2909416399, 0] := by
  decide +kernel

theorem rows15358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15358 = true := by
  decide +kernel

theorem tot15358 : totK PD2M8K2 D2M8K2.t15358 = [0, 0, 65235372122, 307192103540, 395765711927, 97171763526, 2250452236, 0] := by
  decide +kernel

theorem rows15359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15359 = true := by
  decide +kernel

theorem tot15359 : totK PD2M8K2 D2M8K2.t15359 = [0, 0, 182309491354, 454010501051, 268892623556, 27925896374, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

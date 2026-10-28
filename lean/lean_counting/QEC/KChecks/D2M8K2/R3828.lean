import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15312 = true := by
  decide +kernel

theorem tot15312 : totK PD2M8K2 D2M8K2.t15312 = [0, 0, 0, 285755794116, 514360675387, 96246355708, 1369150432, 0] := by
  decide +kernel

theorem rows15313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15313 = true := by
  decide +kernel

theorem tot15313 : totK PD2M8K2 D2M8K2.t15313 = [0, 0, 173835435312, 431057081775, 296058005076, 37171378062, 0, 0] := by
  decide +kernel

theorem rows15314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15314 = true := by
  decide +kernel

theorem tot15314 : totK PD2M8K2 D2M8K2.t15314 = [0, 0, 173977021590, 475667735893, 261101257738, 11890343009, 0, 0] := by
  decide +kernel

theorem rows15315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15315 = true := by
  decide +kernel

theorem tot15315 : totK PD2M8K2 D2M8K2.t15315 = [0, 0, 0, 292859804649, 514829545850, 107910282233, 1402015981, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

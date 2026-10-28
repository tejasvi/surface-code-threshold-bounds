import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15088 = true := by
  decide +kernel

theorem tot15088 : totK PD2M8K2 D2M8K2.t15088 = [0, 0, 192083430212, 468732373589, 206053503098, 12206147664, 0, 0] := by
  decide +kernel

theorem rows15089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15089 = true := by
  decide +kernel

theorem tot15089 : totK PD2M8K2 D2M8K2.t15089 = [0, 0, 0, 294146523243, 461153856174, 103005868141, 1369150432, 0] := by
  decide +kernel

theorem rows15090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15090 = true := by
  decide +kernel

theorem tot15090 : totK PD2M8K2 D2M8K2.t15090 = [0, 0, 87493257244, 397020760731, 349971210980, 41032153799, 0, 0] := by
  decide +kernel

theorem rows15091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15091 = true := by
  decide +kernel

theorem tot15091 : totK PD2M8K2 D2M8K2.t15091 = [0, 0, 188301698084, 478203653903, 213906324661, 9961945378, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

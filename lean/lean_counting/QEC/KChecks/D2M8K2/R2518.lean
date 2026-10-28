import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10072 = true := by
  decide +kernel

theorem tot10072 : totK PD2M8K2 D2M8K2.t10072 = [0, 87730519020, 331566205985, 374216637418, 103794878873, 3884009855, 0, 0] := by
  decide +kernel

theorem rows10073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10073 = true := by
  decide +kernel

theorem tot10073 : totK PD2M8K2 D2M8K2.t10073 = [0, 170487518989, 439148199301, 275115182156, 29279764938, 0, 0, 0] := by
  decide +kernel

theorem rows10074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10074 = true := by
  decide +kernel

theorem tot10074 : totK PD2M8K2 D2M8K2.t10074 = [0, 147558936287, 449910899386, 290854039739, 23516156445, 0, 0, 0] := by
  decide +kernel

theorem rows10075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10075 = true := by
  decide +kernel

theorem tot10075 : totK PD2M8K2 D2M8K2.t10075 = [0, 0, 219320373578, 494207348293, 171456241020, 4967996017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

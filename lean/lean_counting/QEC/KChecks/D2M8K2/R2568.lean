import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10272 = true := by
  decide +kernel

theorem tot10272 : totK PD2M8K2 D2M8K2.t10272 = [0, 165803353843, 443651150382, 289622340488, 30360088343, 0, 0, 0] := by
  decide +kernel

theorem rows10273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10273 = true := by
  decide +kernel

theorem tot10273 : totK PD2M8K2 D2M8K2.t10273 = [0, 104296678417, 428855944024, 346664107195, 30494068909, 0, 0, 0] := by
  decide +kernel

theorem rows10274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10274 = true := by
  decide +kernel

theorem tot10274 : totK PD2M8K2 D2M8K2.t10274 = [0, 0, 213982224519, 488323442014, 187082772155, 9668735432, 0, 0] := by
  decide +kernel

theorem rows10275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10275 = true := by
  decide +kernel

theorem tot10275 : totK PD2M8K2 D2M8K2.t10275 = [0, 84422589187, 317809617239, 376156123602, 103497459925, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

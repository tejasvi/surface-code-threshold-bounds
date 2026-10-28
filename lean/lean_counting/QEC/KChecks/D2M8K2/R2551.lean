import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10204 = true := by
  decide +kernel

theorem tot10204 : totK PD2M8K2 D2M8K2.t10204 = [0, 191561361150, 435989729807, 232201191137, 24226997045, 0, 0, 0] := by
  decide +kernel

theorem rows10205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10205 = true := by
  decide +kernel

theorem tot10205 : totK PD2M8K2 D2M8K2.t10205 = [0, 90840904916, 408792010691, 344173005716, 41601810977, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10206 = true := by
  decide +kernel

theorem tot10206 : totK PD2M8K2 D2M8K2.t10206 = [0, 0, 298733595782, 509304569665, 86509640691, 0, 0, 0] := by
  decide +kernel

theorem rows10207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10207 = true := by
  decide +kernel

theorem tot10207 : totK PD2M8K2 D2M8K2.t10207 = [0, 157174987332, 383048840227, 272312323010, 87274068195, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

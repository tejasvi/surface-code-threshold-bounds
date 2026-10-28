import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15804 = true := by
  decide +kernel

theorem tot15804 : totK PD2M8K2 D2M8K2.t15804 = [0, 0, 188167277134, 481247613395, 203434553237, 6688676231, 0, 0] := by
  decide +kernel

theorem rows15805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15805 = true := by
  decide +kernel

theorem tot15805 : totK PD2M8K2 D2M8K2.t15805 = [0, 0, 179437644002, 488579864510, 221630438162, 10177609099, 0, 0] := by
  decide +kernel

theorem rows15806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15806 = true := by
  decide +kernel

theorem tot15806 : totK PD2M8K2 D2M8K2.t15806 = [0, 0, 190405003710, 469708850456, 226519495028, 12679943201, 0, 0] := by
  decide +kernel

theorem rows15807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15807 = true := by
  decide +kernel

theorem tot15807 : totK PD2M8K2 D2M8K2.t15807 = [0, 0, 193195353208, 464121549856, 208376887196, 12595094539, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

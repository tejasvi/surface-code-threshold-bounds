import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15572 = true := by
  decide +kernel

theorem tot15572 : totK PD2M8K2 D2M8K2.t15572 = [0, 0, 0, 168577859636, 491988838557, 210495766404, 4763482009, 0] := by
  decide +kernel

theorem rows15573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15573 = true := by
  decide +kernel

theorem tot15573 : totK PD2M8K2 D2M8K2.t15573 = [0, 200591725335, 483284037543, 204558565943, 9852138406, 7130640995, 3381127452, 0] := by
  decide +kernel

theorem rows15574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15574 = true := by
  decide +kernel

theorem tot15574 : totK PD2M8K2 D2M8K2.t15574 = [0, 196839912873, 451842926156, 200179335533, 10736670142, 0, 0, 0] := by
  decide +kernel

theorem rows15575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15575 = true := by
  decide +kernel

theorem tot15575 : totK PD2M8K2 D2M8K2.t15575 = [0, 15744875771, 298455187462, 476496361023, 104368530078, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

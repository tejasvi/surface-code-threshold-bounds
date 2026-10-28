import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3492 = true := by
  decide +kernel

theorem tot3492 : totK PD2M8K2 D2M8K2.t3492 = [0, 57837989788, 324101081717, 410725120926, 77622788002, 1206465782, 0, 0] := by
  decide +kernel

theorem rows3493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3493 = true := by
  decide +kernel

theorem tot3493 : totK PD2M8K2 D2M8K2.t3493 = [0, 92812290212, 388432862056, 366615414201, 41085085270, 0, 0, 0] := by
  decide +kernel

theorem rows3494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3494 = true := by
  decide +kernel

theorem tot3494 : totK PD2M8K2 D2M8K2.t3494 = [0, 158481523791, 461286902968, 274750169786, 19986494744, 0, 0, 0] := by
  decide +kernel

theorem rows3495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3495 = true := by
  decide +kernel

theorem tot3495 : totK PD2M8K2 D2M8K2.t3495 = [0, 204418746067, 479510136332, 215287709535, 14127514595, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

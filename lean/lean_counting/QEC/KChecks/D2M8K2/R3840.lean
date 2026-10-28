import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15360 = true := by
  decide +kernel

theorem tot15360 : totK PD2M8K2 D2M8K2.t15360 = [0, 0, 170874428049, 467191705247, 245076006918, 9856487800, 0, 0] := by
  decide +kernel

theorem rows15361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15361 = true := by
  decide +kernel

theorem tot15361 : totK PD2M8K2 D2M8K2.t15361 = [0, 0, 0, 273670220984, 480203398522, 128269028515, 4031931762, 0] := by
  decide +kernel

theorem rows15362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15362 = true := by
  decide +kernel

theorem tot15362 : totK PD2M8K2 D2M8K2.t15362 = [0, 0, 108958476720, 351333292741, 345756368126, 75532539051, 1186940923, 0] := by
  decide +kernel

theorem rows15363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15363 = true := by
  decide +kernel

theorem tot15363 : totK PD2M8K2 D2M8K2.t15363 = [0, 0, 168090022094, 439117540473, 275492850612, 28775531976, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

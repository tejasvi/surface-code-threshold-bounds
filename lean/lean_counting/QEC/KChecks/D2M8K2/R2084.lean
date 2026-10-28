import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8336 = true := by
  decide +kernel

theorem tot8336 : totK PD2M8K2 D2M8K2.t8336 = [0, 157929339591, 477432946834, 235598346094, 12492161858, 0, 0, 0] := by
  decide +kernel

theorem rows8337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8337 = true := by
  decide +kernel

theorem tot8337 : totK PD2M8K2 D2M8K2.t8337 = [0, 0, 300713551859, 463099199354, 78734161071, 1138244013, 0, 0] := by
  decide +kernel

theorem rows8338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8338 = true := by
  decide +kernel

theorem tot8338 : totK PD2M8K2 D2M8K2.t8338 = [0, 156985484761, 443772586829, 286577994714, 29596842348, 0, 0, 0] := by
  decide +kernel

theorem rows8339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8339 = true := by
  decide +kernel

theorem tot8339 : totK PD2M8K2 D2M8K2.t8339 = [0, 171920367210, 480454544258, 231863425217, 15709862891, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

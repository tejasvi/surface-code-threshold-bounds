import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8372 = true := by
  decide +kernel

theorem tot8372 : totK PD2M8K2 D2M8K2.t8372 = [0, 153284384506, 448350483356, 294205621739, 28326782098, 0, 0, 0] := by
  decide +kernel

theorem rows8373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8373 = true := by
  decide +kernel

theorem tot8373 : totK PD2M8K2 D2M8K2.t8373 = [0, 173192491800, 449483341521, 252214404859, 20388719335, 0, 0, 0] := by
  decide +kernel

theorem rows8374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8374 = true := by
  decide +kernel

theorem tot8374 : totK PD2M8K2 D2M8K2.t8374 = [0, 172693091781, 441470644839, 263763976339, 26574644986, 0, 0, 0] := by
  decide +kernel

theorem rows8375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8375 = true := by
  decide +kernel

theorem tot8375 : totK PD2M8K2 D2M8K2.t8375 = [0, 123772380721, 422558364873, 310189797976, 24952311847, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

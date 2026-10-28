import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1280 = true := by
  decide +kernel

theorem tot1280 : totK PD2M8K2 D2M8K2.t1280 = [164815754859, 457651104004, 258893965625, 15244595069, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1281 = true := by
  decide +kernel

theorem tot1281 : totK PD2M8K2 D2M8K2.t1281 = [0, 276144410091, 505956162827, 111821952425, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows1282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1282 = true := by
  decide +kernel

theorem tot1282 : totK PD2M8K2 D2M8K2.t1282 = [91209042872, 380888744160, 388077611396, 52158660815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1283 = true := by
  decide +kernel

theorem tot1283 : totK PD2M8K2 D2M8K2.t1283 = [194146963409, 463877391546, 242328332653, 18979867856, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

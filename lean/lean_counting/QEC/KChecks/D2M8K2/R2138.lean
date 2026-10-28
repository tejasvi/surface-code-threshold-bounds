import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8552 = true := by
  decide +kernel

theorem tot8552 : totK PD2M8K2 D2M8K2.t8552 = [0, 172088500870, 467681799178, 234398971423, 13681267370, 0, 0, 0] := by
  decide +kernel

theorem rows8553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8553 = true := by
  decide +kernel

theorem tot8553 : totK PD2M8K2 D2M8K2.t8553 = [0, 0, 253976772247, 487178912952, 134861327522, 2305904642, 0, 0] := by
  decide +kernel

theorem rows8554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8554 = true := by
  decide +kernel

theorem tot8554 : totK PD2M8K2 D2M8K2.t8554 = [0, 66236035334, 272475580845, 358341845989, 136775290001, 10710292732, 0, 0] := by
  decide +kernel

theorem rows8555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8555 = true := by
  decide +kernel

theorem tot8555 : totK PD2M8K2 D2M8K2.t8555 = [0, 175123299584, 480046925935, 244290729440, 12206498855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

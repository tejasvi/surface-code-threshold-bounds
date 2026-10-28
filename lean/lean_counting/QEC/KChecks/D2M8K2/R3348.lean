import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13392 = true := by
  decide +kernel

theorem tot13392 : totK PD2M8K2 D2M8K2.t13392 = [0, 0, 14646759531, 302676495250, 465318397414, 92081855252, 1369150432, 0] := by
  decide +kernel

theorem rows13393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13393 = true := by
  decide +kernel

theorem tot13393 : totK PD2M8K2 D2M8K2.t13393 = [0, 0, 87164153352, 383647335993, 385960296279, 38407318539, 0, 0] := by
  decide +kernel

theorem rows13394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13394 = true := by
  decide +kernel

theorem tot13394 : totK PD2M8K2 D2M8K2.t13394 = [0, 0, 159018323688, 451220663610, 265874598375, 19729573353, 0, 0] := by
  decide +kernel

theorem rows13395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13395 = true := by
  decide +kernel

theorem tot13395 : totK PD2M8K2 D2M8K2.t13395 = [0, 0, 162024977004, 457297393707, 246913485511, 14120804275, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

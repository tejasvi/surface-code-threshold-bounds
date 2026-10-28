import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13496 = true := by
  decide +kernel

theorem tot13496 : totK PD2M8K2 D2M8K2.t13496 = [0, 0, 0, 194722993121, 477512303721, 204951922863, 12264952070, 0] := by
  decide +kernel

theorem rows13497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13497 = true := by
  decide +kernel

theorem tot13497 : totK PD2M8K2 D2M8K2.t13497 = [0, 0, 0, 207768962199, 470515479373, 184436911116, 10871000096, 0] := by
  decide +kernel

theorem rows13498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13498 = true := by
  decide +kernel

theorem tot13498 : totK PD2M8K2 D2M8K2.t13498 = [0, 0, 0, 194288407466, 472950868017, 206398337426, 12337737162, 0] := by
  decide +kernel

theorem rows13499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13499 = true := by
  decide +kernel

theorem tot13499 : totK PD2M8K2 D2M8K2.t13499 = [0, 0, 0, 217543995333, 467367846608, 185171302098, 14411189607, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

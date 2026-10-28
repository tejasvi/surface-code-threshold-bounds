import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13604 = true := by
  decide +kernel

theorem tot13604 : totK PD2M8K2 D2M8K2.t13604 = [0, 156142379044, 455592576668, 276812749891, 23212435192, 0, 0, 0] := by
  decide +kernel

theorem rows13605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13605 = true := by
  decide +kernel

theorem tot13605 : totK PD2M8K2 D2M8K2.t13605 = [0, 174220141959, 459332954884, 262039862964, 19332052856, 0, 0, 0] := by
  decide +kernel

theorem rows13606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13606 = true := by
  decide +kernel

theorem tot13606 : totK PD2M8K2 D2M8K2.t13606 = [204823963468, 479935031595, 201064252634, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13607 = true := by
  decide +kernel

theorem tot13607 : totK PD2M8K2 D2M8K2.t13607 = [193049400465, 467619962963, 219472154770, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13476 = true := by
  decide +kernel

theorem tot13476 : totK PD2M8K2 D2M8K2.t13476 = [0, 0, 0, 170239908620, 462902978718, 225075273252, 11933388171, 0] := by
  decide +kernel

theorem rows13477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13477 = true := by
  decide +kernel

theorem tot13477 : totK PD2M8K2 D2M8K2.t13477 = [0, 0, 83397781031, 337332973458, 375613642867, 96908363328, 1409560813, 0] := by
  decide +kernel

theorem rows13478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13478 = true := by
  decide +kernel

theorem tot13478 : totK PD2M8K2 D2M8K2.t13478 = [0, 0, 177714048602, 448745187525, 259070837462, 22670117867, 0, 0] := by
  decide +kernel

theorem rows13479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13479 = true := by
  decide +kernel

theorem tot13479 : totK PD2M8K2 D2M8K2.t13479 = [0, 0, 155475717698, 448468530252, 267347028532, 16517396802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

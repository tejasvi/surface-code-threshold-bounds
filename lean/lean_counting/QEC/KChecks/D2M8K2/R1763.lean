import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7052 = true := by
  decide +kernel

theorem tot7052 : totK PD2M8K2 D2M8K2.t7052 = [0, 0, 282318078594, 509816232301, 112242325600, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7053 = true := by
  decide +kernel

theorem tot7053 : totK PD2M8K2 D2M8K2.t7053 = [0, 103589792006, 410295697706, 366787498816, 39253483030, 0, 0, 0] := by
  decide +kernel

theorem rows7054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7054 = true := by
  decide +kernel

theorem tot7054 : totK PD2M8K2 D2M8K2.t7054 = [0, 179193041211, 445881152878, 252002301544, 24921714522, 0, 0, 0] := by
  decide +kernel

theorem rows7055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7055 = true := by
  decide +kernel

theorem tot7055 : totK PD2M8K2 D2M8K2.t7055 = [0, 138396455363, 441412090051, 293407405843, 25055868302, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

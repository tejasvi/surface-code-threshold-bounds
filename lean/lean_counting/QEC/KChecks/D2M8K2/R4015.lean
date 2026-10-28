import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16060 = true := by
  decide +kernel

theorem tot16060 : totK PD2M8K2 D2M8K2.t16060 = [0, 11978940098, 300636417029, 480576160254, 105218993923, 1369150432, 0, 0] := by
  decide +kernel

theorem rows16061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16061 = true := by
  decide +kernel

theorem tot16061 : totK PD2M8K2 D2M8K2.t16061 = [0, 87188918593, 370684286625, 405112020896, 49487474156, 0, 0, 0] := by
  decide +kernel

theorem rows16062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16062 = true := by
  decide +kernel

theorem tot16062 : totK PD2M8K2 D2M8K2.t16062 = [0, 160623582072, 467605154078, 265234769710, 20016893592, 0, 0, 0] := by
  decide +kernel

theorem rows16063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16063 = true := by
  decide +kernel

theorem tot16063 : totK PD2M8K2 D2M8K2.t16063 = [0, 163570145806, 449399131453, 250947441130, 17768898690, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13376 = true := by
  decide +kernel

theorem tot13376 : totK PD2M8K2 D2M8K2.t13376 = [0, 0, 170888882450, 473816922933, 219321508165, 10926248329, 0, 0] := by
  decide +kernel

theorem rows13377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13377 = true := by
  decide +kernel

theorem tot13377 : totK PD2M8K2 D2M8K2.t13377 = [0, 0, 153585196779, 463336327628, 240055196388, 13884149399, 0, 0] := by
  decide +kernel

theorem rows13378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13378 = true := by
  decide +kernel

theorem tot13378 : totK PD2M8K2 D2M8K2.t13378 = [0, 0, 0, 304931438025, 455596283630, 82101469442, 1138244013, 0] := by
  decide +kernel

theorem rows13379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13379 = true := by
  decide +kernel

theorem tot13379 : totK PD2M8K2 D2M8K2.t13379 = [0, 0, 180027324132, 447071718027, 258824606784, 25650616412, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

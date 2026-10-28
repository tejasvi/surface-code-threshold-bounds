import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8860 = true := by
  decide +kernel

theorem tot8860 : totK PD2M8K2 D2M8K2.t8860 = [0, 196451849293, 489025397345, 217071991629, 10480478597, 0, 0, 0] := by
  decide +kernel

theorem rows8861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8861 = true := by
  decide +kernel

theorem tot8861 : totK PD2M8K2 D2M8K2.t8861 = [0, 190972729590, 464965342024, 216817249645, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows8862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8862 = true := by
  decide +kernel

theorem tot8862 : totK PD2M8K2 D2M8K2.t8862 = [0, 192646945150, 485353524693, 215620789141, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows8863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8863 = true := by
  decide +kernel

theorem tot8863 : totK PD2M8K2 D2M8K2.t8863 = [0, 162230890645, 449069432841, 236496968667, 15723602574, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

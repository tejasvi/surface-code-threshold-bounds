import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3000 = true := by
  decide +kernel

theorem tot3000 : totK PD2M8K2 D2M8K2.t3000 = [0, 0, 259080446718, 495012462818, 149934814591, 8417083954, 0, 0] := by
  decide +kernel

theorem rows3001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3001 = true := by
  decide +kernel

theorem tot3001 : totK PD2M8K2 D2M8K2.t3001 = [0, 90400450959, 332428888816, 394280443483, 97985509485, 3455941720, 0, 0] := by
  decide +kernel

theorem rows3002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3002 = true := by
  decide +kernel

theorem tot3002 : totK PD2M8K2 D2M8K2.t3002 = [0, 203838036895, 474905598040, 216580957561, 15668555021, 0, 0, 0] := by
  decide +kernel

theorem rows3003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3003 = true := by
  decide +kernel

theorem tot3003 : totK PD2M8K2 D2M8K2.t3003 = [0, 52150595342, 355922971619, 442078403942, 72979508051, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

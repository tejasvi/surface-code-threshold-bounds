import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2284 = true := by
  decide +kernel

theorem tot2284 : totK PD2M8K2 D2M8K2.t2284 = [0, 161065426867, 396187450496, 266318937081, 77573725882, 3884009855, 0, 0] := by
  decide +kernel

theorem rows2285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2285 = true := by
  decide +kernel

theorem tot2285 : totK PD2M8K2 D2M8K2.t2285 = [0, 173778624724, 449447718056, 254649380861, 20253093187, 0, 0, 0] := by
  decide +kernel

theorem rows2286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2286 = true := by
  decide +kernel

theorem tot2286 : totK PD2M8K2 D2M8K2.t2286 = [0, 92937627352, 358167354786, 374852990265, 76348868925, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2287 = true := by
  decide +kernel

theorem tot2287 : totK PD2M8K2 D2M8K2.t2287 = [0, 0, 245462888158, 489363414826, 151876878579, 3699256714, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

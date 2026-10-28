import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15372 = true := by
  decide +kernel

theorem tot15372 : totK PD2M8K2 D2M8K2.t15372 = [0, 0, 280672974906, 507561130506, 103762506598, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15373 = true := by
  decide +kernel

theorem tot15373 : totK PD2M8K2 D2M8K2.t15373 = [0, 183106467492, 450499519678, 275569291993, 32080152999, 0, 0, 0] := by
  decide +kernel

theorem rows15374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15374 = true := by
  decide +kernel

theorem tot15374 : totK PD2M8K2 D2M8K2.t15374 = [0, 171714449031, 452735442611, 245735205944, 16804527463, 0, 0, 0] := by
  decide +kernel

theorem rows15375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15375 = true := by
  decide +kernel

theorem tot15375 : totK PD2M8K2 D2M8K2.t15375 = [0, 74127421197, 305865927801, 367205372057, 155055423806, 17183021007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15304 = true := by
  decide +kernel

theorem tot15304 : totK PD2M8K2 D2M8K2.t15304 = [0, 0, 68124773346, 360065378346, 384481648288, 64238349504, 1198073392, 0] := by
  decide +kernel

theorem rows15305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15305 = true := by
  decide +kernel

theorem tot15305 : totK PD2M8K2 D2M8K2.t15305 = [0, 0, 54502128254, 356956375862, 450296668998, 46232771304, 0, 0] := by
  decide +kernel

theorem rows15306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15306 = true := by
  decide +kernel

theorem tot15306 : totK PD2M8K2 D2M8K2.t15306 = [0, 0, 190573285956, 478315492681, 227076610639, 9951496920, 0, 0] := by
  decide +kernel

theorem rows15307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15307 = true := by
  decide +kernel

theorem tot15307 : totK PD2M8K2 D2M8K2.t15307 = [0, 0, 177826880184, 449590649106, 244048420992, 18185084111, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10420 = true := by
  decide +kernel

theorem tot10420 : totK PD2M8K2 D2M8K2.t10420 = [0, 0, 211109869378, 463659020242, 237141589660, 22915662035, 0, 0] := by
  decide +kernel

theorem rows10421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10421 = true := by
  decide +kernel

theorem tot10421 : totK PD2M8K2 D2M8K2.t10421 = [0, 0, 172395509173, 472898519404, 234933468336, 13574322929, 0, 0] := by
  decide +kernel

theorem rows10422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10422 = true := by
  decide +kernel

theorem tot10422 : totK PD2M8K2 D2M8K2.t10422 = [0, 0, 0, 266298207943, 465944105069, 167622616334, 15073499398, 0] := by
  decide +kernel

theorem rows10423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10423 = true := by
  decide +kernel

theorem tot10423 : totK PD2M8K2 D2M8K2.t10423 = [0, 0, 0, 215504237222, 490506658121, 178686789511, 5430665091, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3220 = true := by
  decide +kernel

theorem tot3220 : totK PD2M8K2 D2M8K2.t3220 = [0, 287865783501, 503149046549, 99793138679, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows3221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3221 = true := by
  decide +kernel

theorem tot3221 : totK PD2M8K2 D2M8K2.t3221 = [0, 248611546808, 501117451553, 142888009686, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows3222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3222 = true := by
  decide +kernel

theorem tot3222 : totK PD2M8K2 D2M8K2.t3222 = [0, 157164615605, 447676091500, 241318904882, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows3223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3223 = true := by
  decide +kernel

theorem tot3223 : totK PD2M8K2 D2M8K2.t3223 = [0, 131759210762, 431405882820, 280648664386, 23539890184, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

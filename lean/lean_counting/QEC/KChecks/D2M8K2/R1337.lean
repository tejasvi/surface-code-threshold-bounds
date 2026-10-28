import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5348 = true := by
  decide +kernel

theorem tot5348 : totK PD2M8K2 D2M8K2.t5348 = [0, 198242656869, 481643521728, 226297990731, 12163480350, 0, 0, 0] := by
  decide +kernel

theorem rows5349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5349 = true := by
  decide +kernel

theorem tot5349 : totK PD2M8K2 D2M8K2.t5349 = [0, 44748213827, 284927712957, 386912330629, 178120707701, 21376388639, 0, 0] := by
  decide +kernel

theorem rows5350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5350 = true := by
  decide +kernel

theorem tot5350 : totK PD2M8K2 D2M8K2.t5350 = [0, 0, 198905483768, 478328192769, 209412093392, 7936160546, 0, 0] := by
  decide +kernel

theorem rows5351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5351 = true := by
  decide +kernel

theorem tot5351 : totK PD2M8K2 D2M8K2.t5351 = [0, 83079777321, 258930900455, 377691053446, 173513981730, 8204069046, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

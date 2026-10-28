import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12064 = true := by
  decide +kernel

theorem tot12064 : totK PD2M8K2 D2M8K2.t12064 = [0, 94308289763, 307064722793, 370704753448, 141725246817, 8863302705, 0, 0] := by
  decide +kernel

theorem rows12065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12065 = true := by
  decide +kernel

theorem tot12065 : totK PD2M8K2 D2M8K2.t12065 = [0, 173147181944, 450959831248, 264712684232, 20800437533, 0, 0, 0] := by
  decide +kernel

theorem rows12066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12066 = true := by
  decide +kernel

theorem tot12066 : totK PD2M8K2 D2M8K2.t12066 = [0, 174865245605, 471594061348, 247967658740, 15389727966, 0, 0, 0] := by
  decide +kernel

theorem rows12067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12067 = true := by
  decide +kernel

theorem tot12067 : totK PD2M8K2 D2M8K2.t12067 = [0, 0, 176197074360, 444579349080, 256539290669, 25307930630, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

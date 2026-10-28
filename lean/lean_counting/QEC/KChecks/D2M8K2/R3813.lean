import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15252 = true := by
  decide +kernel

theorem tot15252 : totK PD2M8K2 D2M8K2.t15252 = [0, 0, 0, 238372013593, 498623802670, 135468923998, 5272504570, 0] := by
  decide +kernel

theorem rows15253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15253 = true := by
  decide +kernel

theorem tot15253 : totK PD2M8K2 D2M8K2.t15253 = [0, 0, 0, 189615625849, 485976521981, 191309192725, 10059231755, 0] := by
  decide +kernel

theorem rows15254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15254 = true := by
  decide +kernel

theorem tot15254 : totK PD2M8K2 D2M8K2.t15254 = [0, 0, 0, 220767714153, 500726541238, 144167084001, 5304976740, 0] := by
  decide +kernel

theorem rows15255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15255 = true := by
  decide +kernel

theorem tot15255 : totK PD2M8K2 D2M8K2.t15255 = [0, 0, 0, 203809974622, 477966228305, 182177285842, 10059780603, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

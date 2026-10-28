import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3260 = true := by
  decide +kernel

theorem tot3260 : totK PD2M8K2 D2M8K2.t3260 = [0, 174663122262, 473169371674, 246935006007, 16215220509, 0, 0, 0] := by
  decide +kernel

theorem rows3261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3261 = true := by
  decide +kernel

theorem tot3261 : totK PD2M8K2 D2M8K2.t3261 = [0, 173505143798, 455860800622, 265981466706, 25483962521, 0, 0, 0] := by
  decide +kernel

theorem rows3262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3262 = true := by
  decide +kernel

theorem tot3262 : totK PD2M8K2 D2M8K2.t3262 = [0, 88735855083, 358333197647, 385564581082, 66727051042, 1075657031, 0, 0] := by
  decide +kernel

theorem rows3263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3263 = true := by
  decide +kernel

theorem tot3263 : totK PD2M8K2 D2M8K2.t3263 = [0, 71145646338, 309466683166, 391589179372, 103501964149, 3804183361, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

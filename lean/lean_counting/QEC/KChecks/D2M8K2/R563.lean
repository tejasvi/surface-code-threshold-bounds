import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2252 = true := by
  decide +kernel

theorem tot2252 : totK PD2M8K2 D2M8K2.t2252 = [0, 187456878315, 468502787320, 241758716108, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows2253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2253 = true := by
  decide +kernel

theorem tot2253 : totK PD2M8K2 D2M8K2.t2253 = [0, 56111990362, 348412490580, 417873824897, 79421518537, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2254 = true := by
  decide +kernel

theorem tot2254 : totK PD2M8K2 D2M8K2.t2254 = [0, 0, 275461375631, 516912278948, 113529659906, 1069412848, 0, 0] := by
  decide +kernel

theorem rows2255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2255 = true := by
  decide +kernel

theorem tot2255 : totK PD2M8K2 D2M8K2.t2255 = [0, 0, 193231325402, 470068637742, 202734840129, 12554737991, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

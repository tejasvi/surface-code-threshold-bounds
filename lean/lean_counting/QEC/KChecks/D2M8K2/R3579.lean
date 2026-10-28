import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14316 = true := by
  decide +kernel

theorem tot14316 : totK PD2M8K2 D2M8K2.t14316 = [0, 0, 209118521248, 495182481717, 183875531852, 5463989431, 0, 0] := by
  decide +kernel

theorem rows14317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14317 = true := by
  decide +kernel

theorem tot14317 : totK PD2M8K2 D2M8K2.t14317 = [0, 0, 168794621508, 451804657162, 223383173464, 13356154502, 0, 0] := by
  decide +kernel

theorem rows14318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14318 = true := by
  decide +kernel

theorem tot14318 : totK PD2M8K2 D2M8K2.t14318 = [0, 0, 234412025321, 476117545607, 158004969107, 8907672167, 0, 0] := by
  decide +kernel

theorem rows14319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14319 = true := by
  decide +kernel

theorem tot14319 : totK PD2M8K2 D2M8K2.t14319 = [0, 0, 226535545036, 499386430348, 153725938317, 2447184110, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

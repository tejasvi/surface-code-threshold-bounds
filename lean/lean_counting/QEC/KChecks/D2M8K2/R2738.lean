import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10952 = true := by
  decide +kernel

theorem tot10952 : totK PD2M8K2 D2M8K2.t10952 = [0, 198402952960, 469528266652, 190753902568, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows10953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10953 = true := by
  decide +kernel

theorem tot10953 : totK PD2M8K2 D2M8K2.t10953 = [155852417729, 435055802415, 277790683249, 37805495475, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10954 = true := by
  decide +kernel

theorem tot10954 : totK PD2M8K2 D2M8K2.t10954 = [171962494088, 446691132718, 254574810979, 18510921421, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10955 = true := by
  decide +kernel

theorem tot10955 : totK PD2M8K2 D2M8K2.t10955 = [91210733126, 361160920572, 369453760403, 71887800207, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

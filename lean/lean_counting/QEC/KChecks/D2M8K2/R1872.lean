import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7488 = true := by
  decide +kernel

theorem tot7488 : totK PD2M8K2 D2M8K2.t7488 = [0, 166673409451, 445114180417, 242931398278, 18185084111, 0, 0, 0] := by
  decide +kernel

theorem rows7489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7489 = true := by
  decide +kernel

theorem tot7489 : totK PD2M8K2 D2M8K2.t7489 = [0, 0, 311266767478, 492657743810, 90734800666, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7490 = true := by
  decide +kernel

theorem tot7490 : totK PD2M8K2 D2M8K2.t7490 = [0, 87414637357, 314085092725, 376152452800, 104413276791, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7491 = true := by
  decide +kernel

theorem tot7491 : totK PD2M8K2 D2M8K2.t7491 = [0, 156910275507, 451222315849, 274810267670, 26052973445, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

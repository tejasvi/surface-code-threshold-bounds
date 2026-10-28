import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7480 = true := by
  decide +kernel

theorem tot7480 : totK PD2M8K2 D2M8K2.t7480 = [0, 165379046579, 467753152584, 264654053946, 21417489890, 0, 0, 0] := by
  decide +kernel

theorem rows7481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7481 = true := by
  decide +kernel

theorem tot7481 : totK PD2M8K2 D2M8K2.t7481 = [0, 173057898740, 459801420885, 245006899237, 15117888121, 0, 0, 0] := by
  decide +kernel

theorem rows7482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7482 = true := by
  decide +kernel

theorem tot7482 : totK PD2M8K2 D2M8K2.t7482 = [0, 0, 269464174023, 516997740235, 116057673031, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7483 = true := by
  decide +kernel

theorem tot7483 : totK PD2M8K2 D2M8K2.t7483 = [0, 33264521362, 214523882292, 429939694165, 183037703826, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

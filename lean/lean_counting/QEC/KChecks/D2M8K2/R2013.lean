import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8052 = true := by
  decide +kernel

theorem tot8052 : totK PD2M8K2 D2M8K2.t8052 = [0, 70176937105, 333117258073, 413403640395, 88744307574, 1164319620, 0, 0] := by
  decide +kernel

theorem rows8053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8053 = true := by
  decide +kernel

theorem tot8053 : totK PD2M8K2 D2M8K2.t8053 = [0, 0, 196900603871, 466512929652, 190438349761, 11885407614, 0, 0] := by
  decide +kernel

theorem rows8054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8054 = true := by
  decide +kernel

theorem tot8054 : totK PD2M8K2 D2M8K2.t8054 = [0, 141287649189, 430237459541, 301833873501, 38317747806, 0, 0, 0] := by
  decide +kernel

theorem rows8055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8055 = true := by
  decide +kernel

theorem tot8055 : totK PD2M8K2 D2M8K2.t8055 = [0, 191082733567, 447846311398, 222549321143, 16877408448, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

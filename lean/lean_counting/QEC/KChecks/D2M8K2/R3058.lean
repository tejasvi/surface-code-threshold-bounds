import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12232 = true := by
  decide +kernel

theorem tot12232 : totK PD2M8K2 D2M8K2.t12232 = [0, 0, 214161140167, 496956536076, 161134156417, 5218872685, 0, 0] := by
  decide +kernel

theorem rows12233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12233 = true := by
  decide +kernel

theorem tot12233 : totK PD2M8K2 D2M8K2.t12233 = [0, 160122128994, 440492108246, 274713255627, 36212938272, 0, 0, 0] := by
  decide +kernel

theorem rows12234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12234 = true := by
  decide +kernel

theorem tot12234 : totK PD2M8K2 D2M8K2.t12234 = [0, 171981095862, 442965720028, 259637966509, 23017804517, 0, 0, 0] := by
  decide +kernel

theorem rows12235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12235 = true := by
  decide +kernel

theorem tot12235 : totK PD2M8K2 D2M8K2.t12235 = [0, 91681601894, 417371570558, 367850465519, 30519236082, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

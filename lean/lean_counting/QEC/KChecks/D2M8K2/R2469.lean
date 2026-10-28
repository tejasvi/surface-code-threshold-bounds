import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9876 = true := by
  decide +kernel

theorem tot9876 : totK PD2M8K2 D2M8K2.t9876 = [0, 0, 180029056163, 461328383060, 210383660738, 12554737991, 0, 0] := by
  decide +kernel

theorem rows9877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9877 = true := by
  decide +kernel

theorem tot9877 : totK PD2M8K2 D2M8K2.t9877 = [0, 0, 197002129417, 468838783227, 204615297481, 12421902774, 0, 0] := by
  decide +kernel

theorem rows9878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9878 = true := by
  decide +kernel

theorem tot9878 : totK PD2M8K2 D2M8K2.t9878 = [0, 0, 36114127710, 351891563802, 389752820473, 65020973887, 1138244013, 0] := by
  decide +kernel

theorem rows9879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9879 = true := by
  decide +kernel

theorem tot9879 : totK PD2M8K2 D2M8K2.t9879 = [0, 0, 92246714946, 419283586406, 354599348129, 34162062976, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

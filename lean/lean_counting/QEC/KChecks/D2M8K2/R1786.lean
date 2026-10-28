import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7144 = true := by
  decide +kernel

theorem tot7144 : totK PD2M8K2 D2M8K2.t7144 = [0, 176623553792, 447881528881, 239915002400, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows7145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7145 = true := by
  decide +kernel

theorem tot7145 : totK PD2M8K2 D2M8K2.t7145 = [0, 151309709628, 442913877831, 275753833498, 23671965746, 0, 0, 0] := by
  decide +kernel

theorem rows7146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7146 = true := by
  decide +kernel

theorem tot7146 : totK PD2M8K2 D2M8K2.t7146 = [0, 0, 271701959141, 505342205044, 110345744759, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7147 = true := by
  decide +kernel

theorem tot7147 : totK PD2M8K2 D2M8K2.t7147 = [0, 158665127972, 431388479070, 308268311553, 32213166842, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

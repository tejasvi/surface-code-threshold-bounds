import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7012 = true := by
  decide +kernel

theorem tot7012 : totK PD2M8K2 D2M8K2.t7012 = [0, 181956760477, 450080122468, 223801192713, 13046285521, 0, 0, 0] := by
  decide +kernel

theorem rows7013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7013 = true := by
  decide +kernel

theorem tot7013 : totK PD2M8K2 D2M8K2.t7013 = [0, 89561782785, 391524797687, 350168837928, 60317342531, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7014 = true := by
  decide +kernel

theorem tot7014 : totK PD2M8K2 D2M8K2.t7014 = [0, 0, 300133918177, 512840864336, 71717656014, 0, 0, 0] := by
  decide +kernel

theorem rows7015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7015 = true := by
  decide +kernel

theorem tot7015 : totK PD2M8K2 D2M8K2.t7015 = [0, 180575128572, 449452336503, 272273166872, 30372071830, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

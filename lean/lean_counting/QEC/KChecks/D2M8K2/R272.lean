import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1088 = true := by
  decide +kernel

theorem tot1088 : totK PD2M8K2 D2M8K2.t1088 = [0, 0, 167746668289, 477989108395, 211449971287, 8566329634, 0, 0] := by
  decide +kernel

theorem rows1089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1089 = true := by
  decide +kernel

theorem tot1089 : totK PD2M8K2 D2M8K2.t1089 = [0, 0, 186598448223, 458579274194, 212965133104, 14752871206, 0, 0] := by
  decide +kernel

theorem rows1090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1090 = true := by
  decide +kernel

theorem tot1090 : totK PD2M8K2 D2M8K2.t1090 = [0, 0, 285634315131, 497979713339, 113317451159, 1369587937, 0, 0] := by
  decide +kernel

theorem rows1091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1091 = true := by
  decide +kernel

theorem tot1091 : totK PD2M8K2 D2M8K2.t1091 = [0, 180782889120, 429565551694, 287137692121, 34334497799, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

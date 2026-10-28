import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8408 = true := by
  decide +kernel

theorem tot8408 : totK PD2M8K2 D2M8K2.t8408 = [0, 0, 0, 287043711157, 453773232303, 106708616372, 1369150432, 0] := by
  decide +kernel

theorem rows8409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8409 = true := by
  decide +kernel

theorem tot8409 : totK PD2M8K2 D2M8K2.t8409 = [0, 0, 190466417523, 449968941054, 221436834334, 16834144157, 0, 0] := by
  decide +kernel

theorem rows8410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8410 = true := by
  decide +kernel

theorem tot8410 : totK PD2M8K2 D2M8K2.t8410 = [0, 0, 194925898266, 463806456804, 186263515958, 12082697338, 0, 0] := by
  decide +kernel

theorem rows8411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8411 = true := by
  decide +kernel

theorem tot8411 : totK PD2M8K2 D2M8K2.t8411 = [0, 0, 200576970927, 484434750232, 191330528035, 10059231755, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

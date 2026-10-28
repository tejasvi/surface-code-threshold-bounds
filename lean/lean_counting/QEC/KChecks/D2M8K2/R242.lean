import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t968 = true := by
  decide +kernel

theorem tot968 : totK PD2M8K2 D2M8K2.t968 = [0, 200176748136, 494434143033, 185627066481, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t969 = true := by
  decide +kernel

theorem tot969 : totK PD2M8K2 D2M8K2.t969 = [84547450418, 310652255881, 387506763701, 98575430131, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t970 = true := by
  decide +kernel

theorem tot970 : totK PD2M8K2 D2M8K2.t970 = [174719665843, 456869049013, 251850429519, 22307090722, 0, 0, 0, 0] := by
  decide +kernel

theorem rows971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t971 = true := by
  decide +kernel

theorem tot971 : totK PD2M8K2 D2M8K2.t971 = [162653102018, 464916679889, 249175064666, 17024329063, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

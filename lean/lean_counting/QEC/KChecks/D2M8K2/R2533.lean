import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10132 = true := by
  decide +kernel

theorem tot10132 : totK PD2M8K2 D2M8K2.t10132 = [0, 177683357892, 457841356529, 254850705679, 24235297590, 0, 0, 0] := by
  decide +kernel

theorem rows10133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10133 = true := by
  decide +kernel

theorem tot10133 : totK PD2M8K2 D2M8K2.t10133 = [0, 142124878872, 444395508554, 286936551252, 24558024261, 0, 0, 0] := by
  decide +kernel

theorem rows10134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10134 = true := by
  decide +kernel

theorem tot10134 : totK PD2M8K2 D2M8K2.t10134 = [0, 0, 260739016802, 485758562125, 142063266618, 8423393484, 0, 0] := by
  decide +kernel

theorem rows10135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10135 = true := by
  decide +kernel

theorem tot10135 : totK PD2M8K2 D2M8K2.t10135 = [0, 149123110795, 365436428530, 298939787872, 80818905398, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

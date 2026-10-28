import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4736 = true := by
  decide +kernel

theorem tot4736 : totK PD2M8K2 D2M8K2.t4736 = [0, 0, 221483486646, 487210945602, 164148784347, 3686482003, 0, 0] := by
  decide +kernel

theorem rows4737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4737 = true := by
  decide +kernel

theorem tot4737 : totK PD2M8K2 D2M8K2.t4737 = [0, 0, 186197240858, 468228693217, 222084784522, 16848974375, 0, 0] := by
  decide +kernel

theorem rows4738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4738 = true := by
  decide +kernel

theorem tot4738 : totK PD2M8K2 D2M8K2.t4738 = [0, 0, 203492527956, 493044852453, 177333064073, 3705122438, 0, 0] := by
  decide +kernel

theorem rows4739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4739 = true := by
  decide +kernel

theorem tot4739 : totK PD2M8K2 D2M8K2.t4739 = [0, 0, 168251807888, 461180458806, 226264838353, 13497510966, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6108 = true := by
  decide +kernel

theorem tot6108 : totK PD2M8K2 D2M8K2.t6108 = [0, 0, 187861506506, 456026566797, 213445150700, 17041558502, 0, 0] := by
  decide +kernel

theorem rows6109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6109 = true := by
  decide +kernel

theorem tot6109 : totK PD2M8K2 D2M8K2.t6109 = [0, 0, 279837996062, 507430121908, 126510644969, 1369820453, 0, 0] := by
  decide +kernel

theorem rows6110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6110 = true := by
  decide +kernel

theorem tot6110 : totK PD2M8K2 D2M8K2.t6110 = [0, 0, 164124336530, 441928141017, 268641732152, 27027668444, 0, 0] := by
  decide +kernel

theorem rows6111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6111 = true := by
  decide +kernel

theorem tot6111 : totK PD2M8K2 D2M8K2.t6111 = [0, 0, 210042025068, 483880318765, 203701814431, 6553345076, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

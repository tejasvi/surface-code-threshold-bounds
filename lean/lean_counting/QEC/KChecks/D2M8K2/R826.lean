import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3304 = true := by
  decide +kernel

theorem tot3304 : totK PD2M8K2 D2M8K2.t3304 = [0, 0, 274276298198, 503447513853, 134079635461, 4143089693, 0, 0] := by
  decide +kernel

theorem rows3305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3305 = true := by
  decide +kernel

theorem tot3305 : totK PD2M8K2 D2M8K2.t3305 = [0, 142183269315, 366695400380, 314476188671, 71965030565, 1227322468, 0, 0] := by
  decide +kernel

theorem rows3306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3306 = true := by
  decide +kernel

theorem tot3306 : totK PD2M8K2 D2M8K2.t3306 = [0, 162675059333, 439043593619, 287511993330, 30585669717, 0, 0, 0] := by
  decide +kernel

theorem rows3307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3307 = true := by
  decide +kernel

theorem tot3307 : totK PD2M8K2 D2M8K2.t3307 = [0, 121485128459, 436819699671, 310365194235, 27235081983, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

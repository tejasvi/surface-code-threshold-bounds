import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7132 = true := by
  decide +kernel

theorem tot7132 : totK PD2M8K2 D2M8K2.t7132 = [0, 0, 225084890425, 492912088134, 168556045093, 5011483316, 0, 0] := by
  decide +kernel

theorem rows7133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7133 = true := by
  decide +kernel

theorem tot7133 : totK PD2M8K2 D2M8K2.t7133 = [0, 0, 192379387888, 488379749672, 204172134078, 10374152040, 0, 0] := by
  decide +kernel

theorem rows7134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7134 = true := by
  decide +kernel

theorem tot7134 : totK PD2M8K2 D2M8K2.t7134 = [0, 0, 206424412197, 472836424120, 185723330040, 9713690252, 0, 0] := by
  decide +kernel

theorem rows7135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7135 = true := by
  decide +kernel

theorem tot7135 : totK PD2M8K2 D2M8K2.t7135 = [0, 0, 107937530609, 436516170786, 298474499767, 22693907379, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

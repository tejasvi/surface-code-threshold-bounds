import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6372 = true := by
  decide +kernel

theorem tot6372 : totK PD2M8K2 D2M8K2.t6372 = [0, 0, 232979123672, 481409793849, 176645140031, 10159529672, 0, 0] := by
  decide +kernel

theorem rows6373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6373 = true := by
  decide +kernel

theorem tot6373 : totK PD2M8K2 D2M8K2.t6373 = [0, 0, 183483842348, 481767471875, 190332112607, 9561023729, 0, 0] := by
  decide +kernel

theorem rows6374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6374 = true := by
  decide +kernel

theorem tot6374 : totK PD2M8K2 D2M8K2.t6374 = [0, 0, 136522137244, 436724431703, 258175229955, 19824781048, 0, 0] := by
  decide +kernel

theorem rows6375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6375 = true := by
  decide +kernel

theorem tot6375 : totK PD2M8K2 D2M8K2.t6375 = [0, 0, 0, 298949651693, 455221508842, 81188747156, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

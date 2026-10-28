import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1080 = true := by
  decide +kernel

theorem tot1080 : totK PD2M8K2 D2M8K2.t1080 = [0, 0, 334617683203, 510440548622, 71850392304, 0, 0, 0] := by
  decide +kernel

theorem rows1081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1081 = true := by
  decide +kernel

theorem tot1081 : totK PD2M8K2 D2M8K2.t1081 = [0, 0, 176576008792, 475164053256, 207284745336, 10738855752, 0, 0] := by
  decide +kernel

theorem rows1082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1082 = true := by
  decide +kernel

theorem tot1082 : totK PD2M8K2 D2M8K2.t1082 = [0, 0, 165509828686, 476461407951, 208523798688, 12223710258, 0, 0] := by
  decide +kernel

theorem rows1083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1083 = true := by
  decide +kernel

theorem tot1083 : totK PD2M8K2 D2M8K2.t1083 = [0, 0, 0, 302002704605, 438149056465, 82396822972, 1209030869, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

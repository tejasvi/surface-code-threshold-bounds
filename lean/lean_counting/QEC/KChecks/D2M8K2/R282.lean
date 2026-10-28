import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1128 = true := by
  decide +kernel

theorem tot1128 : totK PD2M8K2 D2M8K2.t1128 = [0, 50092618556, 317860924777, 422400632786, 86075082919, 1310517177, 0, 0] := by
  decide +kernel

theorem rows1129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1129 = true := by
  decide +kernel

theorem tot1129 : totK PD2M8K2 D2M8K2.t1129 = [0, 90856357215, 371374688244, 409237454072, 44005989047, 0, 0, 0] := by
  decide +kernel

theorem rows1130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1130 = true := by
  decide +kernel

theorem tot1130 : totK PD2M8K2 D2M8K2.t1130 = [0, 142565083513, 438107905117, 302407807634, 33032246799, 0, 0, 0] := by
  decide +kernel

theorem rows1131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1131 = true := by
  decide +kernel

theorem tot1131 : totK PD2M8K2 D2M8K2.t1131 = [0, 152669155160, 452501694459, 273269113383, 27605482304, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

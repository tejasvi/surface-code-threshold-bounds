import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1264 = true := by
  decide +kernel

theorem tot1264 : totK PD2M8K2 D2M8K2.t1264 = [0, 155361765672, 481591350014, 238260902763, 11023652771, 0, 0, 0] := by
  decide +kernel

theorem rows1265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1265 = true := by
  decide +kernel

theorem tot1265 : totK PD2M8K2 D2M8K2.t1265 = [0, 160708736316, 455227083409, 252166562262, 17364808128, 0, 0, 0] := by
  decide +kernel

theorem rows1266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1266 = true := by
  decide +kernel

theorem tot1266 : totK PD2M8K2 D2M8K2.t1266 = [0, 0, 291655858912, 469715610307, 83916466702, 1206465782, 0, 0] := by
  decide +kernel

theorem rows1267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1267 = true := by
  decide +kernel

theorem tot1267 : totK PD2M8K2 D2M8K2.t1267 = [0, 179483303131, 441374012754, 269052494166, 29662001941, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

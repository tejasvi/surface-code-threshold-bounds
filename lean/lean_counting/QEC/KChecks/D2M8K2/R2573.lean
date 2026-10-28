import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10292 = true := by
  decide +kernel

theorem tot10292 : totK PD2M8K2 D2M8K2.t10292 = [0, 0, 0, 299383164321, 485557157101, 97032982095, 1171084559, 0] := by
  decide +kernel

theorem rows10293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10293 = true := by
  decide +kernel

theorem tot10293 : totK PD2M8K2 D2M8K2.t10293 = [0, 0, 0, 206188905734, 455531669474, 182779939053, 11934365838, 0] := by
  decide +kernel

theorem rows10294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10294 = true := by
  decide +kernel

theorem tot10294 : totK PD2M8K2 D2M8K2.t10294 = [0, 0, 195143272018, 468547127302, 220045705466, 14971608201, 0, 0] := by
  decide +kernel

theorem rows10295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10295 = true := by
  decide +kernel

theorem tot10295 : totK PD2M8K2 D2M8K2.t10295 = [0, 0, 199913646256, 472739025788, 207620985276, 12096313584, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

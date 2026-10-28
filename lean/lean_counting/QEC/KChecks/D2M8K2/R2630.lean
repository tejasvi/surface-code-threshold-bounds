import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10520 = true := by
  decide +kernel

theorem tot10520 : totK PD2M8K2 D2M8K2.t10520 = [0, 0, 85808503149, 400920399018, 326263565047, 47332223894, 1369150432, 0] := by
  decide +kernel

theorem rows10521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10521 = true := by
  decide +kernel

theorem tot10521 : totK PD2M8K2 D2M8K2.t10521 = [0, 0, 0, 329660824101, 446927221507, 71902984220, 0, 0] := by
  decide +kernel

theorem rows10522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10522 = true := by
  decide +kernel

theorem tot10522 : totK PD2M8K2 D2M8K2.t10522 = [0, 0, 228894755498, 494110458289, 163265325449, 6434855751, 0, 0] := by
  decide +kernel

theorem rows10523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10523 = true := by
  decide +kernel

theorem tot10523 : totK PD2M8K2 D2M8K2.t10523 = [0, 0, 150096872984, 461204478691, 237447525772, 13452000861, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13120 = true := by
  decide +kernel

theorem tot13120 : totK PD2M8K2 D2M8K2.t13120 = [0, 0, 274486135463, 501614568363, 109111031855, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13121 = true := by
  decide +kernel

theorem tot13121 : totK PD2M8K2 D2M8K2.t13121 = [0, 127552667007, 395606281465, 360406154647, 45897827872, 0, 0, 0] := by
  decide +kernel

theorem rows13122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13122 = true := by
  decide +kernel

theorem tot13122 : totK PD2M8K2 D2M8K2.t13122 = [0, 205963827385, 470696622220, 216351454062, 14050539979, 0, 0, 0] := by
  decide +kernel

theorem rows13123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13123 = true := by
  decide +kernel

theorem tot13123 : totK PD2M8K2 D2M8K2.t13123 = [0, 86239566114, 419896795113, 350904522611, 40473730458, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

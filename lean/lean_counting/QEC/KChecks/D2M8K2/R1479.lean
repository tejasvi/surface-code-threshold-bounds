import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5916 = true := by
  decide +kernel

theorem tot5916 : totK PD2M8K2 D2M8K2.t5916 = [0, 0, 281615009229, 470296577534, 119982879582, 3882006667, 0, 0] := by
  decide +kernel

theorem rows5917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5917 = true := by
  decide +kernel

theorem tot5917 : totK PD2M8K2 D2M8K2.t5917 = [200807421208, 483080765663, 206522159502, 9826700831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5918 = true := by
  decide +kernel

theorem tot5918 : totK PD2M8K2 D2M8K2.t5918 = [122250587995, 426722954202, 324678038895, 33191331324, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5919 = true := by
  decide +kernel

theorem tot5919 : totK PD2M8K2 D2M8K2.t5919 = [26852199204, 288565770840, 491783323640, 110308158752, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

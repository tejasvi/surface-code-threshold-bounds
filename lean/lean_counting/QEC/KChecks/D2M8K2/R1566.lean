import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6264 = true := by
  decide +kernel

theorem tot6264 : totK PD2M8K2 D2M8K2.t6264 = [0, 0, 339533751825, 479439394579, 66500599088, 0, 0, 0] := by
  decide +kernel

theorem rows6265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6265 = true := by
  decide +kernel

theorem tot6265 : totK PD2M8K2 D2M8K2.t6265 = [176394742691, 411681522430, 148513935501, 82318132645, 68588630925, 3882006667, 0, 0] := by
  decide +kernel

theorem rows6266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6266 = true := by
  decide +kernel

theorem tot6266 : totK PD2M8K2 D2M8K2.t6266 = [175835846421, 435612328565, 236829985852, 19660340886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6267 = true := by
  decide +kernel

theorem tot6267 : totK PD2M8K2 D2M8K2.t6267 = [55384796968, 331544746424, 421219689629, 92563144548, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

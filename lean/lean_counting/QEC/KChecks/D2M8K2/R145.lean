import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t580 = true := by
  decide +kernel

theorem tot580 : totK PD2M8K2 D2M8K2.t580 = [0, 164714092683, 449639945313, 274988245617, 26993182208, 0, 0, 0] := by
  decide +kernel

theorem rows581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t581 = true := by
  decide +kernel

theorem tot581 : totK PD2M8K2 D2M8K2.t581 = [0, 78090548466, 342873995343, 393853011470, 80925875535, 1198073392, 0, 0] := by
  decide +kernel

theorem rows582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t582 = true := by
  decide +kernel

theorem tot582 : totK PD2M8K2 D2M8K2.t582 = [0, 61435016852, 292177238291, 421613552749, 121204926827, 4030866388, 0, 0] := by
  decide +kernel

theorem rows583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t583 = true := by
  decide +kernel

theorem tot583 : totK PD2M8K2 D2M8K2.t583 = [0, 178754144014, 461280668965, 249072188725, 22325532137, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

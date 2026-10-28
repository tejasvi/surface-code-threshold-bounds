import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t532 = true := by
  decide +kernel

theorem tot532 : totK PD2M8K2 D2M8K2.t532 = [0, 0, 188078536810, 464196284963, 209634539692, 13266821875, 0, 0] := by
  decide +kernel

theorem rows533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t533 = true := by
  decide +kernel

theorem tot533 : totK PD2M8K2 D2M8K2.t533 = [0, 0, 54428813195, 351464490118, 368001894879, 58834484921, 1021600638, 0] := by
  decide +kernel

theorem rows534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t534 = true := by
  decide +kernel

theorem tot534 : totK PD2M8K2 D2M8K2.t534 = [0, 0, 64773924968, 300361860409, 367421277195, 91215672299, 3552795014, 0] := by
  decide +kernel

theorem rows535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t535 = true := by
  decide +kernel

theorem tot535 : totK PD2M8K2 D2M8K2.t535 = [0, 0, 192708934065, 487789111588, 206458439329, 11385413710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

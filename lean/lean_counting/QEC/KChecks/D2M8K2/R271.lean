import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1084 = true := by
  decide +kernel

theorem tot1084 : totK PD2M8K2 D2M8K2.t1084 = [0, 0, 214325952717, 492541987981, 177518508799, 5533471308, 0, 0] := by
  decide +kernel

theorem rows1085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1085 = true := by
  decide +kernel

theorem tot1085 : totK PD2M8K2 D2M8K2.t1085 = [0, 0, 198693780528, 463138329717, 196183627750, 12177165453, 0, 0] := by
  decide +kernel

theorem rows1086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1086 = true := by
  decide +kernel

theorem tot1086 : totK PD2M8K2 D2M8K2.t1086 = [0, 0, 231560812930, 504064842331, 150502728798, 2530668022, 0, 0] := by
  decide +kernel

theorem rows1087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1087 = true := by
  decide +kernel

theorem tot1087 : totK PD2M8K2 D2M8K2.t1087 = [0, 0, 235103402207, 466280947315, 166072947234, 11092222415, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

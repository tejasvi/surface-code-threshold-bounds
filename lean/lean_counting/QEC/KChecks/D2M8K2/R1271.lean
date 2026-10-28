import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5084 = true := by
  decide +kernel

theorem tot5084 : totK PD2M8K2 D2M8K2.t5084 = [0, 180760729814, 461738316369, 251785409654, 18178010947, 0, 0, 0] := by
  decide +kernel

theorem rows5085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5085 = true := by
  decide +kernel

theorem tot5085 : totK PD2M8K2 D2M8K2.t5085 = [0, 66388834028, 328833481598, 394392706552, 82882351686, 1198073392, 0, 0] := by
  decide +kernel

theorem rows5086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5086 = true := by
  decide +kernel

theorem tot5086 : totK PD2M8K2 D2M8K2.t5086 = [0, 0, 225093865066, 484454087735, 168032891127, 9482920370, 0, 0] := by
  decide +kernel

theorem rows5087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5087 = true := by
  decide +kernel

theorem tot5087 : totK PD2M8K2 D2M8K2.t5087 = [0, 175160306834, 419429699726, 245880888402, 56196692509, 2569691499, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

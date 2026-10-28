import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14988 = true := by
  decide +kernel

theorem tot14988 : totK PD2M8K2 D2M8K2.t14988 = [0, 0, 190469581740, 494228318118, 205471499272, 11481658005, 0, 0] := by
  decide +kernel

theorem rows14989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14989 = true := by
  decide +kernel

theorem tot14989 : totK PD2M8K2 D2M8K2.t14989 = [0, 0, 171262282187, 453900308779, 240138396889, 15503624502, 0, 0] := by
  decide +kernel

theorem rows14990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14990 = true := by
  decide +kernel

theorem tot14990 : totK PD2M8K2 D2M8K2.t14990 = [0, 0, 87965506125, 361579663036, 346979653611, 60116698934, 1128585284, 0] := by
  decide +kernel

theorem rows14991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14991 = true := by
  decide +kernel

theorem tot14991 : totK PD2M8K2 D2M8K2.t14991 = [0, 0, 0, 288455984577, 455281080311, 110507730953, 4006170569, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

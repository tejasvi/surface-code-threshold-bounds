import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11468 = true := by
  decide +kernel

theorem tot11468 : totK PD2M8K2 D2M8K2.t11468 = [0, 138141707029, 444391701792, 289133214723, 31411298661, 0, 0, 0] := by
  decide +kernel

theorem rows11469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11469 = true := by
  decide +kernel

theorem tot11469 : totK PD2M8K2 D2M8K2.t11469 = [0, 0, 180096071388, 445419070110, 255288628816, 25298831311, 0, 0] := by
  decide +kernel

theorem rows11470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11470 = true := by
  decide +kernel

theorem tot11470 : totK PD2M8K2 D2M8K2.t11470 = [0, 0, 191176843928, 501110834657, 197247304336, 5430665091, 0, 0] := by
  decide +kernel

theorem rows11471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11471 = true := by
  decide +kernel

theorem tot11471 : totK PD2M8K2 D2M8K2.t11471 = [0, 171723400371, 400077306461, 228498660496, 94717979311, 6756203132, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

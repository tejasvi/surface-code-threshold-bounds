import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15128 = true := by
  decide +kernel

theorem tot15128 : totK PD2M8K2 D2M8K2.t15128 = [0, 0, 149685247596, 455848686657, 269515559837, 20777283226, 0, 0] := by
  decide +kernel

theorem rows15129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15129 = true := by
  decide +kernel

theorem tot15129 : totK PD2M8K2 D2M8K2.t15129 = [0, 0, 208120984955, 470985549005, 189046199003, 9523201561, 0, 0] := by
  decide +kernel

theorem rows15130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15130 = true := by
  decide +kernel

theorem tot15130 : totK PD2M8K2 D2M8K2.t15130 = [0, 0, 181804063640, 492266557877, 211290352237, 11451523762, 0, 0] := by
  decide +kernel

theorem rows15131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15131 = true := by
  decide +kernel

theorem tot15131 : totK PD2M8K2 D2M8K2.t15131 = [0, 0, 157089643897, 453117372629, 277478484614, 17827164195, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

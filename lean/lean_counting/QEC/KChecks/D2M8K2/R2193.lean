import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8772 = true := by
  decide +kernel

theorem tot8772 : totK PD2M8K2 D2M8K2.t8772 = [0, 179148547845, 430877793591, 274880317476, 34508733527, 0, 0, 0] := by
  decide +kernel

theorem rows8773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8773 = true := by
  decide +kernel

theorem tot8773 : totK PD2M8K2 D2M8K2.t8773 = [0, 176205413550, 460610097132, 249000004756, 17829946705, 0, 0, 0] := by
  decide +kernel

theorem rows8774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8774 = true := by
  decide +kernel

theorem tot8774 : totK PD2M8K2 D2M8K2.t8774 = [0, 73215069665, 341384532647, 366412323343, 118855666943, 13135967731, 0, 0] := by
  decide +kernel

theorem rows8775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8775 = true := by
  decide +kernel

theorem tot8775 : totK PD2M8K2 D2M8K2.t8775 = [0, 0, 172571399822, 454087753188, 243554509113, 14606904743, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5184 = true := by
  decide +kernel

theorem tot5184 : totK PD2M8K2 D2M8K2.t5184 = [0, 0, 82166277453, 334447908539, 378670849053, 103951546261, 1409560813, 0] := by
  decide +kernel

theorem rows5185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5185 = true := by
  decide +kernel

theorem tot5185 : totK PD2M8K2 D2M8K2.t5185 = [0, 0, 179466949467, 449612753141, 262465996232, 27391067017, 0, 0] := by
  decide +kernel

theorem rows5186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5186 = true := by
  decide +kernel

theorem tot5186 : totK PD2M8K2 D2M8K2.t5186 = [0, 0, 154981718383, 452874435648, 269939187883, 17794188794, 0, 0] := by
  decide +kernel

theorem rows5187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5187 = true := by
  decide +kernel

theorem tot5187 : totK PD2M8K2 D2M8K2.t5187 = [0, 0, 0, 221856784341, 488661859675, 149709312827, 7025833541, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

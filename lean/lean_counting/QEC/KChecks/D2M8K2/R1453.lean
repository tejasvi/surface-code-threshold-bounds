import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5812 = true := by
  decide +kernel

theorem tot5812 : totK PD2M8K2 D2M8K2.t5812 = [0, 164532907657, 439274511247, 279224004168, 30307792245, 0, 0, 0] := by
  decide +kernel

theorem rows5813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5813 = true := by
  decide +kernel

theorem tot5813 : totK PD2M8K2 D2M8K2.t5813 = [0, 120150086924, 441605854036, 300833708163, 16772284945, 0, 0, 0] := by
  decide +kernel

theorem rows5814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5814 = true := by
  decide +kernel

theorem tot5814 : totK PD2M8K2 D2M8K2.t5814 = [0, 0, 326101286343, 512848887802, 73771041415, 0, 0, 0] := by
  decide +kernel

theorem rows5815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5815 = true := by
  decide +kernel

theorem tot5815 : totK PD2M8K2 D2M8K2.t5815 = [0, 156764870116, 385487078079, 293516388297, 75376176519, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

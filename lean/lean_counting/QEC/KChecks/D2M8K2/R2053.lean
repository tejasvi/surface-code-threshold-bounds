import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8212 = true := by
  decide +kernel

theorem tot8212 : totK PD2M8K2 D2M8K2.t8212 = [0, 0, 18514691823, 303711847353, 449243324189, 106679010109, 3824247485, 0] := by
  decide +kernel

theorem rows8213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8213 = true := by
  decide +kernel

theorem tot8213 : totK PD2M8K2 D2M8K2.t8213 = [0, 0, 189980921397, 464896849568, 239886622029, 20128547347, 0, 0] := by
  decide +kernel

theorem rows8214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8214 = true := by
  decide +kernel

theorem tot8214 : totK PD2M8K2 D2M8K2.t8214 = [0, 0, 183826020472, 473008047128, 235579010894, 12551143345, 0, 0] := by
  decide +kernel

theorem rows8215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8215 = true := by
  decide +kernel

theorem tot8215 : totK PD2M8K2 D2M8K2.t8215 = [0, 0, 49142996948, 324601676409, 428687940125, 90969198117, 1242138600, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

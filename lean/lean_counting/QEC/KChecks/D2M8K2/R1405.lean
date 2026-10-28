import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5620 = true := by
  decide +kernel

theorem tot5620 : totK PD2M8K2 D2M8K2.t5620 = [160403090464, 474757170938, 254817139155, 13916467904, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5621 = true := by
  decide +kernel

theorem tot5621 : totK PD2M8K2 D2M8K2.t5621 = [0, 272271011006, 520943333019, 105513786330, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5622 = true := by
  decide +kernel

theorem tot5622 : totK PD2M8K2 D2M8K2.t5622 = [0, 208598855089, 497255988492, 175913014660, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows5623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5623 = true := by
  decide +kernel

theorem tot5623 : totK PD2M8K2 D2M8K2.t5623 = [0, 186574809334, 441540708342, 215782208420, 16891742343, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

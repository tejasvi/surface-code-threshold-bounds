import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9628 = true := by
  decide +kernel

theorem tot9628 : totK PD2M8K2 D2M8K2.t9628 = [0, 161042149573, 454872419982, 276124007670, 20812872639, 0, 0, 0] := by
  decide +kernel

theorem rows9629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9629 = true := by
  decide +kernel

theorem tot9629 : totK PD2M8K2 D2M8K2.t9629 = [0, 171794632953, 428582781590, 259256532684, 26494818292, 0, 0, 0] := by
  decide +kernel

theorem rows9630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9630 = true := by
  decide +kernel

theorem tot9630 : totK PD2M8K2 D2M8K2.t9630 = [0, 92937627352, 394280688815, 365983677625, 56899620910, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9631 = true := by
  decide +kernel

theorem tot9631 : totK PD2M8K2 D2M8K2.t9631 = [0, 0, 224519537270, 490224363117, 151343771751, 3633193399, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

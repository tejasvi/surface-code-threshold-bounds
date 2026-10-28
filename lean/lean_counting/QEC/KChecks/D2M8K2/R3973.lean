import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15892 = true := by
  decide +kernel

theorem tot15892 : totK PD2M8K2 D2M8K2.t15892 = [0, 174847607514, 472705075734, 247437911737, 14770254060, 0, 0, 0] := by
  decide +kernel

theorem rows15893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15893 = true := by
  decide +kernel

theorem tot15893 : totK PD2M8K2 D2M8K2.t15893 = [0, 70166284074, 326565928952, 379316411610, 133653515736, 9977052014, 0, 0] := by
  decide +kernel

theorem rows15894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15894 = true := by
  decide +kernel

theorem tot15894 : totK PD2M8K2 D2M8K2.t15894 = [0, 0, 243835713174, 506565335450, 160148586087, 4021104278, 0, 0] := by
  decide +kernel

theorem rows15895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15895 = true := by
  decide +kernel

theorem tot15895 : totK PD2M8K2 D2M8K2.t15895 = [0, 164100342924, 402555878292, 268072546059, 68438844026, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

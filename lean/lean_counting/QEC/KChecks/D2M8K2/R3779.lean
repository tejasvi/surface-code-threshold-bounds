import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15116 = true := by
  decide +kernel

theorem tot15116 : totK PD2M8K2 D2M8K2.t15116 = [0, 161288847707, 464438461354, 272358629729, 19475093686, 0, 0, 0] := by
  decide +kernel

theorem rows15117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15117 = true := by
  decide +kernel

theorem tot15117 : totK PD2M8K2 D2M8K2.t15117 = [0, 0, 254325492658, 510590169674, 131717200641, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15118 = true := by
  decide +kernel

theorem tot15118 : totK PD2M8K2 D2M8K2.t15118 = [0, 0, 160291510961, 456668485136, 243459470611, 13697907789, 0, 0] := by
  decide +kernel

theorem rows15119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15119 = true := by
  decide +kernel

theorem tot15119 : totK PD2M8K2 D2M8K2.t15119 = [0, 0, 189324476338, 468392950092, 223648394181, 16917284594, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

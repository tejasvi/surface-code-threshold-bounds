import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t236 = true := by
  decide +kernel

theorem tot236 : totK PD2M8K2 D2M8K2.t236 = [0, 0, 197861221688, 477412893337, 187727007265, 11991925116, 0, 0] := by
  decide +kernel

theorem rows237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t237 = true := by
  decide +kernel

theorem tot237 : totK PD2M8K2 D2M8K2.t237 = [0, 166116479020, 436419091893, 266037081567, 29076444687, 0, 0, 0] := by
  decide +kernel

theorem rows238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t238 = true := by
  decide +kernel

theorem tot238 : totK PD2M8K2 D2M8K2.t238 = [0, 202558821117, 458330722383, 220265818090, 17028259732, 0, 0, 0] := by
  decide +kernel

theorem rows239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t239 = true := by
  decide +kernel

theorem tot239 : totK PD2M8K2 D2M8K2.t239 = [0, 37670822061, 341259318223, 424986304611, 73094113302, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

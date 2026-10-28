import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10580 = true := by
  decide +kernel

theorem tot10580 : totK PD2M8K2 D2M8K2.t10580 = [0, 0, 280700717017, 519664258666, 99615153170, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10581 = true := by
  decide +kernel

theorem tot10581 : totK PD2M8K2 D2M8K2.t10581 = [0, 0, 204341216364, 495064249285, 177055732138, 5253830308, 0, 0] := by
  decide +kernel

theorem rows10582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10582 = true := by
  decide +kernel

theorem tot10582 : totK PD2M8K2 D2M8K2.t10582 = [0, 0, 216330892162, 466730135313, 181458991868, 9653832318, 0, 0] := by
  decide +kernel

theorem rows10583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10583 = true := by
  decide +kernel

theorem tot10583 : totK PD2M8K2 D2M8K2.t10583 = [0, 0, 87978522599, 381130479987, 324104063430, 49108495702, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

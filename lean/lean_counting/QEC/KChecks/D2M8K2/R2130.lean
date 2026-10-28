import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8520 = true := by
  decide +kernel

theorem tot8520 : totK PD2M8K2 D2M8K2.t8520 = [0, 182309491354, 460441698949, 258091989696, 24263010245, 0, 0, 0] := by
  decide +kernel

theorem rows8521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8521 = true := by
  decide +kernel

theorem tot8521 : totK PD2M8K2 D2M8K2.t8521 = [0, 172446104734, 475715069246, 239467610545, 12392743502, 0, 0, 0] := by
  decide +kernel

theorem rows8522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8522 = true := by
  decide +kernel

theorem tot8522 : totK PD2M8K2 D2M8K2.t8522 = [0, 0, 284944602338, 481947333450, 124992839578, 4031931762, 0, 0] := by
  decide +kernel

theorem rows8523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8523 = true := by
  decide +kernel

theorem tot8523 : totK PD2M8K2 D2M8K2.t8523 = [0, 64203887364, 313720191058, 394638846252, 90163202066, 1186940923, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

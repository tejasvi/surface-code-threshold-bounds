import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9524 = true := by
  decide +kernel

theorem tot9524 : totK PD2M8K2 D2M8K2.t9524 = [202277941304, 474975479081, 228567884505, 14232081361, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9525 = true := by
  decide +kernel

theorem tot9525 : totK PD2M8K2 D2M8K2.t9525 = [19689835847, 312029808173, 458041858991, 101925454205, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows9526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9526 = true := by
  decide +kernel

theorem tot9526 : totK PD2M8K2 D2M8K2.t9526 = [0, 208332613369, 484187983921, 190085253645, 7439461435, 0, 0, 0] := by
  decide +kernel

theorem rows9527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9527 = true := by
  decide +kernel

theorem tot9527 : totK PD2M8K2 D2M8K2.t9527 = [0, 182563770531, 474285352419, 218044078348, 14704558535, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

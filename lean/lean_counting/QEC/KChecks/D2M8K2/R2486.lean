import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9944 = true := by
  decide +kernel

theorem tot9944 : totK PD2M8K2 D2M8K2.t9944 = [0, 0, 0, 181480195749, 475098489526, 199921800656, 10625748888, 0] := by
  decide +kernel

theorem rows9945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9945 = true := by
  decide +kernel

theorem tot9945 : totK PD2M8K2 D2M8K2.t9945 = [0, 0, 0, 84644347099, 355505074266, 348698444353, 69365942277, 1369150432] := by
  decide +kernel

theorem rows9946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9946 = true := by
  decide +kernel

theorem tot9946 : totK PD2M8K2 D2M8K2.t9946 = [0, 0, 0, 47720933716, 390004917058, 377985573104, 39191025216, 0] := by
  decide +kernel

theorem rows9947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9947 = true := by
  decide +kernel

theorem tot9947 : totK PD2M8K2 D2M8K2.t9947 = [0, 0, 0, 226538523339, 506129189152, 139665279181, 2519764721, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

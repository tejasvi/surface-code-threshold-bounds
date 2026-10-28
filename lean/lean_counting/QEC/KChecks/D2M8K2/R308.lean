import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1232 = true := by
  decide +kernel

theorem tot1232 : totK PD2M8K2 D2M8K2.t1232 = [0, 156042733396, 362328680894, 264918447240, 102240162144, 6524090962, 0, 0] := by
  decide +kernel

theorem rows1233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1233 = true := by
  decide +kernel

theorem tot1233 : totK PD2M8K2 D2M8K2.t1233 = [0, 159025326867, 436407504033, 282505390251, 30237831796, 0, 0, 0] := by
  decide +kernel

theorem rows1234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1234 = true := by
  decide +kernel

theorem tot1234 : totK PD2M8K2 D2M8K2.t1234 = [0, 87395272022, 416530581940, 362166898429, 35874514832, 0, 0, 0] := by
  decide +kernel

theorem rows1235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1235 = true := by
  decide +kernel

theorem tot1235 : totK PD2M8K2 D2M8K2.t1235 = [0, 0, 218504868591, 491151865939, 163050043784, 5159868635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

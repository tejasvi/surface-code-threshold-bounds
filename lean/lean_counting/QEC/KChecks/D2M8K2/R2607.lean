import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10428 = true := by
  decide +kernel

theorem tot10428 : totK PD2M8K2 D2M8K2.t10428 = [0, 0, 99437036638, 334868319898, 348963299385, 93329395554, 3581949829, 0] := by
  decide +kernel

theorem rows10429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10429 = true := by
  decide +kernel

theorem tot10429 : totK PD2M8K2 D2M8K2.t10429 = [0, 0, 184977328421, 442068158894, 241440509947, 21865136818, 0, 0] := by
  decide +kernel

theorem rows10430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10430 = true := by
  decide +kernel

theorem tot10430 : totK PD2M8K2 D2M8K2.t10430 = [0, 0, 128510068681, 454244381458, 291831535065, 21367671415, 0, 0] := by
  decide +kernel

theorem rows10431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10431 = true := by
  decide +kernel

theorem tot10431 : totK PD2M8K2 D2M8K2.t10431 = [0, 0, 0, 281592927730, 516846414407, 91010629084, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

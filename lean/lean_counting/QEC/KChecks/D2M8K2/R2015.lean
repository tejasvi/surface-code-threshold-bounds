import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8060 = true := by
  decide +kernel

theorem tot8060 : totK PD2M8K2 D2M8K2.t8060 = [0, 43562993757, 284651606667, 443522784661, 111792784657, 3884009855, 0, 0] := by
  decide +kernel

theorem rows8061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8061 = true := by
  decide +kernel

theorem tot8061 : totK PD2M8K2 D2M8K2.t8061 = [0, 192946007130, 464311468728, 233206960662, 20872037697, 0, 0, 0] := by
  decide +kernel

theorem rows8062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8062 = true := by
  decide +kernel

theorem tot8062 : totK PD2M8K2 D2M8K2.t8062 = [0, 185305993966, 460497701571, 234326884351, 15184326078, 0, 0, 0] := by
  decide +kernel

theorem rows8063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8063 = true := by
  decide +kernel

theorem tot8063 : totK PD2M8K2 D2M8K2.t8063 = [0, 0, 294022849848, 492198291809, 109363508423, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

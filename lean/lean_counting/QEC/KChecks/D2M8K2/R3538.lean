import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14152 = true := by
  decide +kernel

theorem tot14152 : totK PD2M8K2 D2M8K2.t14152 = [183243395725, 435750783771, 262436416423, 53396918993, 7093008096, 0, 0, 0] := by
  decide +kernel

theorem rows14153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14153 = true := by
  decide +kernel

theorem tot14153 : totK PD2M8K2 D2M8K2.t14153 = [170292154681, 471818522273, 237743840210, 14794441526, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14154 = true := by
  decide +kernel

theorem tot14154 : totK PD2M8K2 D2M8K2.t14154 = [89058976036, 323512630794, 363479022191, 133612180073, 15864095392, 0, 0, 0] := by
  decide +kernel

theorem rows14155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14155 = true := by
  decide +kernel

theorem tot14155 : totK PD2M8K2 D2M8K2.t14155 = [0, 184577617876, 461663477398, 237092384372, 13530797253, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

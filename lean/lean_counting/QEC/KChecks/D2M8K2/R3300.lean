import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13200 = true := by
  decide +kernel

theorem tot13200 : totK PD2M8K2 D2M8K2.t13200 = [0, 173208392310, 452864160134, 258626863015, 31088909262, 0, 0, 0] := by
  decide +kernel

theorem rows13201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13201 = true := by
  decide +kernel

theorem tot13201 : totK PD2M8K2 D2M8K2.t13201 = [0, 161440244322, 446708006562, 277672235520, 22472153559, 0, 0, 0] := by
  decide +kernel

theorem rows13202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13202 = true := by
  decide +kernel

theorem tot13202 : totK PD2M8K2 D2M8K2.t13202 = [0, 93373242333, 351608279565, 373809511336, 81839351973, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13203 = true := by
  decide +kernel

theorem tot13203 : totK PD2M8K2 D2M8K2.t13203 = [0, 0, 228790113351, 489568985143, 166563150933, 4764360615, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

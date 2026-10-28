import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15380 = true := by
  decide +kernel

theorem tot15380 : totK PD2M8K2 D2M8K2.t15380 = [0, 0, 290193055125, 507372832670, 106517707173, 1164319620, 0, 0] := by
  decide +kernel

theorem rows15381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15381 = true := by
  decide +kernel

theorem tot15381 : totK PD2M8K2 D2M8K2.t15381 = [0, 0, 196619883846, 477962053509, 186808409234, 11885407614, 0, 0] := by
  decide +kernel

theorem rows15382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15382 = true := by
  decide +kernel

theorem tot15382 : totK PD2M8K2 D2M8K2.t15382 = [0, 183136919807, 443072864718, 256306942987, 30564699471, 0, 0, 0] := by
  decide +kernel

theorem rows15383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15383 = true := by
  decide +kernel

theorem tot15383 : totK PD2M8K2 D2M8K2.t15383 = [0, 195313849267, 478002305481, 221688846000, 13696570319, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

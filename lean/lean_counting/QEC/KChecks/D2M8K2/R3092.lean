import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12368 = true := by
  decide +kernel

theorem tot12368 : totK PD2M8K2 D2M8K2.t12368 = [0, 0, 243836276678, 508065535570, 139163700720, 1369549359, 0, 0] := by
  decide +kernel

theorem rows12369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12369 = true := by
  decide +kernel

theorem tot12369 : totK PD2M8K2 D2M8K2.t12369 = [0, 0, 211642607649, 461825594460, 184661149121, 12177165453, 0, 0] := by
  decide +kernel

theorem rows12370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12370 = true := by
  decide +kernel

theorem tot12370 : totK PD2M8K2 D2M8K2.t12370 = [0, 0, 203907159429, 484609673405, 186611507593, 9836604324, 0, 0] := by
  decide +kernel

theorem rows12371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12371 = true := by
  decide +kernel

theorem tot12371 : totK PD2M8K2 D2M8K2.t12371 = [0, 0, 231855612664, 479733210617, 156896157607, 5155785308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

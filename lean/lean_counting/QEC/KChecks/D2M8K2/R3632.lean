import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14528 = true := by
  decide +kernel

theorem tot14528 : totK PD2M8K2 D2M8K2.t14528 = [0, 168442776982, 473788857125, 247868123877, 13888635665, 0, 0, 0] := by
  decide +kernel

theorem rows14529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14529 = true := by
  decide +kernel

theorem tot14529 : totK PD2M8K2 D2M8K2.t14529 = [0, 0, 305508796088, 469773281494, 78053492432, 1053411165, 0, 0] := by
  decide +kernel

theorem rows14530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14530 = true := by
  decide +kernel

theorem tot14530 : totK PD2M8K2 D2M8K2.t14530 = [0, 150246259409, 363331873815, 267870890226, 75070071350, 3667207281, 0, 0] := by
  decide +kernel

theorem rows14531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14531 = true := by
  decide +kernel

theorem tot14531 : totK PD2M8K2 D2M8K2.t14531 = [0, 176373850712, 458697348632, 254838313487, 23356471282, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

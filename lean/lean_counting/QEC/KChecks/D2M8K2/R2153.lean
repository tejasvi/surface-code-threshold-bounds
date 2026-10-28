import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8612 = true := by
  decide +kernel

theorem tot8612 : totK PD2M8K2 D2M8K2.t8612 = [186582507103, 463704602714, 248787248357, 23236262830, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8613 = true := by
  decide +kernel

theorem tot8613 : totK PD2M8K2 D2M8K2.t8613 = [189167102516, 453460789345, 237038641643, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8614 = true := by
  decide +kernel

theorem tot8614 : totK PD2M8K2 D2M8K2.t8614 = [0, 325467834820, 474709627801, 90593560894, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8615 = true := by
  decide +kernel

theorem tot8615 : totK PD2M8K2 D2M8K2.t8615 = [0, 269085392606, 499374183212, 125491044969, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

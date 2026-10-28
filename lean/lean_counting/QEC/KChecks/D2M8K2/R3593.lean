import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14372 = true := by
  decide +kernel

theorem tot14372 : totK PD2M8K2 D2M8K2.t14372 = [0, 0, 11164499329, 198632409678, 441647639539, 181013219619, 11853261585, 0] := by
  decide +kernel

theorem rows14373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14373 = true := by
  decide +kernel

theorem tot14373 : totK PD2M8K2 D2M8K2.t14373 = [0, 0, 194544377976, 472424713760, 192869756286, 10905421912, 0, 0] := by
  decide +kernel

theorem rows14374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14374 = true := by
  decide +kernel

theorem tot14374 : totK PD2M8K2 D2M8K2.t14374 = [0, 0, 179429366641, 460028365816, 205330814084, 12977844203, 0, 0] := by
  decide +kernel

theorem rows14375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14375 = true := by
  decide +kernel

theorem tot14375 : totK PD2M8K2 D2M8K2.t14375 = [0, 0, 0, 307734957710, 446092518780, 74866737003, 1021600638, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8300 = true := by
  decide +kernel

theorem tot8300 : totK PD2M8K2 D2M8K2.t8300 = [0, 176523477734, 501776528091, 209728788045, 4907437938, 0, 0, 0] := by
  decide +kernel

theorem rows8301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8301 = true := by
  decide +kernel

theorem tot8301 : totK PD2M8K2 D2M8K2.t8301 = [0, 170897981212, 463167644649, 228665377456, 13880306384, 0, 0, 0] := by
  decide +kernel

theorem rows8302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8302 = true := by
  decide +kernel

theorem tot8302 : totK PD2M8K2 D2M8K2.t8302 = [0, 0, 284298942988, 485412299227, 86631235121, 1239866073, 0, 0] := by
  decide +kernel

theorem rows8303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8303 = true := by
  decide +kernel

theorem tot8303 : totK PD2M8K2 D2M8K2.t8303 = [0, 127169944728, 412461824405, 346776241253, 39686719425, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

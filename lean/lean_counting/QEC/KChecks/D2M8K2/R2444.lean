import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9776 = true := by
  decide +kernel

theorem tot9776 : totK PD2M8K2 D2M8K2.t9776 = [0, 186741398247, 449275400278, 236255215280, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows9777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9777 = true := by
  decide +kernel

theorem tot9777 : totK PD2M8K2 D2M8K2.t9777 = [0, 0, 319277060069, 471995770872, 85351378123, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9778 = true := by
  decide +kernel

theorem tot9778 : totK PD2M8K2 D2M8K2.t9778 = [0, 69229626996, 294669068341, 411716613386, 111974565989, 3884009855, 0, 0] := by
  decide +kernel

theorem rows9779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9779 = true := by
  decide +kernel

theorem tot9779 : totK PD2M8K2 D2M8K2.t9779 = [0, 170726534082, 458255265021, 250505941546, 19739469166, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

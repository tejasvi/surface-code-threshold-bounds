import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t524 = true := by
  decide +kernel

theorem tot524 : totK PD2M8K2 D2M8K2.t524 = [0, 0, 15921317223, 320671303453, 448340109065, 65170052166, 0, 0] := by
  decide +kernel

theorem rows525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t525 = true := by
  decide +kernel

theorem tot525 : totK PD2M8K2 D2M8K2.t525 = [0, 0, 183417393006, 468498973911, 241644286173, 20001318118, 0, 0] := by
  decide +kernel

theorem rows526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t526 = true := by
  decide +kernel

theorem tot526 : totK PD2M8K2 D2M8K2.t526 = [0, 0, 202051411086, 487044659101, 183073324515, 6986199635, 0, 0] := by
  decide +kernel

theorem rows527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t527 = true := by
  decide +kernel

theorem tot527 : totK PD2M8K2 D2M8K2.t527 = [0, 0, 198936102424, 471212419801, 214166162089, 16063424123, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

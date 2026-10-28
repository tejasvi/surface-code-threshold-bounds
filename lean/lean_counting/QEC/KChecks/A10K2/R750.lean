import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3000 = true := by
  decide +kernel

theorem tot3000 : totK PA10K2 A10K2.t3000 = [0, 0, 94395552473, 816581549775, 2123938273648, 1680612976902, 267725440657, 6766355402, 0, 0] := by
  decide +kernel

theorem rows3001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3001 = true := by
  decide +kernel

theorem tot3001 : totK PA10K2 A10K2.t3001 = [0, 0, 428209560454, 1849147157725, 2064495811395, 569916125655, 23293567916, 0, 0, 0] := by
  decide +kernel

theorem rows3002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3002 = true := by
  decide +kernel

theorem tot3002 : totK PA10K2 A10K2.t3002 = [0, 0, 327234200007, 1481016971448, 2142420952391, 966678886378, 75185559112, 0, 0, 0] := by
  decide +kernel

theorem rows3003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3003 = true := by
  decide +kernel

theorem tot3003 : totK PA10K2 A10K2.t3003 = [0, 0, 0, 576178960757, 1998924167089, 1910929867004, 397124812670, 12224107035, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

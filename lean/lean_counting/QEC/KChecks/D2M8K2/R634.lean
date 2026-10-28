import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2536 = true := by
  decide +kernel

theorem tot2536 : totK PD2M8K2 D2M8K2.t2536 = [0, 93391851717, 400251634411, 369509827327, 44657806538, 0, 0, 0] := by
  decide +kernel

theorem rows2537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2537 = true := by
  decide +kernel

theorem tot2537 : totK PD2M8K2 D2M8K2.t2537 = [0, 162136092157, 453097694203, 283549680149, 21553256642, 0, 0, 0] := by
  decide +kernel

theorem rows2538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2538 = true := by
  decide +kernel

theorem tot2538 : totK PD2M8K2 D2M8K2.t2538 = [0, 177775196140, 463396461011, 245076478287, 16828634270, 0, 0, 0] := by
  decide +kernel

theorem rows2539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2539 = true := by
  decide +kernel

theorem tot2539 : totK PD2M8K2 D2M8K2.t2539 = [0, 188987400393, 461649712043, 236017710313, 19920018668, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

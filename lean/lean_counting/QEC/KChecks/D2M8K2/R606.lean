import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2424 = true := by
  decide +kernel

theorem tot2424 : totK PD2M8K2 D2M8K2.t2424 = [0, 0, 174199877314, 477184532827, 233431735154, 14815639298, 0, 0] := by
  decide +kernel

theorem rows2425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2425 = true := by
  decide +kernel

theorem tot2425 : totK PD2M8K2 D2M8K2.t2425 = [0, 0, 177947042797, 445428545805, 262842055026, 21169395674, 0, 0] := by
  decide +kernel

theorem rows2426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2426 = true := by
  decide +kernel

theorem tot2426 : totK PD2M8K2 D2M8K2.t2426 = [0, 0, 155002192905, 455942253774, 267662867981, 18830981488, 0, 0] := by
  decide +kernel

theorem rows2427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2427 = true := by
  decide +kernel

theorem tot2427 : totK PD2M8K2 D2M8K2.t2427 = [0, 0, 0, 240221918457, 469295012344, 130878135582, 4879840392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

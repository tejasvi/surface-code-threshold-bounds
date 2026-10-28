import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15904 = true := by
  decide +kernel

theorem tot15904 : totK PD2M8K2 D2M8K2.t15904 = [0, 0, 202369277682, 475184078914, 186949506530, 9673986356, 0, 0] := by
  decide +kernel

theorem rows15905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15905 = true := by
  decide +kernel

theorem tot15905 : totK PD2M8K2 D2M8K2.t15905 = [0, 0, 66989628128, 354179807768, 363551651417, 55309550610, 1138244013, 0] := by
  decide +kernel

theorem rows15906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15906 = true := by
  decide +kernel

theorem tot15906 : totK PD2M8K2 D2M8K2.t15906 = [0, 0, 92489513495, 426852310599, 344644912762, 28205877417, 0, 0] := by
  decide +kernel

theorem rows15907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15907 = true := by
  decide +kernel

theorem tot15907 : totK PD2M8K2 D2M8K2.t15907 = [0, 0, 156965183464, 449654198608, 278825719970, 25905862242, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

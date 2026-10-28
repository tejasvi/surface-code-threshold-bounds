import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7296 = true := by
  decide +kernel

theorem tot7296 : totK PD2M8K2 D2M8K2.t7296 = [0, 0, 0, 227224558240, 508843381630, 153980909704, 5138457373, 0] := by
  decide +kernel

theorem rows7297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7297 = true := by
  decide +kernel

theorem tot7297 : totK PD2M8K2 D2M8K2.t7297 = [0, 0, 151182405642, 446678671676, 293119651188, 28055526974, 0, 0] := by
  decide +kernel

theorem rows7298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7298 = true := by
  decide +kernel

theorem tot7298 : totK PD2M8K2 D2M8K2.t7298 = [0, 0, 210381270699, 441875713529, 235052793528, 17495487386, 0, 0] := by
  decide +kernel

theorem rows7299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7299 = true := by
  decide +kernel

theorem tot7299 : totK PD2M8K2 D2M8K2.t7299 = [0, 0, 191595810113, 483283646941, 226992975492, 14944747389, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

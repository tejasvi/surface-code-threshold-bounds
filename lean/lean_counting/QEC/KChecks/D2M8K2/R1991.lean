import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7964 = true := by
  decide +kernel

theorem tot7964 : totK PD2M8K2 D2M8K2.t7964 = [0, 0, 0, 235951264757, 501843367951, 147918650119, 2519764721, 0] := by
  decide +kernel

theorem rows7965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7965 = true := by
  decide +kernel

theorem tot7965 : totK PD2M8K2 D2M8K2.t7965 = [0, 0, 0, 235209993321, 462047989058, 162619064782, 11026950091, 0] := by
  decide +kernel

theorem rows7966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7966 = true := by
  decide +kernel

theorem tot7966 : totK PD2M8K2 D2M8K2.t7966 = [0, 0, 0, 243594539257, 493479284166, 132363407047, 2447234685, 0] := by
  decide +kernel

theorem rows7967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7967 = true := by
  decide +kernel

theorem tot7967 : totK PD2M8K2 D2M8K2.t7967 = [0, 0, 0, 242065545819, 496484791678, 135635517914, 2772616150, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

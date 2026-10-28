import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4996 = true := by
  decide +kernel

theorem tot4996 : totK PD2M8K2 D2M8K2.t4996 = [0, 0, 11585800147, 369560178354, 468926274634, 49360338678, 0, 0] := by
  decide +kernel

theorem rows4997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4997 = true := by
  decide +kernel

theorem tot4997 : totK PD2M8K2 D2M8K2.t4997 = [0, 0, 90349095627, 333992510437, 399917044274, 101711655265, 1415142070, 0] := by
  decide +kernel

theorem rows4998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4998 = true := by
  decide +kernel

theorem tot4998 : totK PD2M8K2 D2M8K2.t4998 = [0, 0, 167456538397, 458402149986, 278258121146, 17585302487, 0, 0] := by
  decide +kernel

theorem rows4999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4999 = true := by
  decide +kernel

theorem tot4999 : totK PD2M8K2 D2M8K2.t4999 = [0, 0, 89677770257, 401768955515, 382527056506, 53011563282, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

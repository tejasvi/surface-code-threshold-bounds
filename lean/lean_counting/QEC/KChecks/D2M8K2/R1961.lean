import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7844 = true := by
  decide +kernel

theorem tot7844 : totK PD2M8K2 D2M8K2.t7844 = [0, 0, 133949771794, 343508101397, 354142642618, 92645654754, 1415142070, 0] := by
  decide +kernel

theorem rows7845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7845 = true := by
  decide +kernel

theorem tot7845 : totK PD2M8K2 D2M8K2.t7845 = [0, 0, 198265925983, 496920982443, 217127548935, 9803941968, 0, 0] := by
  decide +kernel

theorem rows7846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7846 = true := by
  decide +kernel

theorem tot7846 : totK PD2M8K2 D2M8K2.t7846 = [0, 178256666961, 410672516228, 217127382574, 88304041041, 10798778176, 0, 0] := by
  decide +kernel

theorem rows7847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7847 = true := by
  decide +kernel

theorem tot7847 : totK PD2M8K2 D2M8K2.t7847 = [0, 167998592346, 433587479005, 242520635426, 19859907739, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

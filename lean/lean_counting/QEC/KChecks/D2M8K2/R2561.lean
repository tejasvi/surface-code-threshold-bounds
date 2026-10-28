import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10244 = true := by
  decide +kernel

theorem tot10244 : totK PD2M8K2 D2M8K2.t10244 = [0, 0, 172881138109, 454015877435, 273069710505, 27254131634, 0, 0] := by
  decide +kernel

theorem rows10245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10245 = true := by
  decide +kernel

theorem tot10245 : totK PD2M8K2 D2M8K2.t10245 = [0, 0, 194010629620, 485328534245, 223795243735, 8977779328, 0, 0] := by
  decide +kernel

theorem rows10246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10246 = true := by
  decide +kernel

theorem tot10246 : totK PD2M8K2 D2M8K2.t10246 = [0, 0, 34473473380, 276097657741, 401834002135, 182659624877, 19152079361, 0] := by
  decide +kernel

theorem rows10247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10247 = true := by
  decide +kernel

theorem tot10247 : totK PD2M8K2 D2M8K2.t10247 = [0, 0, 0, 220772864236, 494029507736, 163678036830, 4912480105, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

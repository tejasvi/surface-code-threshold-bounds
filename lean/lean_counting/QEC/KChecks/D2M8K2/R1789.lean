import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7156 = true := by
  decide +kernel

theorem tot7156 : totK PD2M8K2 D2M8K2.t7156 = [0, 140433394095, 446782869443, 284577334202, 21889072041, 0, 0, 0] := by
  decide +kernel

theorem rows7157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7157 = true := by
  decide +kernel

theorem tot7157 : totK PD2M8K2 D2M8K2.t7157 = [0, 0, 208282075934, 481333238951, 172916545782, 8214782009, 0, 0] := by
  decide +kernel

theorem rows7158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7158 = true := by
  decide +kernel

theorem tot7158 : totK PD2M8K2 D2M8K2.t7158 = [0, 86654048599, 326679676584, 373575982064, 94853622413, 3581949829, 0, 0] := by
  decide +kernel

theorem rows7159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7159 = true := by
  decide +kernel

theorem tot7159 : totK PD2M8K2 D2M8K2.t7159 = [0, 170885735598, 452554028404, 260525973078, 25363074863, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

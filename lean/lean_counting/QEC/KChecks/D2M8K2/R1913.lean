import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7652 = true := by
  decide +kernel

theorem tot7652 : totK PD2M8K2 D2M8K2.t7652 = [0, 0, 126751692978, 440083778739, 304001141109, 24455920083, 0, 0] := by
  decide +kernel

theorem rows7653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7653 = true := by
  decide +kernel

theorem tot7653 : totK PD2M8K2 D2M8K2.t7653 = [0, 0, 0, 284275322484, 502286993149, 96930614827, 1369150432, 0] := by
  decide +kernel

theorem rows7654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7654 = true := by
  decide +kernel

theorem tot7654 : totK PD2M8K2 D2M8K2.t7654 = [0, 0, 159686860411, 448268183271, 279450774609, 26065811486, 0, 0] := by
  decide +kernel

theorem rows7655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7655 = true := by
  decide +kernel

theorem tot7655 : totK PD2M8K2 D2M8K2.t7655 = [0, 0, 177171957290, 449122313220, 249133486631, 16753003576, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

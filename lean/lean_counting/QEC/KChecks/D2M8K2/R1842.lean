import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7368 = true := by
  decide +kernel

theorem tot7368 : totK PD2M8K2 D2M8K2.t7368 = [0, 0, 192160864846, 487604015984, 217378743172, 8061635119, 0, 0] := by
  decide +kernel

theorem rows7369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7369 = true := by
  decide +kernel

theorem tot7369 : totK PD2M8K2 D2M8K2.t7369 = [0, 0, 172250596352, 460115386032, 250007761279, 22222956560, 0, 0] := by
  decide +kernel

theorem rows7370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7370 = true := by
  decide +kernel

theorem tot7370 : totK PD2M8K2 D2M8K2.t7370 = [0, 0, 179600865894, 465926978818, 239858731213, 13761953177, 0, 0] := by
  decide +kernel

theorem rows7371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7371 = true := by
  decide +kernel

theorem tot7371 : totK PD2M8K2 D2M8K2.t7371 = [0, 0, 88264756189, 352989391476, 363155582702, 78066552938, 1162935789, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

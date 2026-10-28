import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1972 = true := by
  decide +kernel

theorem tot1972 : totK PD2M8K2 D2M8K2.t1972 = [0, 0, 202528578287, 476277496329, 205641002945, 10875173101, 0, 0] := by
  decide +kernel

theorem rows1973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1973 = true := by
  decide +kernel

theorem tot1973 : totK PD2M8K2 D2M8K2.t1973 = [0, 102184501845, 304935303204, 355231412512, 151525069026, 13468148062, 0, 0] := by
  decide +kernel

theorem rows1974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1974 = true := by
  decide +kernel

theorem tot1974 : totK PD2M8K2 D2M8K2.t1974 = [0, 196999820717, 470679652740, 226658389774, 14984818298, 0, 0, 0] := by
  decide +kernel

theorem rows1975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1975 = true := by
  decide +kernel

theorem tot1975 : totK PD2M8K2 D2M8K2.t1975 = [0, 125084172275, 443577635211, 304446604295, 32469628777, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

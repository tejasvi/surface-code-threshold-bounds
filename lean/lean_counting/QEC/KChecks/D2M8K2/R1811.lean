import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7244 = true := by
  decide +kernel

theorem tot7244 : totK PD2M8K2 D2M8K2.t7244 = [0, 0, 179264115148, 455462010587, 278112551521, 28337392052, 0, 0] := by
  decide +kernel

theorem rows7245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7245 = true := by
  decide +kernel

theorem tot7245 : totK PD2M8K2 D2M8K2.t7245 = [0, 0, 165903952289, 468575026760, 256736637382, 18591509916, 0, 0] := by
  decide +kernel

theorem rows7246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7246 = true := by
  decide +kernel

theorem tot7246 : totK PD2M8K2 D2M8K2.t7246 = [0, 0, 0, 238435991680, 504950281331, 144215004754, 3973351865, 0] := by
  decide +kernel

theorem rows7247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7247 = true := by
  decide +kernel

theorem tot7247 : totK PD2M8K2 D2M8K2.t7247 = [0, 0, 172341156901, 458786427051, 249373121131, 40972106421, 1310997200, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

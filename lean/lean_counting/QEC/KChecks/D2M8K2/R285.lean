import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1140 = true := by
  decide +kernel

theorem tot1140 : totK PD2M8K2 D2M8K2.t1140 = [0, 26126490397, 327109027863, 444456710585, 81483371908, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1141 = true := by
  decide +kernel

theorem tot1141 : totK PD2M8K2 D2M8K2.t1141 = [0, 46289452755, 281850239155, 447853529142, 120845967074, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1142 = true := by
  decide +kernel

theorem tot1142 : totK PD2M8K2 D2M8K2.t1142 = [0, 194285106825, 472191763879, 229639956815, 19771284190, 0, 0, 0] := by
  decide +kernel

theorem rows1143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1143 = true := by
  decide +kernel

theorem tot1143 : totK PD2M8K2 D2M8K2.t1143 = [0, 88005768970, 391450110169, 370421191741, 46988057253, 1210106048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

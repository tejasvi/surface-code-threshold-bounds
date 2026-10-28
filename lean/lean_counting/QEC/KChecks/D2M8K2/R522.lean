import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2088 = true := by
  decide +kernel

theorem tot2088 : totK PD2M8K2 D2M8K2.t2088 = [0, 182433760473, 468970567028, 247564726524, 16228219889, 0, 0, 0] := by
  decide +kernel

theorem rows2089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2089 = true := by
  decide +kernel

theorem tot2089 : totK PD2M8K2 D2M8K2.t2089 = [0, 0, 282640458883, 497455724556, 115593620798, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2090 = true := by
  decide +kernel

theorem tot2090 : totK PD2M8K2 D2M8K2.t2090 = [0, 0, 209317033053, 483781677432, 183098157715, 7442000727, 0, 0] := by
  decide +kernel

theorem rows2091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2091 = true := by
  decide +kernel

theorem tot2091 : totK PD2M8K2 D2M8K2.t2091 = [0, 0, 188302677190, 469519469688, 218229026233, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

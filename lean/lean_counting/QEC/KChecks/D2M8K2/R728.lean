import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2912 = true := by
  decide +kernel

theorem tot2912 : totK PD2M8K2 D2M8K2.t2912 = [0, 206038935731, 489724041040, 180185776138, 9482920370, 0, 0, 0] := by
  decide +kernel

theorem rows2913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2913 = true := by
  decide +kernel

theorem tot2913 : totK PD2M8K2 D2M8K2.t2913 = [172390672205, 442175000553, 246136268113, 38967301164, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows2914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2914 = true := by
  decide +kernel

theorem tot2914 : totK PD2M8K2 D2M8K2.t2914 = [188332850901, 452800502777, 234353553566, 20048117613, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2915 = true := by
  decide +kernel

theorem tot2915 : totK PD2M8K2 D2M8K2.t2915 = [74997432338, 352365910481, 386210758809, 77704573573, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

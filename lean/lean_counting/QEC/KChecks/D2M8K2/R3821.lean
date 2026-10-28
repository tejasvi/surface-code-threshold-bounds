import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15284 = true := by
  decide +kernel

theorem tot15284 : totK PD2M8K2 D2M8K2.t15284 = [0, 0, 187051103686, 472650818521, 248779627354, 18835772370, 0, 0] := by
  decide +kernel

theorem rows15285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15285 = true := by
  decide +kernel

theorem tot15285 : totK PD2M8K2 D2M8K2.t15285 = [0, 0, 191307462320, 472659535908, 221935532889, 12523541424, 0, 0] := by
  decide +kernel

theorem rows15286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15286 = true := by
  decide +kernel

theorem tot15286 : totK PD2M8K2 D2M8K2.t15286 = [0, 0, 8125304319, 312269698018, 489894523896, 91857422807, 1178750802, 0] := by
  decide +kernel

theorem rows15287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15287 = true := by
  decide +kernel

theorem tot15287 : totK PD2M8K2 D2M8K2.t15287 = [0, 0, 33678501200, 275382882063, 458852070545, 124318290201, 4257574148, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12228 = true := by
  decide +kernel

theorem tot12228 : totK PD2M8K2 D2M8K2.t12228 = [0, 0, 262513808675, 503679356692, 133958154270, 4009909289, 0, 0] := by
  decide +kernel

theorem rows12229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12229 = true := by
  decide +kernel

theorem tot12229 : totK PD2M8K2 D2M8K2.t12229 = [0, 156620130629, 398779995137, 280847147195, 61087329470, 1149959346, 0, 0] := by
  decide +kernel

theorem rows12230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12230 = true := by
  decide +kernel

theorem tot12230 : totK PD2M8K2 D2M8K2.t12230 = [0, 177487975125, 432158898334, 275152696143, 30435711819, 0, 0, 0] := by
  decide +kernel

theorem rows12231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12231 = true := by
  decide +kernel

theorem tot12231 : totK PD2M8K2 D2M8K2.t12231 = [0, 78933146671, 424758715650, 352574170713, 35394648151, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

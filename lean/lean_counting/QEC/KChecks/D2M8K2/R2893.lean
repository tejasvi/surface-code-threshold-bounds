import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11572 = true := by
  decide +kernel

theorem tot11572 : totK PD2M8K2 D2M8K2.t11572 = [55267625348, 344942571242, 412453888908, 79303373939, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11573 = true := by
  decide +kernel

theorem tot11573 : totK PD2M8K2 D2M8K2.t11573 = [22237561286, 271895567788, 471380204751, 125000748675, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11574 = true := by
  decide +kernel

theorem tot11574 : totK PD2M8K2 D2M8K2.t11574 = [202621027469, 472708969673, 213572772908, 18690155982, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11575 = true := by
  decide +kernel

theorem tot11575 : totK PD2M8K2 D2M8K2.t11575 = [154631132256, 444726278259, 267889623846, 20902670269, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

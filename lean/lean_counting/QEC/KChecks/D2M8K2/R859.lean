import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3436 = true := by
  decide +kernel

theorem tot3436 : totK PD2M8K2 D2M8K2.t3436 = [177769216434, 453784406382, 254671216066, 18234939311, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3437 = true := by
  decide +kernel

theorem tot3437 : totK PD2M8K2 D2M8K2.t3437 = [80501774670, 348459669092, 382107266314, 83610240622, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows3438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3438 = true := by
  decide +kernel

theorem tot3438 : totK PD2M8K2 D2M8K2.t3438 = [0, 227722977122, 486365604350, 163334455122, 9394901982, 0, 0, 0] := by
  decide +kernel

theorem rows3439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3439 = true := by
  decide +kernel

theorem tot3439 : totK PD2M8K2 D2M8K2.t3439 = [155785623112, 412469813194, 282027387892, 59081774304, 2478123692, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

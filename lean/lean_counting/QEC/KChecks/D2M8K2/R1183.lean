import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4732 = true := by
  decide +kernel

theorem tot4732 : totK PD2M8K2 D2M8K2.t4732 = [0, 0, 273273060266, 512152565323, 99380178200, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4733 = true := by
  decide +kernel

theorem tot4733 : totK PD2M8K2 D2M8K2.t4733 = [0, 87517773469, 338502879142, 354886005829, 96589474609, 3884009855, 0, 0] := by
  decide +kernel

theorem rows4734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4734 = true := by
  decide +kernel

theorem tot4734 : totK PD2M8K2 D2M8K2.t4734 = [0, 183760417529, 449533148717, 254721832076, 25971805521, 0, 0, 0] := by
  decide +kernel

theorem rows4735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4735 = true := by
  decide +kernel

theorem tot4735 : totK PD2M8K2 D2M8K2.t4735 = [0, 145772694100, 450787664609, 295801054307, 23574091243, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

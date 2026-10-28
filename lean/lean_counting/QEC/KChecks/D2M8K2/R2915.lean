import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11660 = true := by
  decide +kernel

theorem tot11660 : totK PD2M8K2 D2M8K2.t11660 = [0, 134813967960, 365099348976, 290259775759, 74310451467, 3436822651, 0, 0] := by
  decide +kernel

theorem rows11661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11661 = true := by
  decide +kernel

theorem tot11661 : totK PD2M8K2 D2M8K2.t11661 = [0, 185104199575, 467420984611, 242791222024, 18252358503, 0, 0, 0] := by
  decide +kernel

theorem rows11662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11662 = true := by
  decide +kernel

theorem tot11662 : totK PD2M8K2 D2M8K2.t11662 = [0, 94888957409, 394580620681, 317217529745, 42969409066, 1021600638, 0, 0] := by
  decide +kernel

theorem rows11663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11663 = true := by
  decide +kernel

theorem tot11663 : totK PD2M8K2 D2M8K2.t11663 = [0, 0, 318337960599, 465911532890, 77475808693, 991020230, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

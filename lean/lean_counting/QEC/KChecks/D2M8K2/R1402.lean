import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5608 = true := by
  decide +kernel

theorem tot5608 : totK PD2M8K2 D2M8K2.t5608 = [152868529535, 454067205642, 273598876157, 28152385143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5609 = true := by
  decide +kernel

theorem tot5609 : totK PD2M8K2 D2M8K2.t5609 = [0, 178234796745, 448509540747, 256647648942, 25269856785, 0, 0, 0] := by
  decide +kernel

theorem rows5610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5610 = true := by
  decide +kernel

theorem tot5610 : totK PD2M8K2 D2M8K2.t5610 = [85167078157, 276935600496, 372526805657, 150577522301, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows5611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5611 = true := by
  decide +kernel

theorem tot5611 : totK PD2M8K2 D2M8K2.t5611 = [171870687712, 452574007547, 264389572461, 26566035967, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

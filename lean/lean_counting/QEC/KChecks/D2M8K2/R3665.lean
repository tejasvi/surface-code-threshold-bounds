import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14660 = true := by
  decide +kernel

theorem tot14660 : totK PD2M8K2 D2M8K2.t14660 = [0, 135641448723, 375569133285, 298889921811, 68223572756, 2569691499, 0, 0] := by
  decide +kernel

theorem rows14661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14661 = true := by
  decide +kernel

theorem tot14661 : totK PD2M8K2 D2M8K2.t14661 = [0, 173136001274, 441700041174, 259881155221, 25966986292, 0, 0, 0] := by
  decide +kernel

theorem rows14662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14662 = true := by
  decide +kernel

theorem tot14662 : totK PD2M8K2 D2M8K2.t14662 = [0, 90004739926, 368961676450, 346495853536, 59212488983, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14663 = true := by
  decide +kernel

theorem tot14663 : totK PD2M8K2 D2M8K2.t14663 = [0, 0, 312385004176, 516786526127, 76043300522, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

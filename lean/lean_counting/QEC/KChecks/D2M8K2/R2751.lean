import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11004 = true := by
  decide +kernel

theorem tot11004 : totK PD2M8K2 D2M8K2.t11004 = [0, 198888632159, 463584858980, 216752185918, 13468795916, 0, 0, 0] := by
  decide +kernel

theorem rows11005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11005 = true := by
  decide +kernel

theorem tot11005 : totK PD2M8K2 D2M8K2.t11005 = [0, 47081948287, 347805976901, 400671658923, 60657913037, 1021600638, 0, 0] := by
  decide +kernel

theorem rows11006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11006 = true := by
  decide +kernel

theorem tot11006 : totK PD2M8K2 D2M8K2.t11006 = [0, 65310693356, 307061307544, 379063681025, 91918588940, 3552795014, 0, 0] := by
  decide +kernel

theorem rows11007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11007 = true := by
  decide +kernel

theorem tot11007 : totK PD2M8K2 D2M8K2.t11007 = [0, 173601705220, 462635867124, 250368602727, 20604354612, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

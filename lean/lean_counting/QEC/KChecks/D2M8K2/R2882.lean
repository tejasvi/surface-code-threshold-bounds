import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11528 = true := by
  decide +kernel

theorem tot11528 : totK PD2M8K2 D2M8K2.t11528 = [0, 93610018881, 205722927785, 237580816022, 291987000362, 84897210332, 1429815836, 0] := by
  decide +kernel

theorem rows11529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11529 = true := by
  decide +kernel

theorem tot11529 : totK PD2M8K2 D2M8K2.t11529 = [0, 173779972420, 446985568692, 260262730866, 20975040218, 0, 0, 0] := by
  decide +kernel

theorem rows11530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11530 = true := by
  decide +kernel

theorem tot11530 : totK PD2M8K2 D2M8K2.t11530 = [0, 162612680181, 469594205390, 264215124069, 17912851798, 0, 0, 0] := by
  decide +kernel

theorem rows11531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11531 = true := by
  decide +kernel

theorem tot11531 : totK PD2M8K2 D2M8K2.t11531 = [0, 0, 162852474212, 447284790514, 259973059820, 25316940874, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

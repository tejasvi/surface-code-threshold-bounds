import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4608 = true := by
  decide +kernel

theorem tot4608 : totK PD2M8K2 D2M8K2.t4608 = [0, 0, 193345194871, 478637368739, 225931968582, 15302588063, 0, 0] := by
  decide +kernel

theorem rows4609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4609 = true := by
  decide +kernel

theorem tot4609 : totK PD2M8K2 D2M8K2.t4609 = [0, 0, 118057437873, 447886551592, 322923188404, 34688065716, 0, 0] := by
  decide +kernel

theorem rows4610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4610 = true := by
  decide +kernel

theorem tot4610 : totK PD2M8K2 D2M8K2.t4610 = [0, 0, 0, 196580969514, 478237984391, 218946747692, 13604428459, 0] := by
  decide +kernel

theorem rows4611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4611 = true := by
  decide +kernel

theorem tot4611 : totK PD2M8K2 D2M8K2.t4611 = [0, 0, 81374014488, 327125211701, 374962225430, 104024276370, 1409560813, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

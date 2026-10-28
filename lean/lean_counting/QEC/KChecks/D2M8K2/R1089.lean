import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4356 = true := by
  decide +kernel

theorem tot4356 : totK PD2M8K2 D2M8K2.t4356 = [0, 0, 0, 178120028926, 466955876810, 243116223631, 19416920390, 0] := by
  decide +kernel

theorem rows4357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4357 = true := by
  decide +kernel

theorem tot4357 : totK PD2M8K2 D2M8K2.t4357 = [0, 0, 0, 154123453904, 454479906670, 261043437146, 16676276051, 0] := by
  decide +kernel

theorem rows4358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4358 = true := by
  decide +kernel

theorem tot4358 : totK PD2M8K2 D2M8K2.t4358 = [0, 0, 0, 0, 321244515531, 469700602872, 77282589890, 1323630408] := by
  decide +kernel

theorem rows4359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4359 = true := by
  decide +kernel

theorem tot4359 : totK PD2M8K2 D2M8K2.t4359 = [0, 0, 0, 180201175960, 434473940660, 263005970040, 29301768371, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

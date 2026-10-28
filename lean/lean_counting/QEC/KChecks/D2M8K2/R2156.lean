import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8624 = true := by
  decide +kernel

theorem tot8624 : totK PD2M8K2 D2M8K2.t8624 = [0, 194531410298, 474656656951, 226699173016, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows8625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8625 = true := by
  decide +kernel

theorem tot8625 : totK PD2M8K2 D2M8K2.t8625 = [0, 207055319672, 496493556230, 190516953768, 5064232198, 0, 0, 0] := by
  decide +kernel

theorem rows8626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8626 = true := by
  decide +kernel

theorem tot8626 : totK PD2M8K2 D2M8K2.t8626 = [0, 172608218966, 436994485148, 247205329784, 23953760117, 0, 0, 0] := by
  decide +kernel

theorem rows8627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8627 = true := by
  decide +kernel

theorem tot8627 : totK PD2M8K2 D2M8K2.t8627 = [0, 92584149739, 381230861131, 337668738281, 55765786854, 1095107716, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

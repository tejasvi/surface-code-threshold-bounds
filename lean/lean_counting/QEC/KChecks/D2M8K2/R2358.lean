import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9432 = true := by
  decide +kernel

theorem tot9432 : totK PD2M8K2 D2M8K2.t9432 = [0, 0, 202612829976, 473645765434, 187911633882, 10856745823, 0, 0] := by
  decide +kernel

theorem rows9433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9433 = true := by
  decide +kernel

theorem tot9433 : totK PD2M8K2 D2M8K2.t9433 = [0, 0, 187396986225, 466717307732, 206781172304, 12264952070, 0, 0] := by
  decide +kernel

theorem rows9434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9434 = true := by
  decide +kernel

theorem tot9434 : totK PD2M8K2 D2M8K2.t9434 = [0, 0, 201496009791, 478801932045, 188052660309, 10871000096, 0, 0] := by
  decide +kernel

theorem rows9435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9435 = true := by
  decide +kernel

theorem tot9435 : totK PD2M8K2 D2M8K2.t9435 = [0, 0, 189661133085, 474319518557, 208541659067, 12337737162, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

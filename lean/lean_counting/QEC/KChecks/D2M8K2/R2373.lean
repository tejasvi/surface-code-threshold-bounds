import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9492 = true := by
  decide +kernel

theorem tot9492 : totK PD2M8K2 D2M8K2.t9492 = [0, 193029202322, 467888677072, 232970547259, 14851641519, 0, 0, 0] := by
  decide +kernel

theorem rows9493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9493 = true := by
  decide +kernel

theorem tot9493 : totK PD2M8K2 D2M8K2.t9493 = [0, 150777232859, 460038020626, 283600197895, 24920361612, 0, 0, 0] := by
  decide +kernel

theorem rows9494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9494 = true := by
  decide +kernel

theorem tot9494 : totK PD2M8K2 D2M8K2.t9494 = [0, 0, 173024294617, 443993313244, 250834541475, 25191558099, 0, 0] := by
  decide +kernel

theorem rows9495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9495 = true := by
  decide +kernel

theorem tot9495 : totK PD2M8K2 D2M8K2.t9495 = [0, 0, 217658649246, 488655605647, 175633677360, 5206224793, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

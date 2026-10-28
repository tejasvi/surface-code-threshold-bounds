import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9716 = true := by
  decide +kernel

theorem tot9716 : totK PD2M8K2 D2M8K2.t9716 = [0, 0, 287700899249, 491633043196, 140393600423, 2959325837, 0, 0] := by
  decide +kernel

theorem rows9717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9717 = true := by
  decide +kernel

theorem tot9717 : totK PD2M8K2 D2M8K2.t9717 = [0, 0, 196726982220, 496008938960, 193338703845, 8971621811, 0, 0] := by
  decide +kernel

theorem rows9718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9718 = true := by
  decide +kernel

theorem tot9718 : totK PD2M8K2 D2M8K2.t9718 = [0, 0, 172477294670, 447920148019, 251231387554, 19668375445, 0, 0] := by
  decide +kernel

theorem rows9719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9719 = true := by
  decide +kernel

theorem tot9719 : totK PD2M8K2 D2M8K2.t9719 = [0, 0, 87939979134, 350516659606, 351957355519, 60476566098, 1135526696, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

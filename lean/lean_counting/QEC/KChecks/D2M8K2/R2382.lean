import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9528 = true := by
  decide +kernel

theorem tot9528 : totK PD2M8K2 D2M8K2.t9528 = [0, 163897138926, 469691365455, 218238939794, 10735115630, 0, 0, 0] := by
  decide +kernel

theorem rows9529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9529 = true := by
  decide +kernel

theorem tot9529 : totK PD2M8K2 D2M8K2.t9529 = [0, 86953184342, 341054825318, 368442872180, 69846542387, 1206465782, 0, 0] := by
  decide +kernel

theorem rows9530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9530 = true := by
  decide +kernel

theorem tot9530 : totK PD2M8K2 D2M8K2.t9530 = [0, 88408878787, 389673921998, 370643685768, 36885823855, 0, 0, 0] := by
  decide +kernel

theorem rows9531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9531 = true := by
  decide +kernel

theorem tot9531 : totK PD2M8K2 D2M8K2.t9531 = [0, 161693062113, 453242805150, 274198288583, 29089283249, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

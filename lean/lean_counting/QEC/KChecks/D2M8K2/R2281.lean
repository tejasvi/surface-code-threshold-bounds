import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9124 = true := by
  decide +kernel

theorem tot9124 : totK PD2M8K2 D2M8K2.t9124 = [0, 0, 222176584585, 486834933913, 195855571823, 6781982568, 0, 0] := by
  decide +kernel

theorem rows9125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9125 = true := by
  decide +kernel

theorem tot9125 : totK PD2M8K2 D2M8K2.t9125 = [0, 0, 231670700182, 483570687921, 141774494870, 2244230249, 0, 0] := by
  decide +kernel

theorem rows9126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9126 = true := by
  decide +kernel

theorem tot9126 : totK PD2M8K2 D2M8K2.t9126 = [0, 0, 208662321092, 473314444341, 175332565174, 6582704093, 0, 0] := by
  decide +kernel

theorem rows9127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9127 = true := by
  decide +kernel

theorem tot9127 : totK PD2M8K2 D2M8K2.t9127 = [0, 0, 183117999153, 462011453550, 233042175969, 18184677977, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

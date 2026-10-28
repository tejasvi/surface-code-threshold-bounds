import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7184 = true := by
  decide +kernel

theorem tot7184 : totK PD2M8K2 D2M8K2.t7184 = [0, 159473947647, 448968726170, 273206665504, 19455320537, 0, 0, 0] := by
  decide +kernel

theorem rows7185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7185 = true := by
  decide +kernel

theorem tot7185 : totK PD2M8K2 D2M8K2.t7185 = [0, 89370891521, 334242673452, 391678254395, 85419481260, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7186 = true := by
  decide +kernel

theorem tot7186 : totK PD2M8K2 D2M8K2.t7186 = [0, 0, 219152499368, 486598924333, 171195596395, 9399702592, 0, 0] := by
  decide +kernel

theorem rows7187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7187 = true := by
  decide +kernel

theorem tot7187 : totK PD2M8K2 D2M8K2.t7187 = [0, 151718351142, 431499103879, 278935307738, 48365602257, 2479761128, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

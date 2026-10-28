import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8144 = true := by
  decide +kernel

theorem tot8144 : totK PD2M8K2 D2M8K2.t8144 = [0, 0, 19433589518, 326050539287, 445586466444, 86051949085, 1162935789, 0] := by
  decide +kernel

theorem rows8145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8145 = true := by
  decide +kernel

theorem tot8145 : totK PD2M8K2 D2M8K2.t8145 = [0, 0, 0, 198551907280, 453900014495, 186451522214, 11853261585, 0] := by
  decide +kernel

theorem rows8146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8146 = true := by
  decide +kernel

theorem tot8146 : totK PD2M8K2 D2M8K2.t8146 = [0, 0, 182685969704, 471210966415, 232389446023, 16131077680, 0, 0] := by
  decide +kernel

theorem rows8147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8147 = true := by
  decide +kernel

theorem tot8147 : totK PD2M8K2 D2M8K2.t8147 = [0, 0, 195457419725, 479125772367, 214765141995, 12375753328, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

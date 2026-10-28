import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7164 = true := by
  decide +kernel

theorem tot7164 : totK PD2M8K2 D2M8K2.t7164 = [0, 0, 157928230636, 466282352634, 239156888369, 12694203091, 0, 0] := by
  decide +kernel

theorem rows7165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7165 = true := by
  decide +kernel

theorem tot7165 : totK PD2M8K2 D2M8K2.t7165 = [0, 0, 0, 296477739963, 458252882670, 81675802260, 1138244013, 0] := by
  decide +kernel

theorem rows7166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7166 = true := by
  decide +kernel

theorem tot7166 : totK PD2M8K2 D2M8K2.t7166 = [0, 0, 172986484160, 479874848161, 247138853632, 17449961755, 0, 0] := by
  decide +kernel

theorem rows7167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7167 = true := by
  decide +kernel

theorem tot7167 : totK PD2M8K2 D2M8K2.t7167 = [0, 0, 223877852713, 496829724769, 173174408325, 5315349635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

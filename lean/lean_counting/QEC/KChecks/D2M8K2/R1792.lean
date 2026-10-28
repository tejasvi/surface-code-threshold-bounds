import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7168 = true := by
  decide +kernel

theorem tot7168 : totK PD2M8K2 D2M8K2.t7168 = [0, 0, 188101075478, 486253822312, 217249956678, 11051716772, 0, 0] := by
  decide +kernel

theorem rows7169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7169 = true := by
  decide +kernel

theorem tot7169 : totK PD2M8K2 D2M8K2.t7169 = [0, 0, 156062270197, 457665993225, 254311100041, 16126223677, 0, 0] := by
  decide +kernel

theorem rows7170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7170 = true := by
  decide +kernel

theorem tot7170 : totK PD2M8K2 D2M8K2.t7170 = [0, 0, 222522969377, 504774922864, 168560627184, 2682721786, 0, 0] := by
  decide +kernel

theorem rows7171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7171 = true := by
  decide +kernel

theorem tot7171 : totK PD2M8K2 D2M8K2.t7171 = [0, 0, 152484897188, 458989039657, 238690409974, 13597322258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

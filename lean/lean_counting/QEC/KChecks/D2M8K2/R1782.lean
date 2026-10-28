import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7128 = true := by
  decide +kernel

theorem tot7128 : totK PD2M8K2 D2M8K2.t7128 = [0, 0, 282752933772, 520554683470, 92161262304, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7129 = true := by
  decide +kernel

theorem tot7129 : totK PD2M8K2 D2M8K2.t7129 = [0, 106934552672, 353478926254, 335137422211, 86676433943, 3884009855, 0, 0] := by
  decide +kernel

theorem rows7130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7130 = true := by
  decide +kernel

theorem tot7130 : totK PD2M8K2 D2M8K2.t7130 = [0, 200837409341, 461801483407, 232147704298, 22941706825, 0, 0, 0] := by
  decide +kernel

theorem rows7131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7131 = true := by
  decide +kernel

theorem tot7131 : totK PD2M8K2 D2M8K2.t7131 = [0, 91836339268, 411116979604, 364304896699, 34951777773, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

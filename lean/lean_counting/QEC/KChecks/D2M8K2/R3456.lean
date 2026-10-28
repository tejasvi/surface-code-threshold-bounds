import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13824 = true := by
  decide +kernel

theorem tot13824 : totK PD2M8K2 D2M8K2.t13824 = [0, 172652162697, 476499185017, 228412758226, 7799206690, 0, 0, 0] := by
  decide +kernel

theorem rows13825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13825 = true := by
  decide +kernel

theorem tot13825 : totK PD2M8K2 D2M8K2.t13825 = [171568788750, 439756996281, 254571857685, 49740206812, 4429463114, 0, 0, 0] := by
  decide +kernel

theorem rows13826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13826 = true := by
  decide +kernel

theorem tot13826 : totK PD2M8K2 D2M8K2.t13826 = [191551576359, 461516931405, 226436827124, 15617333555, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13827 = true := by
  decide +kernel

theorem tot13827 : totK PD2M8K2 D2M8K2.t13827 = [71268930115, 343342678660, 397104295938, 88200400924, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

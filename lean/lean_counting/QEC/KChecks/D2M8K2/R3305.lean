import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13220 = true := by
  decide +kernel

theorem tot13220 : totK PD2M8K2 D2M8K2.t13220 = [0, 173839897800, 444357878304, 264120733070, 28347022840, 0, 0, 0] := by
  decide +kernel

theorem rows13221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13221 = true := by
  decide +kernel

theorem tot13221 : totK PD2M8K2 D2M8K2.t13221 = [0, 190824070234, 472069938278, 218701011828, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows13222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13222 = true := by
  decide +kernel

theorem tot13222 : totK PD2M8K2 D2M8K2.t13222 = [0, 45950195159, 311636458824, 430371951930, 89819607175, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13223 = true := by
  decide +kernel

theorem tot13223 : totK PD2M8K2 D2M8K2.t13223 = [0, 0, 200466603010, 469673288316, 185885594177, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

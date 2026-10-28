import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7796 = true := by
  decide +kernel

theorem tot7796 : totK PD2M8K2 D2M8K2.t7796 = [0, 188279367166, 485685874620, 218502633341, 10887814723, 0, 0, 0] := by
  decide +kernel

theorem rows7797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7797 = true := by
  decide +kernel

theorem tot7797 : totK PD2M8K2 D2M8K2.t7797 = [0, 0, 230689602098, 485079872155, 156396621638, 4967996017, 0, 0] := by
  decide +kernel

theorem rows7798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7798 = true := by
  decide +kernel

theorem tot7798 : totK PD2M8K2 D2M8K2.t7798 = [0, 0, 246195950271, 489350064263, 159495612477, 8981457347, 0, 0] := by
  decide +kernel

theorem rows7799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7799 = true := by
  decide +kernel

theorem tot7799 : totK PD2M8K2 D2M8K2.t7799 = [0, 0, 170810745043, 469339983481, 214908965686, 10797020908, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

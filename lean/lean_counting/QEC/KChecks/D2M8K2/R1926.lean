import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7704 = true := by
  decide +kernel

theorem tot7704 : totK PD2M8K2 D2M8K2.t7704 = [0, 0, 86563879224, 258401415601, 385079817278, 153279495344, 5521894595, 0] := by
  decide +kernel

theorem rows7705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7705 = true := by
  decide +kernel

theorem tot7705 : totK PD2M8K2 D2M8K2.t7705 = [0, 0, 182695852126, 469965761720, 255529460317, 21054802440, 0, 0] := by
  decide +kernel

theorem rows7706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7706 = true := by
  decide +kernel

theorem tot7706 : totK PD2M8K2 D2M8K2.t7706 = [0, 0, 175934456340, 472730732630, 244905748959, 13632511348, 0, 0] := by
  decide +kernel

theorem rows7707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7707 = true := by
  decide +kernel

theorem tot7707 : totK PD2M8K2 D2M8K2.t7707 = [0, 0, 0, 284908502981, 509324607199, 108612143596, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

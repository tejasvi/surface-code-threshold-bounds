import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows20 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t20 = true := by
  decide +kernel

theorem tot20 : totK PD2M8K2 D2M8K2.t20 = [0, 184746237567, 478177789524, 223817148313, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows21 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t21 = true := by
  decide +kernel

theorem tot21 : totK PD2M8K2 D2M8K2.t21 = [0, 188575001416, 455756911407, 216501954738, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows22 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t22 = true := by
  decide +kernel

theorem tot22 : totK PD2M8K2 D2M8K2.t22 = [0, 124821642950, 436435599753, 291404706163, 28000958262, 0, 0, 0] := by
  decide +kernel

theorem rows23 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t23 = true := by
  decide +kernel

theorem tot23 : totK PD2M8K2 D2M8K2.t23 = [0, 0, 290143811069, 460188440090, 104670175105, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

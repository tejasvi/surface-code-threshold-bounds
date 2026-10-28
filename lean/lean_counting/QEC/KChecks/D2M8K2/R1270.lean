import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5080 = true := by
  decide +kernel

theorem tot5080 : totK PD2M8K2 D2M8K2.t5080 = [0, 192312159857, 479334987382, 222537793935, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows5081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5081 = true := by
  decide +kernel

theorem tot5081 : totK PD2M8K2 D2M8K2.t5081 = [0, 47118357002, 313363461420, 433976874481, 84233140829, 1164319620, 0, 0] := by
  decide +kernel

theorem rows5082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5082 = true := by
  decide +kernel

theorem tot5082 : totK PD2M8K2 D2M8K2.t5082 = [0, 0, 201303255626, 473836593632, 186861947214, 11885407614, 0, 0] := by
  decide +kernel

theorem rows5083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5083 = true := by
  decide +kernel

theorem tot5083 : totK PD2M8K2 D2M8K2.t5083 = [0, 170590953727, 446135960746, 251590642497, 33112491725, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

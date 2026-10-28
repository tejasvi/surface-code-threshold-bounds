import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10652 = true := by
  decide +kernel

theorem tot10652 : totK PD2M8K2 D2M8K2.t10652 = [0, 0, 93184785870, 404333031628, 362859119530, 40140876423, 0, 0] := by
  decide +kernel

theorem rows10653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10653 = true := by
  decide +kernel

theorem tot10653 : totK PD2M8K2 D2M8K2.t10653 = [0, 0, 175265229416, 456960876435, 231215138248, 18690206973, 0, 0] := by
  decide +kernel

theorem rows10654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10654 = true := by
  decide +kernel

theorem tot10654 : totK PD2M8K2 D2M8K2.t10654 = [0, 0, 221254596355, 505530616753, 181200593614, 4059882638, 0, 0] := by
  decide +kernel

theorem rows10655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10655 = true := by
  decide +kernel

theorem tot10655 : totK PD2M8K2 D2M8K2.t10655 = [0, 0, 186482694146, 478652400751, 211649035859, 11051716772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

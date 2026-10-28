import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5816 = true := by
  decide +kernel

theorem tot5816 : totK PD2M8K2 D2M8K2.t5816 = [0, 171632570718, 451440756800, 252689724474, 18950718513, 0, 0, 0] := by
  decide +kernel

theorem rows5817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5817 = true := by
  decide +kernel

theorem tot5817 : totK PD2M8K2 D2M8K2.t5817 = [0, 92515481918, 420486741600, 360235797144, 42367375651, 0, 0, 0] := by
  decide +kernel

theorem rows5818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5818 = true := by
  decide +kernel

theorem tot5818 : totK PD2M8K2 D2M8K2.t5818 = [0, 0, 225133439554, 497044614208, 151688697013, 2484078857, 0, 0] := by
  decide +kernel

theorem rows5819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5819 = true := by
  decide +kernel

theorem tot5819 : totK PD2M8K2 D2M8K2.t5819 = [175368045151, 376548395843, 131992981729, 111712282582, 91362372070, 6818291842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5064 = true := by
  decide +kernel

theorem tot5064 : totK PD2M8K2 D2M8K2.t5064 = [0, 0, 0, 198253193727, 459916810068, 186853502042, 11934365838, 0] := by
  decide +kernel

theorem rows5065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5065 = true := by
  decide +kernel

theorem tot5065 : totK PD2M8K2 D2M8K2.t5065 = [0, 0, 169581915327, 453594268739, 247851094646, 22202731849, 0, 0] := by
  decide +kernel

theorem rows5066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5066 = true := by
  decide +kernel

theorem tot5066 : totK PD2M8K2 D2M8K2.t5066 = [0, 0, 162685660134, 456869546009, 258869616231, 16380377171, 0, 0] := by
  decide +kernel

theorem rows5067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5067 = true := by
  decide +kernel

theorem tot5067 : totK PD2M8K2 D2M8K2.t5067 = [0, 0, 84033991644, 364529282776, 351631517060, 59762403288, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

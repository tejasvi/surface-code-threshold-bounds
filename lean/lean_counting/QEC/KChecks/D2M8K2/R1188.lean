import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4752 = true := by
  decide +kernel

theorem tot4752 : totK PD2M8K2 D2M8K2.t4752 = [0, 0, 172263091196, 453344782971, 257672306401, 22041786505, 0, 0] := by
  decide +kernel

theorem rows4753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4753 = true := by
  decide +kernel

theorem tot4753 : totK PD2M8K2 D2M8K2.t4753 = [0, 18870634022, 174659141066, 440197092868, 261317227133, 21861286897, 0, 0] := by
  decide +kernel

theorem rows4754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4754 = true := by
  decide +kernel

theorem tot4754 : totK PD2M8K2 D2M8K2.t4754 = [0, 209063422608, 480050169854, 187402182869, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows4755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4755 = true := by
  decide +kernel

theorem tot4755 : totK PD2M8K2 D2M8K2.t4755 = [0, 147655911961, 453842428718, 264554117309, 16464045146, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

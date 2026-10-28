import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8160 = true := by
  decide +kernel

theorem tot8160 : totK PD2M8K2 D2M8K2.t8160 = [0, 89098610365, 346623834667, 380004497873, 76369467266, 1198073392, 0, 0] := by
  decide +kernel

theorem rows8161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8161 = true := by
  decide +kernel

theorem tot8161 : totK PD2M8K2 D2M8K2.t8161 = [0, 0, 251000750140, 488957630298, 155008612524, 8470662040, 0, 0] := by
  decide +kernel

theorem rows8162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8162 = true := by
  decide +kernel

theorem tot8162 : totK PD2M8K2 D2M8K2.t8162 = [0, 139733096986, 377376271578, 292601919722, 77661632981, 3581949829, 0, 0] := by
  decide +kernel

theorem rows8163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8163 = true := by
  decide +kernel

theorem tot8163 : totK PD2M8K2 D2M8K2.t8163 = [0, 179079508016, 453836454824, 259065790738, 26889629665, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7036 = true := by
  decide +kernel

theorem tot7036 : totK PD2M8K2 D2M8K2.t7036 = [0, 0, 191242339821, 470564117229, 227775483187, 18087669958, 0, 0] := by
  decide +kernel

theorem rows7037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7037 = true := by
  decide +kernel

theorem tot7037 : totK PD2M8K2 D2M8K2.t7037 = [0, 0, 201596833401, 477305602634, 209336453590, 15083436772, 0, 0] := by
  decide +kernel

theorem rows7038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7038 = true := by
  decide +kernel

theorem tot7038 : totK PD2M8K2 D2M8K2.t7038 = [0, 0, 202016405126, 479341111300, 200883301960, 11453348948, 0, 0] := by
  decide +kernel

theorem rows7039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7039 = true := by
  decide +kernel

theorem tot7039 : totK PD2M8K2 D2M8K2.t7039 = [0, 0, 206158693850, 478816836712, 186958405012, 7438052843, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t548 = true := by
  decide +kernel

theorem tot548 : totK PD2M8K2 D2M8K2.t548 = [0, 100775115955, 343626229043, 345939207649, 86990678583, 3462014130, 0, 0] := by
  decide +kernel

theorem rows549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t549 = true := by
  decide +kernel

theorem tot549 : totK PD2M8K2 D2M8K2.t549 = [0, 198702215675, 456642020223, 237925304848, 18549410704, 0, 0, 0] := by
  decide +kernel

theorem rows550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t550 = true := by
  decide +kernel

theorem tot550 : totK PD2M8K2 D2M8K2.t550 = [0, 22116493432, 333262937674, 447667550124, 78254539029, 1104198603, 0, 0] := by
  decide +kernel

theorem rows551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t551 = true := by
  decide +kernel

theorem tot551 : totK PD2M8K2 D2M8K2.t551 = [0, 89667044445, 334371333153, 360720219401, 87459906619, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

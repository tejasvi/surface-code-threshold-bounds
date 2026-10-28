import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1752 = true := by
  decide +kernel

theorem tot1752 : totK PD2M8K2 D2M8K2.t1752 = [0, 0, 169103209791, 476927958582, 244192957260, 11409580711, 0, 0] := by
  decide +kernel

theorem rows1753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1753 = true := by
  decide +kernel

theorem tot1753 : totK PD2M8K2 D2M8K2.t1753 = [0, 0, 155552939965, 444829657272, 272523773716, 18188187394, 0, 0] := by
  decide +kernel

theorem rows1754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1754 = true := by
  decide +kernel

theorem tot1754 : totK PD2M8K2 D2M8K2.t1754 = [0, 0, 0, 227431784973, 457701446650, 157450645218, 9602367571, 0] := by
  decide +kernel

theorem rows1755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1755 = true := by
  decide +kernel

theorem tot1755 : totK PD2M8K2 D2M8K2.t1755 = [0, 0, 102556995953, 346585041626, 338420607478, 80848198406, 3581949829, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

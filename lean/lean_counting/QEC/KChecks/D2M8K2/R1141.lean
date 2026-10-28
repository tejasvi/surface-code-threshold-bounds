import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4564 = true := by
  decide +kernel

theorem tot4564 : totK PD2M8K2 D2M8K2.t4564 = [0, 0, 188540108795, 479549075467, 221611474899, 15386750601, 0, 0] := by
  decide +kernel

theorem rows4565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4565 = true := by
  decide +kernel

theorem tot4565 : totK PD2M8K2 D2M8K2.t4565 = [0, 0, 0, 354009894886, 490810150713, 60183926580, 0, 0] := by
  decide +kernel

theorem rows4566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4566 = true := by
  decide +kernel

theorem tot4566 : totK PD2M8K2 D2M8K2.t4566 = [0, 0, 100061397447, 340828902655, 364403502139, 96587127835, 2585032425, 0] := by
  decide +kernel

theorem rows4567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4567 = true := by
  decide +kernel

theorem tot4567 : totK PD2M8K2 D2M8K2.t4567 = [0, 0, 170751411407, 451467603267, 271605457063, 29322329664, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

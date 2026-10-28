import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9556 = true := by
  decide +kernel

theorem tot9556 : totK PD2M8K2 D2M8K2.t9556 = [161274750009, 447359144725, 283274171946, 22666707949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9557 = true := by
  decide +kernel

theorem tot9557 : totK PD2M8K2 D2M8K2.t9557 = [92934196222, 341937027325, 376042996736, 81455141835, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows9558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9558 = true := by
  decide +kernel

theorem tot9558 : totK PD2M8K2 D2M8K2.t9558 = [0, 248611848507, 486726177583, 158161587649, 4761634222, 0, 0, 0] := by
  decide +kernel

theorem rows9559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9559 = true := by
  decide +kernel

theorem tot9559 : totK PD2M8K2 D2M8K2.t9559 = [0, 182163085273, 464590021930, 226415639150, 17381584168, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

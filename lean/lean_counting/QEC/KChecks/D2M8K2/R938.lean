import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3752 = true := by
  decide +kernel

theorem tot3752 : totK PD2M8K2 D2M8K2.t3752 = [0, 117246799802, 444885103474, 327950047532, 31574870067, 0, 0, 0] := by
  decide +kernel

theorem rows3753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3753 = true := by
  decide +kernel

theorem tot3753 : totK PD2M8K2 D2M8K2.t3753 = [0, 28036261290, 281080335909, 481204845528, 111884992118, 1415142070, 0, 0] := by
  decide +kernel

theorem rows3754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3754 = true := by
  decide +kernel

theorem tot3754 : totK PD2M8K2 D2M8K2.t3754 = [0, 187003022557, 467247491916, 246518882555, 23151192985, 0, 0, 0] := by
  decide +kernel

theorem rows3755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3755 = true := by
  decide +kernel

theorem tot3755 : totK PD2M8K2 D2M8K2.t3755 = [0, 190038208004, 468360151270, 233647913200, 13286492890, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

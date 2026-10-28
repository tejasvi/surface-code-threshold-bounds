import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11752 = true := by
  decide +kernel

theorem tot11752 : totK PD2M8K2 D2M8K2.t11752 = [0, 0, 90682560486, 442066311932, 298824198882, 21372115616, 0, 0] := by
  decide +kernel

theorem rows11753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11753 = true := by
  decide +kernel

theorem tot11753 : totK PD2M8K2 D2M8K2.t11753 = [0, 0, 196850541173, 467111594432, 210944432716, 12552144954, 0, 0] := by
  decide +kernel

theorem rows11754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11754 = true := by
  decide +kernel

theorem tot11754 : totK PD2M8K2 D2M8K2.t11754 = [0, 0, 195384260257, 460239881021, 193890339386, 12436572017, 0, 0] := by
  decide +kernel

theorem rows11755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11755 = true := by
  decide +kernel

theorem tot11755 : totK PD2M8K2 D2M8K2.t11755 = [0, 0, 234165516827, 488780102765, 145757935497, 2447234685, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

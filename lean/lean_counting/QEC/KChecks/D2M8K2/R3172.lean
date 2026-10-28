import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12688 = true := by
  decide +kernel

theorem tot12688 : totK PD2M8K2 D2M8K2.t12688 = [0, 0, 121679063083, 415451126942, 302577161058, 25399050409, 0, 0] := by
  decide +kernel

theorem rows12689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12689 = true := by
  decide +kernel

theorem tot12689 : totK PD2M8K2 D2M8K2.t12689 = [0, 0, 0, 277078285641, 500577122175, 100675927583, 1369150432, 0] := by
  decide +kernel

theorem rows12690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12690 = true := by
  decide +kernel

theorem tot12690 : totK PD2M8K2 D2M8K2.t12690 = [0, 0, 171652222897, 427910657776, 282987034440, 24592756399, 0, 0] := by
  decide +kernel

theorem rows12691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12691 = true := by
  decide +kernel

theorem tot12691 : totK PD2M8K2 D2M8K2.t12691 = [0, 0, 170753623478, 467617071073, 240029232858, 16905318215, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

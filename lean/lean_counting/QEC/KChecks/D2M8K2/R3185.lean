import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12740 = true := by
  decide +kernel

theorem tot12740 : totK PD2M8K2 D2M8K2.t12740 = [0, 0, 48864814763, 227028265796, 420802482559, 183862499443, 7877424857, 0] := by
  decide +kernel

theorem rows12741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12741 = true := by
  decide +kernel

theorem tot12741 : totK PD2M8K2 D2M8K2.t12741 = [0, 0, 198567522159, 471536348515, 232916403673, 21899705541, 0, 0] := by
  decide +kernel

theorem rows12742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12742 = true := by
  decide +kernel

theorem tot12742 : totK PD2M8K2 D2M8K2.t12742 = [0, 0, 170791424039, 462851690287, 239598628003, 12280210264, 0, 0] := by
  decide +kernel

theorem rows12743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12743 = true := by
  decide +kernel

theorem tot12743 : totK PD2M8K2 D2M8K2.t12743 = [0, 0, 0, 299284058606, 492933516739, 103434664977, 2909416399, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

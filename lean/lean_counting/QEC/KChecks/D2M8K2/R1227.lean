import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4908 = true := by
  decide +kernel

theorem tot4908 : totK PD2M8K2 D2M8K2.t4908 = [0, 0, 0, 271301726212, 456162835544, 179387832227, 10964724083, 0] := by
  decide +kernel

theorem rows4909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4909 = true := by
  decide +kernel

theorem tot4909 : totK PD2M8K2 D2M8K2.t4909 = [0, 0, 0, 209545229976, 493444413854, 190020289466, 6781982568, 0] := by
  decide +kernel

theorem rows4910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4910 = true := by
  decide +kernel

theorem tot4910 : totK PD2M8K2 D2M8K2.t4910 = [0, 0, 0, 302452477026, 483179857814, 102435109960, 1260239111, 0] := by
  decide +kernel

theorem rows4911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4911 = true := by
  decide +kernel

theorem tot4911 : totK PD2M8K2 D2M8K2.t4911 = [0, 0, 0, 165829457763, 485104844863, 211948177599, 10980938576, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

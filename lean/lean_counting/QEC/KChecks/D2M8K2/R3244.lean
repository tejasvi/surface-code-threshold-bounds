import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12976 = true := by
  decide +kernel

theorem tot12976 : totK PD2M8K2 D2M8K2.t12976 = [0, 0, 0, 311078501730, 461182904512, 76232744301, 1206465782, 0] := by
  decide +kernel

theorem rows12977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12977 = true := by
  decide +kernel

theorem tot12977 : totK PD2M8K2 D2M8K2.t12977 = [0, 0, 182442894580, 449844460263, 261307514684, 31250947553, 0, 0] := by
  decide +kernel

theorem rows12978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12978 = true := by
  decide +kernel

theorem tot12978 : totK PD2M8K2 D2M8K2.t12978 = [0, 0, 210672805297, 493150359262, 191343967516, 5488642804, 0, 0] := by
  decide +kernel

theorem rows12979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12979 = true := by
  decide +kernel

theorem tot12979 : totK PD2M8K2 D2M8K2.t12979 = [0, 0, 204563972591, 479862327941, 201154222098, 10231520536, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

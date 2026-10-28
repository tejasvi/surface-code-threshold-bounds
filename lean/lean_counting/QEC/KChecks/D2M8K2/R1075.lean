import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4300 = true := by
  decide +kernel

theorem tot4300 : totK PD2M8K2 D2M8K2.t4300 = [0, 0, 0, 188985698045, 393418433755, 256503824243, 53221389490, 1271866555] := by
  decide +kernel

theorem rows4301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4301 = true := by
  decide +kernel

theorem tot4301 : totK PD2M8K2 D2M8K2.t4301 = [0, 0, 0, 215191620711, 482090250517, 200120150172, 6753105075, 0] := by
  decide +kernel

theorem rows4302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4302 = true := by
  decide +kernel

theorem tot4302 : totK PD2M8K2 D2M8K2.t4302 = [0, 0, 174479919827, 339830360531, 225948163949, 125679088739, 10061564396, 0] := by
  decide +kernel

theorem rows4303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4303 = true := by
  decide +kernel

theorem tot4303 : totK PD2M8K2 D2M8K2.t4303 = [0, 0, 144573248409, 452961260512, 272960968939, 16347538990, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

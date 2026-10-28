import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4092 = true := by
  decide +kernel

theorem tot4092 : totK PD2M8K2 D2M8K2.t4092 = [0, 186120298181, 436846674378, 210447949362, 56007824695, 9433566158, 0, 0] := by
  decide +kernel

theorem rows4093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4093 = true := by
  decide +kernel

theorem tot4093 : totK PD2M8K2 D2M8K2.t4093 = [0, 136885508158, 440517293605, 293012678362, 23399979168, 0, 0, 0] := by
  decide +kernel

theorem rows4094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4094 = true := by
  decide +kernel

theorem tot4094 : totK PD2M8K2 D2M8K2.t4094 = [0, 59184742890, 357920770384, 446168776563, 54737195700, 0, 0, 0] := by
  decide +kernel

theorem rows4095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4095 = true := by
  decide +kernel

theorem tot4095 : totK PD2M8K2 D2M8K2.t4095 = [0, 181869452667, 451234879084, 267027317836, 29073430889, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

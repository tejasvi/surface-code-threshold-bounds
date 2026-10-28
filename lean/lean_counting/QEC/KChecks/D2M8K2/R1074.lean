import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4296 = true := by
  decide +kernel

theorem tot4296 : totK PD2M8K2 D2M8K2.t4296 = [0, 0, 0, 48362297334, 237135676712, 415844620686, 137141026536, 5352782441] := by
  decide +kernel

theorem rows4297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4297 = true := by
  decide +kernel

theorem tot4297 : totK PD2M8K2 D2M8K2.t4297 = [0, 0, 0, 175050550895, 499001309855, 218804348430, 9790196716, 0] := by
  decide +kernel

theorem rows4298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4298 = true := by
  decide +kernel

theorem tot4298 : totK PD2M8K2 D2M8K2.t4298 = [0, 0, 0, 178017608236, 478987383457, 222135119776, 9554626757, 0] := by
  decide +kernel

theorem rows4299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4299 = true := by
  decide +kernel

theorem tot4299 : totK PD2M8K2 D2M8K2.t4299 = [0, 0, 0, 0, 352901257347, 466660323843, 49135624837, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

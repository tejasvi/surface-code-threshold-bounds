import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4864 = true := by
  decide +kernel

theorem tot4864 : totK PD2M8K2 D2M8K2.t4864 = [0, 0, 176374678362, 472455669169, 248018844494, 12142509965, 0, 0] := by
  decide +kernel

theorem rows4865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4865 = true := by
  decide +kernel

theorem tot4865 : totK PD2M8K2 D2M8K2.t4865 = [0, 0, 0, 270492896257, 513099812795, 119648816264, 1198073392, 0] := by
  decide +kernel

theorem rows4866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4866 = true := by
  decide +kernel

theorem tot4866 : totK PD2M8K2 D2M8K2.t4866 = [0, 0, 30599545247, 209307141459, 434596836137, 188770521891, 12052611869, 0] := by
  decide +kernel

theorem rows4867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4867 = true := by
  decide +kernel

theorem tot4867 : totK PD2M8K2 D2M8K2.t4867 = [0, 0, 179018123410, 449228843396, 238410898475, 22743397594, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

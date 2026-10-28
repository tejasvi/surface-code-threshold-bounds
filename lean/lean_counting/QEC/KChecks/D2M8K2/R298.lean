import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1192 = true := by
  decide +kernel

theorem tot1192 : totK PD2M8K2 D2M8K2.t1192 = [76175827862, 357216524021, 384087954517, 71285541179, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows1193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1193 = true := by
  decide +kernel

theorem tot1193 : totK PD2M8K2 D2M8K2.t1193 = [72608393446, 300560101241, 405241846893, 112531684998, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows1194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1194 = true := by
  decide +kernel

theorem tot1194 : totK PD2M8K2 D2M8K2.t1194 = [171820657288, 460180315146, 255008273747, 22181025704, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1195 = true := by
  decide +kernel

theorem tot1195 : totK PD2M8K2 D2M8K2.t1195 = [179867083042, 466584787535, 246158889993, 17092887201, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

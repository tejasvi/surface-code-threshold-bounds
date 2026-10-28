import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1044 = true := by
  decide +kernel

theorem tot1044 : totK PD2M8K2 D2M8K2.t1044 = [183576233279, 463992578824, 253255214265, 22490689519, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1045 = true := by
  decide +kernel

theorem tot1045 : totK PD2M8K2 D2M8K2.t1045 = [183118638751, 466853849730, 239918407144, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1046 = true := by
  decide +kernel

theorem tot1046 : totK PD2M8K2 D2M8K2.t1046 = [19228354030, 328883229052, 463884994010, 84289764754, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows1047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1047 = true := by
  decide +kernel

theorem tot1047 : totK PD2M8K2 D2M8K2.t1047 = [0, 266800611364, 511840673943, 128635573737, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

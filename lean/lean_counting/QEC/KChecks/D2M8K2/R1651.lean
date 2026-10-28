import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6604 = true := by
  decide +kernel

theorem tot6604 : totK PD2M8K2 D2M8K2.t6604 = [0, 177439509053, 472778094891, 243237454440, 15843944531, 0, 0, 0] := by
  decide +kernel

theorem rows6605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6605 = true := by
  decide +kernel

theorem tot6605 : totK PD2M8K2 D2M8K2.t6605 = [0, 197069645355, 463251000115, 210966213965, 10178930409, 0, 0, 0] := by
  decide +kernel

theorem rows6606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6606 = true := by
  decide +kernel

theorem tot6606 : totK PD2M8K2 D2M8K2.t6606 = [0, 190534969844, 476019624263, 226591853164, 15844255384, 0, 0, 0] := by
  decide +kernel

theorem rows6607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6607 = true := by
  decide +kernel

theorem tot6607 : totK PD2M8K2 D2M8K2.t6607 = [0, 190410964158, 455719127898, 224364753637, 16702988424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

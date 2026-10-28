import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12308 = true := by
  decide +kernel

theorem tot12308 : totK PD2M8K2 D2M8K2.t12308 = [0, 0, 312298948196, 472301377889, 80892016523, 1053411165, 0, 0] := by
  decide +kernel

theorem rows12309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12309 = true := by
  decide +kernel

theorem tot12309 : totK PD2M8K2 D2M8K2.t12309 = [0, 163963065441, 381533521417, 253144660869, 73426852562, 3667207281, 0, 0] := by
  decide +kernel

theorem rows12310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12310 = true := by
  decide +kernel

theorem tot12310 : totK PD2M8K2 D2M8K2.t12310 = [0, 161012605395, 447423059271, 278512725094, 20790636752, 0, 0, 0] := by
  decide +kernel

theorem rows12311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12311 = true := by
  decide +kernel

theorem tot12311 : totK PD2M8K2 D2M8K2.t12311 = [182717929658, 451465099572, 215740672412, 36884820693, 7008164077, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11328 = true := by
  decide +kernel

theorem tot11328 : totK PD2M8K2 D2M8K2.t11328 = [174650386013, 441299702014, 267324186410, 26848536076, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11329 = true := by
  decide +kernel

theorem tot11329 : totK PD2M8K2 D2M8K2.t11329 = [162037142227, 474383147482, 261020155078, 14870912610, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11330 = true := by
  decide +kernel

theorem tot11330 : totK PD2M8K2 D2M8K2.t11330 = [0, 198569688621, 465093939404, 224910040285, 21396654552, 0, 0, 0] := by
  decide +kernel

theorem rows11331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11331 = true := by
  decide +kernel

theorem tot11331 : totK PD2M8K2 D2M8K2.t11331 = [0, 180002060351, 482136512803, 228154227356, 9404016956, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

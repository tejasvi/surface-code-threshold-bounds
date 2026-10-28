import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11104 = true := by
  decide +kernel

theorem tot11104 : totK PD2M8K2 D2M8K2.t11104 = [0, 117097336354, 408199330728, 313652016494, 49794316442, 1689881148, 0, 0] := by
  decide +kernel

theorem rows11105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11105 = true := by
  decide +kernel

theorem tot11105 : totK PD2M8K2 D2M8K2.t11105 = [0, 180895429210, 443984944045, 249908264382, 24826081626, 0, 0, 0] := by
  decide +kernel

theorem rows11106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11106 = true := by
  decide +kernel

theorem tot11106 : totK PD2M8K2 D2M8K2.t11106 = [0, 125224413203, 442601438879, 310685198918, 25320969689, 0, 0, 0] := by
  decide +kernel

theorem rows11107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11107 = true := by
  decide +kernel

theorem tot11107 : totK PD2M8K2 D2M8K2.t11107 = [0, 0, 216862716582, 484524670693, 157021572799, 4811815119, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

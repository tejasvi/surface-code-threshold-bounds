import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9688 = true := by
  decide +kernel

theorem tot9688 : totK PD2M8K2 D2M8K2.t9688 = [0, 0, 52305571454, 345707609370, 394057558193, 67886162414, 1128585284, 0] := by
  decide +kernel

theorem rows9689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9689 = true := by
  decide +kernel

theorem tot9689 : totK PD2M8K2 D2M8K2.t9689 = [0, 0, 52600150510, 295206574121, 407820646539, 105182931504, 4006170569, 0] := by
  decide +kernel

theorem rows9690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9690 = true := by
  decide +kernel

theorem tot9690 : totK PD2M8K2 D2M8K2.t9690 = [0, 0, 204912456639, 476835975706, 203978505917, 11448224421, 0, 0] := by
  decide +kernel

theorem rows9691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9691 = true := by
  decide +kernel

theorem tot9691 : totK PD2M8K2 D2M8K2.t9691 = [0, 0, 163627164274, 480689350606, 237863330450, 10612771741, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

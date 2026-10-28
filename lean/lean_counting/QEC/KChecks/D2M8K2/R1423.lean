import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5692 = true := by
  decide +kernel

theorem tot5692 : totK PD2M8K2 D2M8K2.t5692 = [0, 0, 212176846599, 472354961948, 163299569318, 7362961718, 0, 0] := by
  decide +kernel

theorem rows5693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5693 = true := by
  decide +kernel

theorem tot5693 : totK PD2M8K2 D2M8K2.t5693 = [0, 0, 192640695389, 473515883122, 207562268590, 14510083306, 0, 0] := by
  decide +kernel

theorem rows5694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5694 = true := by
  decide +kernel

theorem tot5694 : totK PD2M8K2 D2M8K2.t5694 = [0, 0, 173978836422, 457654312104, 218519175706, 16632994142, 0, 0] := by
  decide +kernel

theorem rows5695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5695 = true := by
  decide +kernel

theorem tot5695 : totK PD2M8K2 D2M8K2.t5695 = [0, 0, 86408083722, 374871300104, 337253477903, 63983811803, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

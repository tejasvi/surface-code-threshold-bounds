import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4748 = true := by
  decide +kernel

theorem tot4748 : totK PD2M8K2 D2M8K2.t4748 = [0, 0, 194940006831, 477602011598, 211899261421, 11071105621, 0, 0] := by
  decide +kernel

theorem rows4749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4749 = true := by
  decide +kernel

theorem tot4749 : totK PD2M8K2 D2M8K2.t4749 = [0, 0, 186788734933, 469213055122, 221337500564, 13176583453, 0, 0] := by
  decide +kernel

theorem rows4750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4750 = true := by
  decide +kernel

theorem tot4750 : totK PD2M8K2 D2M8K2.t4750 = [0, 0, 0, 331468281891, 447674602727, 65155853662, 1053411165, 0] := by
  decide +kernel

theorem rows4751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4751 = true := by
  decide +kernel

theorem tot4751 : totK PD2M8K2 D2M8K2.t4751 = [0, 0, 82821601848, 320323895344, 356643306483, 91828416184, 3667207281, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

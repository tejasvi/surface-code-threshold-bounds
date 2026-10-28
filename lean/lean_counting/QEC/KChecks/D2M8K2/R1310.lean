import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5240 = true := by
  decide +kernel

theorem tot5240 : totK PD2M8K2 D2M8K2.t5240 = [0, 171012859452, 451713042675, 269252529590, 20012605371, 0, 0, 0] := by
  decide +kernel

theorem rows5241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5241 = true := by
  decide +kernel

theorem tot5241 : totK PD2M8K2 D2M8K2.t5241 = [0, 87890102425, 356483096870, 374465517894, 77859919244, 1163840124, 0, 0] := by
  decide +kernel

theorem rows5242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5242 = true := by
  decide +kernel

theorem tot5242 : totK PD2M8K2 D2M8K2.t5242 = [0, 0, 239449157262, 491833356102, 157715791011, 8197355695, 0, 0] := by
  decide +kernel

theorem rows5243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5243 = true := by
  decide +kernel

theorem tot5243 : totK PD2M8K2 D2M8K2.t5243 = [0, 156352226729, 416900445163, 278950970076, 56788069105, 2251425328, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

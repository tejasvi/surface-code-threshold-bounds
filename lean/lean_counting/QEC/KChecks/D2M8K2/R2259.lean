import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9036 = true := by
  decide +kernel

theorem tot9036 : totK PD2M8K2 D2M8K2.t9036 = [0, 0, 18616785608, 336993062831, 425947613797, 57516816093, 0, 0] := by
  decide +kernel

theorem rows9037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9037 = true := by
  decide +kernel

theorem tot9037 : totK PD2M8K2 D2M8K2.t9037 = [0, 0, 217442909145, 491885742260, 148111074204, 2519764721, 0, 0] := by
  decide +kernel

theorem rows9038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9038 = true := by
  decide +kernel

theorem tot9038 : totK PD2M8K2 D2M8K2.t9038 = [0, 0, 223485912431, 490501915866, 161772670421, 2447226230, 0, 0] := by
  decide +kernel

theorem rows9039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9039 = true := by
  decide +kernel

theorem tot9039 : totK PD2M8K2 D2M8K2.t9039 = [0, 0, 194307483935, 465533782662, 214031139497, 12652156324, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

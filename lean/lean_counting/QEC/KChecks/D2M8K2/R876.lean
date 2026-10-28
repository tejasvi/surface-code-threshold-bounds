import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3504 = true := by
  decide +kernel

theorem tot3504 : totK PD2M8K2 D2M8K2.t3504 = [0, 174171802489, 460754933001, 262986318735, 21956222201, 0, 0, 0] := by
  decide +kernel

theorem rows3505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3505 = true := by
  decide +kernel

theorem tot3505 : totK PD2M8K2 D2M8K2.t3505 = [87379608540, 275096929315, 338396084244, 183249934649, 18296482768, 0, 0, 0] := by
  decide +kernel

theorem rows3506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3506 = true := by
  decide +kernel

theorem tot3506 : totK PD2M8K2 D2M8K2.t3506 = [187448321194, 453439387351, 226763467651, 17111997474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3507 = true := by
  decide +kernel

theorem tot3507 : totK PD2M8K2 D2M8K2.t3507 = [102435238113, 407456109636, 336685909947, 41274647047, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

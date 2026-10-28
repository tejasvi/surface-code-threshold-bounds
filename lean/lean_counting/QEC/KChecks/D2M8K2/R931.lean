import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3724 = true := by
  decide +kernel

theorem tot3724 : totK PD2M8K2 D2M8K2.t3724 = [167248517720, 465363147125, 258107172523, 18527604408, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3725 = true := by
  decide +kernel

theorem tot3725 : totK PD2M8K2 D2M8K2.t3725 = [0, 229347850736, 497140976410, 162663008780, 7162567726, 0, 0, 0] := by
  decide +kernel

theorem rows3726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3726 = true := by
  decide +kernel

theorem tot3726 : totK PD2M8K2 D2M8K2.t3726 = [66166673759, 300129111893, 395658962291, 114695442764, 5737564422, 0, 0, 0] := by
  decide +kernel

theorem rows3727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3727 = true := by
  decide +kernel

theorem tot3727 : totK PD2M8K2 D2M8K2.t3727 = [181906074839, 467991426379, 261218911610, 23190023676, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

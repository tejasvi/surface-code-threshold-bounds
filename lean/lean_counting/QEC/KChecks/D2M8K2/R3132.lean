import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12528 = true := by
  decide +kernel

theorem tot12528 : totK PD2M8K2 D2M8K2.t12528 = [0, 0, 164100838655, 465422272227, 246959133303, 19019349331, 0, 0] := by
  decide +kernel

theorem rows12529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12529 = true := by
  decide +kernel

theorem tot12529 : totK PD2M8K2 D2M8K2.t12529 = [0, 0, 191352642578, 462191591049, 224578898652, 13468795916, 0, 0] := by
  decide +kernel

theorem rows12530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12530 = true := by
  decide +kernel

theorem tot12530 : totK PD2M8K2 D2M8K2.t12530 = [0, 0, 54617937868, 355453046736, 381300835997, 59409648346, 1021600638, 0] := by
  decide +kernel

theorem rows12531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12531 = true := by
  decide +kernel

theorem tot12531 : totK PD2M8K2 D2M8K2.t12531 = [0, 0, 59040401375, 303220594539, 389428113170, 93166853631, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

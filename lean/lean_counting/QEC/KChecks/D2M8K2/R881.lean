import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3524 = true := by
  decide +kernel

theorem tot3524 : totK PD2M8K2 D2M8K2.t3524 = [0, 261923835220, 503618605032, 144967997453, 3742744013, 0, 0, 0] := by
  decide +kernel

theorem rows3525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3525 = true := by
  decide +kernel

theorem tot3525 : totK PD2M8K2 D2M8K2.t3525 = [0, 152695064511, 454301908614, 237410107756, 15742723725, 0, 0, 0] := by
  decide +kernel

theorem rows3526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3526 = true := by
  decide +kernel

theorem tot3526 : totK PD2M8K2 D2M8K2.t3526 = [0, 186236970254, 473706881073, 214806312685, 12361325328, 0, 0, 0] := by
  decide +kernel

theorem rows3527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3527 = true := by
  decide +kernel

theorem tot3527 : totK PD2M8K2 D2M8K2.t3527 = [0, 36620594963, 309358726127, 437175150742, 76609833612, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

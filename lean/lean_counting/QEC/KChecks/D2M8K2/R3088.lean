import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12352 = true := by
  decide +kernel

theorem tot12352 : totK PD2M8K2 D2M8K2.t12352 = [0, 0, 266972045361, 501498120659, 115214130905, 2309606161, 0, 0] := by
  decide +kernel

theorem rows12353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12353 = true := by
  decide +kernel

theorem tot12353 : totK PD2M8K2 D2M8K2.t12353 = [0, 58286174097, 243609706427, 403554810265, 148064876723, 10673843635, 0, 0] := by
  decide +kernel

theorem rows12354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12354 = true := by
  decide +kernel

theorem tot12354 : totK PD2M8K2 D2M8K2.t12354 = [0, 185482000289, 477050160662, 235244677214, 13613005002, 0, 0, 0] := by
  decide +kernel

theorem rows12355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12355 = true := by
  decide +kernel

theorem tot12355 : totK PD2M8K2 D2M8K2.t12355 = [0, 162465993231, 466583636588, 243936238264, 12597559134, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

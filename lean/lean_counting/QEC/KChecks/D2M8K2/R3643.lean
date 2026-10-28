import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14572 = true := by
  decide +kernel

theorem tot14572 : totK PD2M8K2 D2M8K2.t14572 = [173303433249, 451960520802, 260638296570, 34003674790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14573 = true := by
  decide +kernel

theorem tot14573 : totK PD2M8K2 D2M8K2.t14573 = [163420478254, 456265194706, 265314122374, 18419824630, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14574 = true := by
  decide +kernel

theorem tot14574 : totK PD2M8K2 D2M8K2.t14574 = [89753051296, 343161126912, 387786711591, 82405366446, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14575 = true := by
  decide +kernel

theorem tot14575 : totK PD2M8K2 D2M8K2.t14575 = [0, 230349371794, 480952701925, 167832846100, 9478200669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

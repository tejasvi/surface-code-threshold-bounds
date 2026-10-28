import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14564 = true := by
  decide +kernel

theorem tot14564 : totK PD2M8K2 D2M8K2.t14564 = [155468204927, 419990111266, 324963593795, 40765723854, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14565 = true := by
  decide +kernel

theorem tot14565 : totK PD2M8K2 D2M8K2.t14565 = [174263722444, 474285711075, 245618684465, 15281451407, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14566 = true := by
  decide +kernel

theorem tot14566 : totK PD2M8K2 D2M8K2.t14566 = [89930864070, 358661378178, 359684411005, 97823927581, 13120661245, 0, 0, 0] := by
  decide +kernel

theorem rows14567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14567 = true := by
  decide +kernel

theorem tot14567 : totK PD2M8K2 D2M8K2.t14567 = [0, 168149053444, 461081603054, 253474032481, 14928019357, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

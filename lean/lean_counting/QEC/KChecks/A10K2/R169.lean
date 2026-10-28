import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t676 = true := by
  decide +kernel

theorem tot676 : totK PA10K2 A10K2.t676 = [0, 364430561365, 1666283375385, 2068798100626, 612727984065, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t677 = true := by
  decide +kernel

theorem tot677 : totK PA10K2 A10K2.t677 = [0, 0, 677629497621, 2152294274553, 1617447109891, 238742265886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t678 = true := by
  decide +kernel

theorem tot678 : totK PA10K2 A10K2.t678 = [0, 268061909688, 1251568326428, 1977298187624, 1168559395676, 234873721743, 13317224979, 0, 0, 0] := by
  decide +kernel

theorem rows679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t679 = true := by
  decide +kernel

theorem tot679 : totK PA10K2 A10K2.t679 = [0, 0, 571824530637, 1922693105690, 1764156693998, 446234379866, 26479096260, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

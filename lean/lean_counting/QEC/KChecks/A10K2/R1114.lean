import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4456 = true := by
  decide +kernel

theorem tot4456 : totK PA10K2 A10K2.t4456 = [441839207433, 1534973493331, 1814548292951, 902647264397, 179656650673, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4457 = true := by
  decide +kernel

theorem tot4457 : totK PA10K2 A10K2.t4457 = [301571695590, 1433981420777, 2152985671058, 926229258730, 76488752013, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4458 = true := by
  decide +kernel

theorem tot4458 : totK PA10K2 A10K2.t4458 = [0, 601009014031, 2067936213455, 1912946045449, 381963699134, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4459 = true := by
  decide +kernel

theorem tot4459 : totK PA10K2 A10K2.t4459 = [0, 320437926777, 1511403202050, 2120397946586, 841899501773, 74841839271, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6280 = true := by
  decide +kernel

theorem tot6280 : totK PA10K2 A10K2.t6280 = [0, 225308319829, 1207617973128, 2120211115967, 1196014866007, 208221820063, 15171143123, 0, 0, 0] := by
  decide +kernel

theorem rows6281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6281 = true := by
  decide +kernel

theorem tot6281 : totK PA10K2 A10K2.t6281 = [0, 79946846261, 703461737055, 1848936150896, 1587058172652, 351391865765, 15911743486, 0, 0, 0] := by
  decide +kernel

theorem rows6282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6282 = true := by
  decide +kernel

theorem tot6282 : totK PA10K2 A10K2.t6282 = [0, 507471979970, 1773459210956, 1820040356085, 521988079307, 31936107789, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6283 = true := by
  decide +kernel

theorem tot6283 : totK PA10K2 A10K2.t6283 = [0, 95577804451, 1137274377921, 2189485004806, 989514969808, 77355190755, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

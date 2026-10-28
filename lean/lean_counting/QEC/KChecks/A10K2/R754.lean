import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3016 = true := by
  decide +kernel

theorem tot3016 : totK PA10K2 A10K2.t3016 = [0, 0, 0, 699133857427, 2068446489193, 1810601413131, 388332368861, 18292998707, 0, 0] := by
  decide +kernel

theorem rows3017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3017 = true := by
  decide +kernel

theorem tot3017 : totK PA10K2 A10K2.t3017 = [0, 0, 303693864090, 1204134680413, 1786210252966, 1251614700725, 369219893259, 29010686974, 0, 0] := by
  decide +kernel

theorem rows3018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3018 = true := by
  decide +kernel

theorem tot3018 : totK PA10K2 A10K2.t3018 = [0, 0, 480247428435, 1769153493008, 1968373110558, 715135658897, 56423586159, 0, 0, 0] := by
  decide +kernel

theorem rows3019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3019 = true := by
  decide +kernel

theorem tot3019 : totK PA10K2 A10K2.t3019 = [0, 0, 0, 709169539935, 2136421931163, 1627656714754, 332472664282, 12473006693, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

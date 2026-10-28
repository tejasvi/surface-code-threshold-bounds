import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6340 = true := by
  decide +kernel

theorem tot6340 : totK PA10K2 A10K2.t6340 = [0, 200194408439, 1036300583445, 2056355701991, 1507675587623, 288366383751, 7007974415, 0, 0, 0] := by
  decide +kernel

theorem rows6341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6341 = true := by
  decide +kernel

theorem tot6341 : totK PA10K2 A10K2.t6341 = [0, 491518892522, 1860103106726, 1981370155059, 546755215806, 31908368213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6342 = true := by
  decide +kernel

theorem tot6342 : totK PA10K2 A10K2.t6342 = [0, 118398086739, 961132561118, 2083446233406, 1488650870043, 312402175345, 20328650499, 0, 0, 0] := by
  decide +kernel

theorem rows6343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6343 = true := by
  decide +kernel

theorem tot6343 : totK PA10K2 A10K2.t6343 = [0, 232865494112, 1053082940094, 1912494626673, 1425623864067, 292952597665, 10956717587, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

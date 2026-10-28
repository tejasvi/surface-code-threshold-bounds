import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6944 = true := by
  decide +kernel

theorem tot6944 : totK PA10K2 A10K2.t6944 = [0, 493539445507, 1908788527574, 2056346242214, 585151480971, 38113691692, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6945 = true := by
  decide +kernel

theorem tot6945 : totK PA10K2 A10K2.t6945 = [0, 119627100822, 1026682124856, 2204684884121, 1484198604867, 262129164220, 6574379264, 0, 0, 0] := by
  decide +kernel

theorem rows6946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6946 = true := by
  decide +kernel

theorem tot6946 : totK PA10K2 A10K2.t6946 = [0, 0, 438444911217, 1861350021101, 2134055337624, 580626007408, 18784622171, 0, 0, 0] := by
  decide +kernel

theorem rows6947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6947 = true := by
  decide +kernel

theorem tot6947 : totK PA10K2 A10K2.t6947 = [0, 0, 555899558909, 1811561340846, 1714218188247, 579363676733, 63765033835, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

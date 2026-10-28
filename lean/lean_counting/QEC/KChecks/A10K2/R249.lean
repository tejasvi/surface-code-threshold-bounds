import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t996 = true := by
  decide +kernel

theorem tot996 : totK PA10K2 A10K2.t996 = [0, 0, 189846836622, 1355440375554, 2250712740388, 835403737508, 53224042692, 0, 0, 0] := by
  decide +kernel

theorem rows997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t997 = true := by
  decide +kernel

theorem tot997 : totK PA10K2 A10K2.t997 = [0, 0, 307133734239, 1198357439910, 1840182091138, 1107865980449, 180844039151, 6354482628, 0, 0] := by
  decide +kernel

theorem rows998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t998 = true := by
  decide +kernel

theorem tot998 : totK PA10K2 A10K2.t998 = [0, 0, 494216004638, 1908073786609, 2032086345228, 544817156114, 18717824870, 0, 0, 0] := by
  decide +kernel

theorem rows999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t999 = true := by
  decide +kernel

theorem tot999 : totK PA10K2 A10K2.t999 = [0, 0, 0, 681297824967, 2076218406836, 1723510562687, 364010602211, 12473006693, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3880 = true := by
  decide +kernel

theorem tot3880 : totK PA10K2 A10K2.t3880 = [0, 0, 316607767631, 1524074648582, 2130013833115, 837880950661, 74778429178, 0, 0, 0] := by
  decide +kernel

theorem rows3881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3881 = true := by
  decide +kernel

theorem tot3881 : totK PA10K2 A10K2.t3881 = [0, 0, 526397487994, 1937725232202, 1932907021740, 445984040287, 12350643961, 0, 0, 0] := by
  decide +kernel

theorem rows3882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3882 = true := by
  decide +kernel

theorem tot3882 : totK PA10K2 A10K2.t3882 = [0, 0, 0, 540194733021, 1958587271692, 1735747063841, 412968921557, 25239774317, 0, 0] := by
  decide +kernel

theorem rows3883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3883 = true := by
  decide +kernel

theorem tot3883 : totK PA10K2 A10K2.t3883 = [0, 0, 392076695813, 1487760984926, 1883918900921, 898705445260, 150685979414, 5410721913, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

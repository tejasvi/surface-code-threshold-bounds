import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4400 = true := by
  decide +kernel

theorem tot4400 : totK PA10K2 A10K2.t4400 = [0, 0, 478170626599, 1847070189157, 1895907428813, 464799166802, 16735867423, 0, 0, 0] := by
  decide +kernel

theorem rows4401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4401 = true := by
  decide +kernel

theorem tot4401 : totK PA10K2 A10K2.t4401 = [0, 0, 0, 802539592824, 2371716500405, 1366223611330, 116677093814, 0, 0, 0] := by
  decide +kernel

theorem rows4402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4402 = true := by
  decide +kernel

theorem tot4402 : totK PA10K2 A10K2.t4402 = [0, 0, 552312781151, 1819413218013, 1744898939374, 645671373312, 129852533821, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4403 = true := by
  decide +kernel

theorem tot4403 : totK PA10K2 A10K2.t4403 = [0, 0, 0, 751278003404, 2247569166838, 1641284706851, 274637635582, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

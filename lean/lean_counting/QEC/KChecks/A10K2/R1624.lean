import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6496 = true := by
  decide +kernel

theorem tot6496 : totK PA10K2 A10K2.t6496 = [0, 325843893375, 1621608499095, 2168148453981, 808897729692, 68664262343, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6497 = true := by
  decide +kernel

theorem tot6497 : totK PA10K2 A10K2.t6497 = [0, 0, 473012865185, 1821468380415, 1902092241705, 504543508877, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows6498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6498 = true := by
  decide +kernel

theorem tot6498 : totK PA10K2 A10K2.t6498 = [0, 452811472891, 1608702772244, 1868423752094, 849231114689, 101790845703, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6499 = true := by
  decide +kernel

theorem tot6499 : totK PA10K2 A10K2.t6499 = [0, 290643499251, 1478947060984, 2094428401213, 752512308315, 54138101550, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

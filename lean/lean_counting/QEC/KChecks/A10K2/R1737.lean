import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6948 = true := by
  decide +kernel

theorem tot6948 : totK PA10K2 A10K2.t6948 = [0, 0, 292243983067, 1483678855758, 2218798980646, 855068422262, 61866981726, 0, 0, 0] := by
  decide +kernel

theorem rows6949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6949 = true := by
  decide +kernel

theorem tot6949 : totK PA10K2 A10K2.t6949 = [0, 0, 0, 513157726565, 1759591943921, 1772754409703, 490180214558, 31082886609, 0, 0] := by
  decide +kernel

theorem rows6950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6950 = true := by
  decide +kernel

theorem tot6950 : totK PA10K2 A10K2.t6950 = [0, 0, 484950038360, 1688917095868, 1902916314344, 686924327314, 55879297308, 0, 0, 0] := by
  decide +kernel

theorem rows6951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6951 = true := by
  decide +kernel

theorem tot6951 : totK PA10K2 A10K2.t6951 = [0, 0, 99436742374, 1133388820269, 2246381557787, 1011379311211, 78379076963, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

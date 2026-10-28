import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4904 = true := by
  decide +kernel

theorem tot4904 : totK PA10K2 A10K2.t4904 = [0, 0, 520580624864, 1828299465958, 1756879533341, 479302778684, 31082886609, 0, 0, 0] := by
  decide +kernel

theorem rows4905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4905 = true := by
  decide +kernel

theorem tot4905 : totK PA10K2 A10K2.t4905 = [0, 528786827964, 1752757120907, 1839482145312, 603584809404, 55879297308, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4906 = true := by
  decide +kernel

theorem tot4906 : totK PA10K2 A10K2.t4906 = [0, 218725902029, 1408162430151, 2172254781104, 825232529632, 51626803747, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4907 = true := by
  decide +kernel

theorem tot4907 : totK PA10K2 A10K2.t4907 = [0, 366095104304, 1377650583339, 1846358357735, 1005281192944, 167715549196, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

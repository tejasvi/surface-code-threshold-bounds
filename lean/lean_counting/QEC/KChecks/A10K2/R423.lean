import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1692 = true := by
  decide +kernel

theorem tot1692 : totK PA10K2 A10K2.t1692 = [0, 0, 292758513155, 1414297396614, 2087577374129, 923898890061, 79397113484, 0, 0, 0] := by
  decide +kernel

theorem rows1693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1693 = true := by
  decide +kernel

theorem tot1693 : totK PA10K2 A10K2.t1693 = [0, 0, 452937161428, 1785869543641, 2010803165323, 541070918217, 18560348465, 0, 0, 0] := by
  decide +kernel

theorem rows1694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1694 = true := by
  decide +kernel

theorem tot1694 : totK PA10K2 A10K2.t1694 = [0, 0, 0, 573497559884, 2009953467344, 1650640174505, 343035173048, 24614390653, 0, 0] := by
  decide +kernel

theorem rows1695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1695 = true := by
  decide +kernel

theorem tot1695 : totK PA10K2 A10K2.t1695 = [0, 0, 396445561613, 1459595434013, 1787051235895, 850759089774, 137622810853, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

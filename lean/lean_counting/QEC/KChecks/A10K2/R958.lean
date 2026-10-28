import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3832 = true := by
  decide +kernel

theorem tot3832 : totK PA10K2 A10K2.t3832 = [0, 0, 0, 0, 768521712281, 2308790947698, 1349001121064, 135879255444, 0, 0] := by
  decide +kernel

theorem rows3833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3833 = true := by
  decide +kernel

theorem tot3833 : totK PA10K2 A10K2.t3833 = [0, 0, 42649034548, 570543934099, 1852041595761, 1914917491831, 618208594336, 110272847697, 6121173289, 0] := by
  decide +kernel

theorem rows3834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3834 = true := by
  decide +kernel

theorem tot3834 : totK PA10K2 A10K2.t3834 = [0, 0, 509674541421, 1883060544180, 1807748462697, 431521364698, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows3835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3835 = true := by
  decide +kernel

theorem tot3835 : totK PA10K2 A10K2.t3835 = [0, 0, 129948670344, 856531235218, 1849056333293, 1328328257486, 289452613994, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

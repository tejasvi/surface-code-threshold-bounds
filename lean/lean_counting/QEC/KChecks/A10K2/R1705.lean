import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6820 = true := by
  decide +kernel

theorem tot6820 : totK PA10K2 A10K2.t6820 = [0, 612761359905, 2019332485512, 1923070406287, 443219723131, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6821 = true := by
  decide +kernel

theorem tot6821 : totK PA10K2 A10K2.t6821 = [0, 296731035481, 1500148937585, 2140592323232, 839988537619, 74462335336, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6822 = true := by
  decide +kernel

theorem tot6822 : totK PA10K2 A10K2.t6822 = [0, 464281269216, 1773014432971, 1987372492780, 713734233977, 55258067394, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6823 = true := by
  decide +kernel

theorem tot6823 : totK PA10K2 A10K2.t6823 = [0, 0, 730322511639, 2224640655391, 1581687733090, 251752948704, 6904928264, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

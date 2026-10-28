import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4844 = true := by
  decide +kernel

theorem tot4844 : totK PA10K2 A10K2.t4844 = [441334865603, 1800822034620, 1938921460558, 494462168406, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4845 = true := by
  decide +kernel

theorem tot4845 : totK PA10K2 A10K2.t4845 = [0, 817042714036, 2306883925772, 1427224442639, 141112168323, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4846 = true := by
  decide +kernel

theorem tot4846 : totK PA10K2 A10K2.t4846 = [0, 539376908212, 1800430496031, 1885197242315, 530216231067, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4847 = true := by
  decide +kernel

theorem tot4847 : totK PA10K2 A10K2.t4847 = [0, 514229884907, 1966418784315, 1957916883628, 446556479962, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

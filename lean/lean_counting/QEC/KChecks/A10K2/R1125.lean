import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4500 = true := by
  decide +kernel

theorem tot4500 : totK PA10K2 A10K2.t4500 = [0, 0, 636432396286, 2159690411209, 1884702546792, 361604236009, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows4501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4501 = true := by
  decide +kernel

theorem tot4501 : totK PA10K2 A10K2.t4501 = [0, 0, 588630179823, 1952532367760, 1805787498949, 511490473878, 34099770725, 0, 0, 0] := by
  decide +kernel

theorem rows4502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4502 = true := by
  decide +kernel

theorem tot4502 : totK PA10K2 A10K2.t4502 = [0, 0, 542496059800, 1811885137104, 1826399777922, 516866042742, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows4503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4503 = true := by
  decide +kernel

theorem tot4503 : totK PA10K2 A10K2.t4503 = [0, 0, 0, 766242083225, 2072663097909, 1496674035445, 365309006729, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
